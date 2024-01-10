/*
 * Cppcheck - A tool for static C/C++ code analysis
 * Copyright (C) 2007-2023 Cppcheck team.
 *
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

#include "addoninfo.h"

#include "path.h"
#include "utils.h"

#include <fstream>
#include <string>
#include <vector>

#include "json.h"

static std::string getFullPath(const std::string &fileName, const std::string &exename) {
    if (Path::isFile(fileName))
        return fileName;

    const std::string exepath = Path::getPathFromFilename(exename);
    if (Path::isFile(exepath + fileName))
        return exepath + fileName;
    if (Path::isFile(exepath + "addons/" + fileName))
        return exepath + "addons/" + fileName;

#ifdef FILESDIR
    if (Path::isFile(FILESDIR + ("/" + fileName)))
        return FILESDIR + ("/" + fileName);
    if (Path::isFile(FILESDIR + ("/addons/" + fileName)))
        return FILESDIR + ("/addons/" + fileName);
#endif
    return "";
}

static std::string parseAddonInfo(AddonInfo& addoninfo, const picojson::value &json, const std::string &fileName, const std::string &exename) {

    try {
        const std::string& json_error = picojson::get_last_error();
        if (!json_error.empty())
            throw cppcheck::JsonError(json_error);
        if (!json.is<picojson::object>())
            throw cppcheck::JsonError("JSON is not an object.");

        // TODO: remove/complete default value handling for missing fields
        const picojson::object& obj = json.get<picojson::object>();

        for (const std::string& arg: cppcheck::readOptionalArray<std::string>(obj, "args")) {
            if (!addoninfo.args.empty())
                addoninfo.args += " ";
            addoninfo.args += arg;
        }

        addoninfo.ctu = cppcheck::readOptional<bool>(obj, "ctu");
        addoninfo.python = cppcheck::readOptional<std::string>(obj, "python");
        addoninfo.executable = cppcheck::readOptional<std::string>(obj, "executable");
        const std::string& script = cppcheck::readOptional<std::string>(obj, "script");
        // Either "executable" or "script" must be specified
        if (addoninfo.executable.empty() == script.empty())
            throw cppcheck::JsonError("Either 'executable' or 'script' must be specified.");
        if (!addoninfo.executable.empty())
            addoninfo.executable = getFullPath(addoninfo.executable, fileName);
        else {
            if (!endsWith(script, ".py"))
                throw cppcheck::JsonError("'script' must end with .py");
            return addoninfo.getAddonInfo(script, exename);
        }
    } catch (const cppcheck::JsonError& e) {
        return "Failed to parse " + fileName + ". " + e.what();
    }
    return "";
}

std::string AddonInfo::getAddonInfo(const std::string &fileName, const std::string &exename) {
    if (fileName[0] == '{') {
        picojson::value json;
        const std::string err = picojson::parse(json, fileName);
        (void)err; // TODO: report
        return parseAddonInfo(*this, json, fileName, exename);
    }
    if (fileName.find('.') == std::string::npos)
        return getAddonInfo(fileName + ".py", exename);

    if (endsWith(fileName, ".py")) {
        scriptFile = Path::fromNativeSeparators(getFullPath(fileName, exename));
        if (scriptFile.empty())
            return "Did not find addon " + fileName;

        std::string::size_type pos1 = scriptFile.rfind('/');
        if (pos1 == std::string::npos)
            pos1 = 0;
        else
            pos1++;
        std::string::size_type pos2 = scriptFile.rfind('.');
        if (pos2 < pos1)
            pos2 = std::string::npos;
        name = scriptFile.substr(pos1, pos2 - pos1);

        runScript = getFullPath("runaddon.py", exename);

        return "";
    }

    if (!endsWith(fileName, ".json"))
        return "Failed to open addon " + fileName;

    std::ifstream fin(fileName);
    if (!fin.is_open())
        return "Failed to open " + fileName;
    picojson::value json;
    fin >> json;
    return parseAddonInfo(*this, json, fileName, exename);
}
