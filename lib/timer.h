/* -*- C++ -*-
 * Cppcheck - A tool for static C/C++ code analysis
 * Copyright (C) 2007-2025 Cppcheck team.
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
//---------------------------------------------------------------------------
#ifndef timerH
#define timerH
//---------------------------------------------------------------------------

#include "config.h"

#include <cstdint>
#include <ctime>
#include <functional>
#include <map>
#include <mutex>
#include <string>
#include <utility>

enum class SHOWTIME_MODES : std::uint8_t {
    SHOWTIME_NONE,
    SHOWTIME_FILE,
    SHOWTIME_FILE_TOTAL,
    SHOWTIME_SUMMARY,
    SHOWTIME_TOP5_SUMMARY,
    SHOWTIME_TOP5_FILE
};

class CPPCHECKLIB TimerResultsIntf {
public:
    virtual ~TimerResultsIntf() = default;

    virtual void addResults(const std::string& str, std::clock_t clocks) = 0;
};

struct TimerResultsData {
    std::clock_t mClocks{};
    long mNumberOfResults{};

    double seconds() const {
        const double ret = static_cast<double>(static_cast<unsigned long>(mClocks)) / static_cast<double>(CLOCKS_PER_SEC);
        return ret;
    }
};

class CPPCHECKLIB TimerResults : public TimerResultsIntf {
public:
    TimerResults() = default;

    void showResults(SHOWTIME_MODES mode) const;
    void addResults(const std::string& str, std::clock_t clocks) override;

    void reset();

private:
    std::map<std::string, TimerResultsData> mResults;
    mutable std::mutex mResultsSync;
};

class CPPCHECKLIB Timer {
public:
    Timer(std::string str, SHOWTIME_MODES showtimeMode, TimerResultsIntf* timerResults = nullptr);
    Timer(bool fileTotal, std::string filename);
    ~Timer();

    Timer(const Timer&) = delete;
    Timer& operator=(const Timer&) = delete;

    void stop();

    static void run(std::string str, SHOWTIME_MODES showtimeMode, TimerResultsIntf* timerResults, const std::function<void()>& f) {
        Timer t(std::move(str), showtimeMode, timerResults);
        f();
    }

private:
    const std::string mStr;
    TimerResultsIntf* mTimerResults{};
    std::clock_t mStart = std::clock();
    const SHOWTIME_MODES mShowTimeMode = SHOWTIME_MODES::SHOWTIME_FILE_TOTAL;
    bool mStopped{};
};
//---------------------------------------------------------------------------
#endif // timerH
