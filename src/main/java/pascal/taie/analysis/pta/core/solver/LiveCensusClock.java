/*
 * Tai-e: A Static Analysis Framework for Java
 *
 * Copyright (C) 2022 Tian Tan <tiantan@nju.edu.cn>
 * Copyright (C) 2022 Yue Li <yueli@nju.edu.cn>
 *
 * This file is part of Tai-e.
 *
 * Tai-e is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3
 * of the License, or (at your option) any later version.
 *
 * Tai-e is distributed in the hope that it will be useful,but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
 * or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General
 * Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with Tai-e. If not, see <https://www.gnu.org/licenses/>.
 */

package pascal.taie.analysis.pta.core.solver;

import org.jspecify.annotations.Nullable;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.InvalidPathException;
import java.nio.file.Path;

/**
 * Decides when the solver takes a census during the solve: every
 * {@code census-interval} seconds after the end of the last census (or the
 * start of the solve), and whenever the trigger file named by the system
 * property {@value #TRIGGER_PROPERTY} exists. The trigger file is looked
 * for at most once per {@link #TRIGGER_CHECK_NANOS} and deleted when it is
 * found, so that each creation asks for one census; if it cannot be
 * deleted, the trigger is switched off after that census.
 */
final class LiveCensusClock {

    private static final Logger logger = LoggerFactory.getLogger(LiveCensusClock.class);

    static final String TRIGGER_PROPERTY = "taie.pta.census.trigger";

    static final long TRIGGER_CHECK_NANOS = 1_000_000_000L;

    private static final long NANOS_PER_SECOND = 1_000_000_000L;

    private final long intervalNanos;

    private @Nullable Path trigger;

    private long lastCensusNanos;

    private long lastTriggerCheckNanos;

    /**
     * @param intervalNanos the time between two censuses, 0 for none by
     *                      time
     * @param trigger       the trigger file, or null for none
     * @param startNanos    the start of the solve
     */
    LiveCensusClock(long intervalNanos, @Nullable Path trigger, long startNanos) {
        if (intervalNanos < 0) {
            throw new IllegalArgumentException(
                    "census interval must be >= 0, given: " + intervalNanos + " ns");
        }
        this.intervalNanos = intervalNanos;
        this.trigger = trigger;
        lastCensusNanos = startNanos;
        // the first look for the trigger is at the first check
        lastTriggerCheckNanos = startNanos - TRIGGER_CHECK_NANOS;
    }

    /**
     * @return the clock of the option {@code census-interval} (seconds, 0
     * is off) and of the system property {@value #TRIGGER_PROPERTY}
     */
    static LiveCensusClock of(int intervalSeconds, long startNanos) {
        if (intervalSeconds < 0) {
            throw new IllegalArgumentException(
                    "census-interval must be >= 0, given: " + intervalSeconds);
        }
        String file = System.getProperty(TRIGGER_PROPERTY);
        Path trigger = null;
        if (file != null && !file.isEmpty()) {
            try {
                trigger = Path.of(file);
            } catch (InvalidPathException e) {
                logger.warn("The census trigger {} is not a path, the trigger is off", file, e);
            }
        }
        return new LiveCensusClock(intervalSeconds * NANOS_PER_SECOND, trigger, startNanos);
    }

    /**
     * @return whether a census can ever be due.
     */
    boolean isOn() {
        return intervalNanos != 0 || trigger != null;
    }

    /**
     * @return why a census is due at {@code nowNanos} ("interval" or
     * "trigger"), or null if none is; finding the trigger file deletes it.
     */
    @Nullable String due(long nowNanos) {
        Path file = trigger;
        if (file != null && nowNanos - lastTriggerCheckNanos >= TRIGGER_CHECK_NANOS) {
            lastTriggerCheckNanos = nowNanos;
            try {
                if (Files.deleteIfExists(file)) {
                    return "trigger";
                }
            } catch (IOException e) {
                if (Files.exists(file)) {
                    logger.warn("Cannot delete the census trigger {}, the trigger is off"
                            + " after this census", file, e);
                    trigger = null;
                    return "trigger";
                }
            }
        }
        if (intervalNanos != 0 && nowNanos - lastCensusNanos >= intervalNanos) {
            return "interval";
        }
        return null;
    }

    /**
     * Records the end of a census, from which the next interval counts.
     */
    void taken(long endNanos) {
        lastCensusNanos = endNanos;
    }
}
