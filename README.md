# event
Event System Library

A lightweight, modern C++ event system library designed for efficient event handling and dispatching, suitable for games and real-time applications.
Overview
The event library provides a type-safe, high-performance event handling system built with modern C++ (C++17 and above). It includes two core components:

event::emitter: A flexible event emitter that supports dynamic registration and triggering of type-safe events.
event::dispatcher: An event dispatcher that supports both immediate and queued event processing.

The library is header-only, has no external dependencies (using only the C++ Standard Library), and is optimized for performance with minimal memory overhead.
Source: This library is based on the signal submodule of the EnTT library, with the specific code located at https://github.com/skypjack/entt/tree/master/src/entt/signal.