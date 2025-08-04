#pragma once

#include <memory>
#include <type_traits>
#include <utility>
#include <cstddef>
#include <functional>
#include <iterator>
#include <memory>
#include <tuple>
#include <type_traits>
#include <utility>
#include <string_view>


#if defined(__cpp_exceptions) && !defined(NOEXCEPTION)
#    define CONSTEXPR
#    define THROW throw
#    define TRY try
#    define CATCH catch(...)
#else
#    define CONSTEXPR constexpr // use only with throwing functions (waiting for C++20)
#    define THROW
#    define TRY if(true)
#    define CATCH if(false)
#endif

#if __has_include(<version>)
#    include <version>
#
#    if defined(__cpp_consteval)
#        define CONSTEVAL consteval
#    endif
#endif

#ifndef CONSTEVAL
#    define CONSTEVAL constexpr
#endif

#ifdef USE_ATOMIC
#    include <atomic>
#    define MAYBE_ATOMIC(Type) std::atomic<Type>
#else
#    define MAYBE_ATOMIC(Type) Type
#endif

#ifndef ID_TYPE
#    include <cstdint>
#    define ID_TYPE std::uint32_t
#else
#    include <cstdint> // provides coverage for types in the std namespace
#endif

#ifndef SPARSE_PAGE
#    define SPARSE_PAGE 4096
#endif

#ifndef PACKED_PAGE
#    define PACKED_PAGE 1024
#endif

#ifdef DISABLE_ASSERT
#    undef ASSERT
#    define ASSERT(condition, msg) (void(0))
#elif !defined ASSERT
#    include <cassert>
#    define ASSERT(condition, msg) assert(((condition) && (msg)))
#endif

#ifdef DISABLE_ASSERT
#    undef ASSERT_CONSTEXPR
#    define ASSERT_CONSTEXPR(condition, msg) (void(0))
#elif !defined ASSERT_CONSTEXPR
#    define ASSERT_CONSTEXPR(condition, msg) ASSERT(condition, msg)
#endif

#define FAIL(msg) ASSERT(false, msg);

#ifdef NO_ETO
#    define ETO_TYPE(Type) void
#else
#    define ETO_TYPE(Type) Type
#endif

#ifdef NO_MIXIN
#    define STORAGE(Mixin, ...) __VA_ARGS__
#else
#    define STORAGE(Mixin, ...) Mixin<__VA_ARGS__>
#endif

#ifdef STANDARD_CPP
#    define NONSTD false
#else
#    define NONSTD true
#    if defined __clang__ || defined __GNUC__
#        define PRETTY_FUNCTION __PRETTY_FUNCTION__
#        define PRETTY_FUNCTION_PREFIX '='
#        define PRETTY_FUNCTION_SUFFIX ']'
#    elif defined _MSC_VER
#        define PRETTY_FUNCTION __FUNCSIG__
#        define PRETTY_FUNCTION_PREFIX '<'
#        define PRETTY_FUNCTION_SUFFIX '>'
#    endif
#endif

// NOLINTEND(cppcoreguidelines-macro-usage)
#ifndef EXPORT
#    if defined _WIN32 || defined __CYGWIN__ || defined _MSC_VER
#        define EXPORT __declspec(dllexport)
#        define IMPORT __declspec(dllimport)
#        define HIDDEN
#    elif defined __GNUC__ && __GNUC__ >= 4
#        define EXPORT __attribute__((visibility("default")))
#        define IMPORT __attribute__((visibility("default")))
#        define HIDDEN __attribute__((visibility("hidden")))
#    else /* Unsupported compiler */
#        define EXPORT
#        define IMPORT
#        define HIDDEN
#    endif
#endif



namespace event {

template<typename>
class delegate;

template<typename = std::allocator<void>>
class basic_dispatcher;

template<typename, typename = std::allocator<void>>
class emitter;

class connection;

struct scoped_connection;

template<typename>
class sink;

template<typename Type, typename = std::allocator<void>>
class sigh;


/*! @brief Alias declaration for the most common use case. */
using dispatcher = basic_dispatcher<>;


// NOLINTNEXTLINE(cppcoreguidelines-avoid-c-arrays, modernize-avoid-c-arrays)
template<std::size_t Len = sizeof(double[2]), std::size_t = alignof(double[2])>
class basic_any;

/*! @brief Alias declaration for type identifiers. */
using id_type = ID_TYPE;

/*! @brief Alias declaration for the most common use case. */
using any = basic_any<>;

template<typename, typename>
class compressed_pair;

template<typename>
class basic_hashed_string;

/*! @brief Aliases for common character types. */
using hashed_string = basic_hashed_string<char>;

/*! @brief Aliases for common character types. */
using hashed_wstring = basic_hashed_string<wchar_t>;

// NOLINTNEXTLINE(bugprone-forward-declaration-namespace)
struct type_info;

/*! @brief Disambiguation tag for constructors and the like. */
template<auto>
struct connect_arg_t {
    /*! @brief Default constructor. */
    explicit connect_arg_t() = default;
};

/**
 * @brief Constant of type connect_arg_t used to disambiguate calls.
 * @tparam Candidate Element to connect (likely a free or member function).
 */
template<auto Candidate>
inline constexpr connect_arg_t<Candidate> connect_arg{};

/*! @brief Identity function object (waiting for C++20). */
struct identity {
    /*! @brief Indicates that this is a transparent function object. */
    using is_transparent = void;

    /**
     * @brief Returns its argument unchanged.
     * @tparam Type Type of the argument.
     * @param value The actual argument.
     * @return The submitted value as-is.
     */
    template<typename Type>
    [[nodiscard]] constexpr Type &&operator()(Type &&value) const noexcept {
        return std::forward<Type>(value);
    }
};

/**
 * @brief A class to use to push around lists of types, nothing more.
 * @tparam Type Types provided by the type list.
 */
template<typename... Type>
struct type_list {
    /*! @brief Type list type. */
    using type = type_list;
    /*! @brief Compile-time number of elements in the type list. */
    static constexpr auto size = sizeof...(Type);
};

/*! @brief Primary template isn't defined on purpose. */
template<std::size_t, typename>
struct type_list_element;

/**
 * @brief Provides compile-time indexed access to the types of a type list.
 * @tparam Index Index of the type to return.
 * @tparam First First type provided by the type list.
 * @tparam Other Other types provided by the type list.
 */
template<std::size_t Index, typename First, typename... Other>
struct type_list_element<Index, type_list<First, Other...>>
    : type_list_element<Index - 1u, type_list<Other...>> {};

/**
 * @brief Provides compile-time indexed access to the types of a type list.
 * @tparam First First type provided by the type list.
 * @tparam Other Other types provided by the type list.
 */
template<typename First, typename... Other>
struct type_list_element<0u, type_list<First, Other...>> {
    /*! @brief Searched type. */
    using type = First;
};

/**
 * @brief Helper type.
 * @tparam Index Index of the type to return.
 * @tparam List Type list to search into.
 */
template<std::size_t Index, typename List>
using type_list_element_t = typename type_list_element<Index, List>::type;


template<typename To, typename From>
struct constness_as {
    /*! @brief The type resulting from the transcription of the constness. */
    using type = std::remove_const_t<To>;
};

/*! @copydoc constness_as */
template<typename To, typename From>
struct constness_as<To, const From> {
    /*! @brief The type resulting from the transcription of the constness. */
    using type = const To;
};

/**
 * @brief Alias template to facilitate the transcription of the constness.
 * @tparam To The type to which to transcribe the constness.
 * @tparam From The type from which to transcribe the constness.
 */
template<typename To, typename From>
using constness_as_t = typename constness_as<To, From>::type;



/*! @cond TURN_OFF_DOXYGEN */
namespace internal {

template<typename Type>
struct uses_allocator_construction {
    template<typename Allocator, typename... Params>
    static constexpr auto args([[maybe_unused]] const Allocator &allocator, Params &&...params) noexcept {
        if constexpr(!std::uses_allocator_v<Type, Allocator> && std::is_constructible_v<Type, Params...>) {
            return std::forward_as_tuple(std::forward<Params>(params)...);
        } else {
            static_assert(std::uses_allocator_v<Type, Allocator>, "Ill-formed request");

            if constexpr(std::is_constructible_v<Type, std::allocator_arg_t, const Allocator &, Params...>) {
                return std::tuple<std::allocator_arg_t, const Allocator &, Params &&...>{std::allocator_arg, allocator, std::forward<Params>(params)...};
            } else {
                static_assert(std::is_constructible_v<Type, Params..., const Allocator &>, "Ill-formed request");
                return std::forward_as_tuple(std::forward<Params>(params)..., allocator);
            }
        }
    }
};

template<typename Type, typename Other>
struct uses_allocator_construction<std::pair<Type, Other>> {
    using type = std::pair<Type, Other>;

    template<typename Allocator, typename First, typename Second>
    static constexpr auto args(const Allocator &allocator, std::piecewise_construct_t, First &&first, Second &&second) noexcept {
        return std::make_tuple(
            std::piecewise_construct,
            std::apply([&allocator](auto &&...curr) { return uses_allocator_construction<Type>::args(allocator, std::forward<decltype(curr)>(curr)...); }, std::forward<First>(first)),
            std::apply([&allocator](auto &&...curr) { return uses_allocator_construction<Other>::args(allocator, std::forward<decltype(curr)>(curr)...); }, std::forward<Second>(second)));
    }

    template<typename Allocator>
    static constexpr auto args(const Allocator &allocator) noexcept {
        return uses_allocator_construction<type>::args(allocator, std::piecewise_construct, std::tuple<>{}, std::tuple<>{});
    }

    template<typename Allocator, typename First, typename Second>
    static constexpr auto args(const Allocator &allocator, First &&first, Second &&second) noexcept {
        return uses_allocator_construction<type>::args(allocator, std::piecewise_construct, std::forward_as_tuple(std::forward<First>(first)), std::forward_as_tuple(std::forward<Second>(second)));
    }

    template<typename Allocator, typename First, typename Second>
    static constexpr auto args(const Allocator &allocator, const std::pair<First, Second> &value) noexcept {
        return uses_allocator_construction<type>::args(allocator, std::piecewise_construct, std::forward_as_tuple(value.first), std::forward_as_tuple(value.second));
    }

    template<typename Allocator, typename First, typename Second>
    static constexpr auto args(const Allocator &allocator, std::pair<First, Second> &&value) noexcept {
        return uses_allocator_construction<type>::args(allocator, std::piecewise_construct, std::forward_as_tuple(std::move(value.first)), std::forward_as_tuple(std::move(value.second)));
    }
};

} // namespace internal
/*! @endcond */



/**
 * @brief Uses-allocator construction utility (waiting for C++20).
 *
 * Primarily intended for internal use. Creates an object of a given type by
 * means of uses-allocator construction.
 *
 * @tparam Type Type of object to create.
 * @tparam Allocator Type of allocator used to manage memory and elements.
 * @tparam Args Types of arguments to use to construct the object.
 * @param allocator The allocator to use.
 * @param args Parameters to use to construct the object.
 * @return A newly created object of the given type.
 */
template<typename Type, typename Allocator, typename... Args>
constexpr Type make_obj_using_allocator(const Allocator &allocator, Args &&...args) {
    return std::make_from_tuple<Type>(internal::uses_allocator_construction<Type>::args(allocator, std::forward<Args>(args)...));
}



/**
 * @brief Helper type to use as pointer with input iterators.
 * @tparam Type of wrapped value.
 */
template<typename Type>
struct input_iterator_pointer final {
    /*! @brief Value type. */
    using value_type = Type;
    /*! @brief Pointer type. */
    using pointer = Type *;
    /*! @brief Reference type. */
    using reference = Type &;

    /**
     * @brief Constructs a proxy object by move.
     * @param val Value to use to initialize the proxy object.
     */
    constexpr input_iterator_pointer(value_type &&val) noexcept(std::is_nothrow_move_constructible_v<value_type>)
        : value{std::move(val)} {}

    /**
     * @brief Access operator for accessing wrapped values.
     * @return A pointer to the wrapped value.
     */
    [[nodiscard]] constexpr pointer operator->() noexcept {
        return std::addressof(value);
    }

    /**
     * @brief Dereference operator for accessing wrapped values.
     * @return A reference to the wrapped value.
     */
    [[nodiscard]] constexpr reference operator*() noexcept {
        return value;
    }

private:
    Type value;
};



/**
 * @brief Provides the member constant `value` to true if a given type is both
 * an empty and non-final class, false otherwise.
 * @tparam Type The type to test
 */
template<typename Type>
struct is_ebco_eligible
    : std::bool_constant<std::is_empty_v<Type> && !std::is_final_v<Type>> {};

/**
 * @brief Helper variable template.
 * @tparam Type The type to test.
 */
template<typename Type>
inline constexpr bool is_ebco_eligible_v = is_ebco_eligible<Type>::value;


/**
 * @brief Provides the member constant `value` to true if `Type::is_transparent`
 * is valid and denotes a type, false otherwise.
 * @tparam Type The type to test.
 */
template<typename Type, typename = void>
struct is_transparent: std::false_type {};

/*! @copydoc is_transparent */
template<typename Type>
struct is_transparent<Type, std::void_t<typename Type::is_transparent>>: std::true_type {};

/**
 * @brief Helper variable template.
 * @tparam Type The type to test.
 */
template<typename Type>
inline constexpr bool is_transparent_v = is_transparent<Type>::value;


/*! @cond TURN_OFF_DOXYGEN */
namespace internal {

template<typename = id_type>
struct fnv_1a_params;

template<>
struct fnv_1a_params<std::uint32_t> {
    static constexpr auto offset = 2166136261;
    static constexpr auto prime = 16777619;
};

template<>
struct fnv_1a_params<std::uint64_t> {
    static constexpr auto offset = 14695981039346656037ull;
    static constexpr auto prime = 1099511628211ull;
};

template<typename Char>
struct basic_hashed_string {
    using value_type = Char;
    using size_type = std::size_t;
    using hash_type = id_type;

    const value_type *repr{};
    hash_type hash{fnv_1a_params<>::offset};
    size_type length{};
};

} // namespace internal
/*! @endcond */

/**
 * @brief Zero overhead unique identifier.
 *
 * A hashed string is a compile-time tool that allows users to use
 * human-readable identifiers in the codebase while using their numeric
 * counterparts at runtime.<br/>
 * Because of that, a hashed string can also be used in constant expressions if
 * required.
 *
 * @warning
 * This class doesn't take ownership of user-supplied strings nor does it make a
 * copy of them.
 *
 * @tparam Char Character type.
 */
template<typename Char>
class basic_hashed_string: internal::basic_hashed_string<Char> {
    using base_type = internal::basic_hashed_string<Char>;
    using params = internal::fnv_1a_params<>;

    struct const_wrapper {
        // non-explicit constructor on purpose
        constexpr const_wrapper(const typename base_type::value_type *str) noexcept
            : repr{str} {}

        const typename base_type::value_type *repr;
    };

public:
    /*! @brief Character type. */
    using value_type = typename base_type::value_type;
    /*! @brief Unsigned integer type. */
    using size_type = typename base_type::size_type;
    /*! @brief Unsigned integer type. */
    using hash_type = typename base_type::hash_type;

    /**
     * @brief Returns directly the numeric representation of a string view.
     * @param str Human-readable identifier.
     * @param len Length of the string to hash.
     * @return The numeric representation of the string.
     */
    [[nodiscard]] static constexpr hash_type value(const value_type *str, const size_type len) noexcept {
        return basic_hashed_string{str, len};
    }

    /**
     * @brief Returns directly the numeric representation of a string.
     * @tparam N Number of characters of the identifier.
     * @param str Human-readable identifier.
     * @return The numeric representation of the string.
     */
    template<std::size_t N>
    // NOLINTNEXTLINE(cppcoreguidelines-avoid-c-arrays, modernize-avoid-c-arrays)
    [[nodiscard]] static CONSTEVAL hash_type value(const value_type (&str)[N]) noexcept {
        return basic_hashed_string{str};
    }

    /**
     * @brief Returns directly the numeric representation of a string.
     * @param wrapper Helps achieving the purpose by relying on overloading.
     * @return The numeric representation of the string.
     */
    [[nodiscard]] static constexpr hash_type value(const_wrapper wrapper) noexcept {
        return basic_hashed_string{wrapper};
    }

    /*! @brief Constructs an empty hashed string. */
    constexpr basic_hashed_string() noexcept
        : basic_hashed_string{nullptr, 0u} {}

    /**
     * @brief Constructs a hashed string from a string view.
     * @param str Human-readable identifier.
     * @param len Length of the string to hash.
     */
    constexpr basic_hashed_string(const value_type *str, const size_type len) noexcept
        // NOLINTNEXTLINE(cppcoreguidelines-pro-bounds-array-to-pointer-decay)
        : base_type{str} {
        // NOLINTBEGIN(cppcoreguidelines-pro-bounds-pointer-arithmetic)
        for(; base_type::length < len; ++base_type::length) {
            base_type::hash = (base_type::hash ^ static_cast<id_type>(str[base_type::length])) * params::prime;
        }
        // NOLINTEND(cppcoreguidelines-pro-bounds-pointer-arithmetic)
    }

    /**
     * @brief Constructs a hashed string from an array of const characters.
     * @tparam N Number of characters of the identifier.
     * @param str Human-readable identifier.
     */
    template<std::size_t N>
    // NOLINTNEXTLINE(cppcoreguidelines-avoid-c-arrays, modernize-avoid-c-arrays)
    CONSTEVAL basic_hashed_string(const value_type (&str)[N]) noexcept
        // NOLINTNEXTLINE(cppcoreguidelines-pro-bounds-array-to-pointer-decay)
        : base_type{str} {
        for(; str[base_type::length]; ++base_type::length) {
            base_type::hash = (base_type::hash ^ static_cast<id_type>(str[base_type::length])) * params::prime;
        }
    }

    /**
     * @brief Explicit constructor on purpose to avoid constructing a hashed
     * string directly from a `const value_type *`.
     *
     * @warning
     * The lifetime of the string is not extended nor is it copied.
     *
     * @param wrapper Helps achieving the purpose by relying on overloading.
     */
    explicit constexpr basic_hashed_string(const_wrapper wrapper) noexcept
        : base_type{wrapper.repr} {
        // NOLINTBEGIN(cppcoreguidelines-pro-bounds-pointer-arithmetic)
        for(; wrapper.repr[base_type::length]; ++base_type::length) {
            base_type::hash = (base_type::hash ^ static_cast<id_type>(wrapper.repr[base_type::length])) * params::prime;
        }
        // NOLINTEND(cppcoreguidelines-pro-bounds-pointer-arithmetic)
    }

    /**
     * @brief Returns the size of a hashed string.
     * @return The size of the hashed string.
     */
    [[nodiscard]] constexpr size_type size() const noexcept {
        return base_type::length;
    }

    /**
     * @brief Returns the human-readable representation of a hashed string.
     * @return The string used to initialize the hashed string.
     */
    [[nodiscard]] constexpr const value_type *data() const noexcept {
        return base_type::repr;
    }

    /**
     * @brief Returns the numeric representation of a hashed string.
     * @return The numeric representation of the hashed string.
     */
    [[nodiscard]] constexpr hash_type value() const noexcept {
        return base_type::hash;
    }

    /*! @copydoc data */
    [[nodiscard]] explicit constexpr operator const value_type *() const noexcept {
        return data();
    }

    /**
     * @brief Returns the numeric representation of a hashed string.
     * @return The numeric representation of the hashed string.
     */
    [[nodiscard]] constexpr operator hash_type() const noexcept {
        return value();
    }
};

/**
 * @brief Deduction guide.
 * @tparam Char Character type.
 * @param str Human-readable identifier.
 * @param len Length of the string to hash.
 */
template<typename Char>
basic_hashed_string(const Char *str, std::size_t len) -> basic_hashed_string<Char>;

/**
 * @brief Deduction guide.
 * @tparam Char Character type.
 * @tparam N Number of characters of the identifier.
 * @param str Human-readable identifier.
 */
template<typename Char, std::size_t N>
// NOLINTNEXTLINE(cppcoreguidelines-avoid-c-arrays, modernize-avoid-c-arrays)
basic_hashed_string(const Char (&str)[N]) -> basic_hashed_string<Char>;

/**
 * @brief Compares two hashed strings.
 * @tparam Char Character type.
 * @param lhs A valid hashed string.
 * @param rhs A valid hashed string.
 * @return True if the two hashed strings are identical, false otherwise.
 */
template<typename Char>
[[nodiscard]] constexpr bool operator==(const basic_hashed_string<Char> &lhs, const basic_hashed_string<Char> &rhs) noexcept {
    return lhs.value() == rhs.value();
}

/**
 * @brief Compares two hashed strings.
 * @tparam Char Character type.
 * @param lhs A valid hashed string.
 * @param rhs A valid hashed string.
 * @return True if the two hashed strings differ, false otherwise.
 */
template<typename Char>
[[nodiscard]] constexpr bool operator!=(const basic_hashed_string<Char> &lhs, const basic_hashed_string<Char> &rhs) noexcept {
    return !(lhs == rhs);
}

/**
 * @brief Compares two hashed strings.
 * @tparam Char Character type.
 * @param lhs A valid hashed string.
 * @param rhs A valid hashed string.
 * @return True if the first element is less than the second, false otherwise.
 */
template<typename Char>
[[nodiscard]] constexpr bool operator<(const basic_hashed_string<Char> &lhs, const basic_hashed_string<Char> &rhs) noexcept {
    return lhs.value() < rhs.value();
}

/**
 * @brief Compares two hashed strings.
 * @tparam Char Character type.
 * @param lhs A valid hashed string.
 * @param rhs A valid hashed string.
 * @return True if the first element is less than or equal to the second, false
 * otherwise.
 */
template<typename Char>
[[nodiscard]] constexpr bool operator<=(const basic_hashed_string<Char> &lhs, const basic_hashed_string<Char> &rhs) noexcept {
    return !(rhs < lhs);
}

/**
 * @brief Compares two hashed strings.
 * @tparam Char Character type.
 * @param lhs A valid hashed string.
 * @param rhs A valid hashed string.
 * @return True if the first element is greater than the second, false
 * otherwise.
 */
template<typename Char>
[[nodiscard]] constexpr bool operator>(const basic_hashed_string<Char> &lhs, const basic_hashed_string<Char> &rhs) noexcept {
    return rhs < lhs;
}

/**
 * @brief Compares two hashed strings.
 * @tparam Char Character type.
 * @param lhs A valid hashed string.
 * @param rhs A valid hashed string.
 * @return True if the first element is greater than or equal to the second,
 * false otherwise.
 */
template<typename Char>
[[nodiscard]] constexpr bool operator>=(const basic_hashed_string<Char> &lhs, const basic_hashed_string<Char> &rhs) noexcept {
    return !(lhs < rhs);
}

inline namespace literals {

/**
 * @brief User defined literal for hashed strings.
 * @param str The literal without its suffix.
 * @return A properly initialized hashed string.
 */
[[nodiscard]] CONSTEVAL hashed_string operator""_hs(const char *str, std::size_t) noexcept {
    return hashed_string{str};
}

/**
 * @brief User defined literal for hashed wstrings.
 * @param str The literal without its suffix.
 * @return A properly initialized hashed wstring.
 */
[[nodiscard]] CONSTEVAL hashed_wstring operator""_hws(const wchar_t *str, std::size_t) noexcept {
    return hashed_wstring{str};
}

} // namespace literals


/*! @cond TURN_OFF_DOXYGEN */
namespace internal {

struct  type_index final {
    [[nodiscard]] static id_type next() noexcept {
        static MAYBE_ATOMIC(id_type) value{};
        return value++;
    }
};

template<typename Type>
[[nodiscard]] constexpr const char *pretty_function() noexcept {
#if defined PRETTY_FUNCTION
    return static_cast<const char *>(PRETTY_FUNCTION);
#else
    return "";
#endif
}

template<typename Type>
[[nodiscard]] constexpr auto stripped_type_name() noexcept {
#if defined PRETTY_FUNCTION
    const std::string_view full_name{pretty_function<Type>()};
    auto first = full_name.find_first_not_of(' ', full_name.find_first_of(PRETTY_FUNCTION_PREFIX) + 1);
    auto value = full_name.substr(first, full_name.find_last_of(PRETTY_FUNCTION_SUFFIX) - first);
    return value;
#else
    return std::string_view{};
#endif
}

template<typename Type, auto = stripped_type_name<Type>().find_first_of('.')>
[[nodiscard]] constexpr std::string_view type_name(int) noexcept {
    constexpr auto value = stripped_type_name<Type>();
    return value;
}

template<typename Type>
[[nodiscard]] std::string_view type_name(char) noexcept {
    static const auto value = stripped_type_name<Type>();
    return value;
}

template<typename Type, auto = stripped_type_name<Type>().find_first_of('.')>
[[nodiscard]] constexpr id_type type_hash(int) noexcept {
    constexpr auto stripped = stripped_type_name<Type>();
    constexpr auto value = hashed_string::value(stripped.data(), stripped.size());
    return value;
}

template<typename Type>
[[nodiscard]] id_type type_hash(char) noexcept {
    static const auto value = [](const auto stripped) {
        return hashed_string::value(stripped.data(), stripped.size());
    }(stripped_type_name<Type>());
    return value;
}

} // namespace internal
/*! @endcond */

/**
 * @brief Type sequential identifier.
 * @tparam Type Type for which to generate a sequential identifier.
 */
template<typename Type, typename = void>
struct  type_index final {
    /**
     * @brief Returns the sequential identifier of a given type.
     * @return The sequential identifier of a given type.
     */
    [[nodiscard]] static id_type value() noexcept {
        static const id_type value = internal::type_index::next();
        return value;
    }

    /*! @copydoc value */
    [[nodiscard]] constexpr operator id_type() const noexcept {
        return value();
    }
};

/**
 * @brief Type hash.
 * @tparam Type Type for which to generate a hash value.
 */
template<typename Type, typename = void>
struct type_hash final {
    /**
     * @brief Returns the numeric representation of a given type.
     * @return The numeric representation of the given type.
     */
#if defined PRETTY_FUNCTION
    [[nodiscard]] static constexpr id_type value() noexcept {
        return internal::type_hash<Type>(0);
#else
    [[nodiscard]] static constexpr id_type value() noexcept {
        return type_index<Type>::value();
#endif
    }

    /*! @copydoc value */
    [[nodiscard]] constexpr operator id_type() const noexcept {
        return value();
    }
};

/**
 * @brief Type name.
 * @tparam Type Type for which to generate a name.
 */
template<typename Type, typename = void>
struct type_name final {
    /**
     * @brief Returns the name of a given type.
     * @return The name of the given type.
     */
    [[nodiscard]] static constexpr std::string_view value() noexcept {
        return internal::type_name<Type>(0);
    }

    /*! @copydoc value */
    [[nodiscard]] constexpr operator std::string_view() const noexcept {
        return value();
    }
};

/*! @brief Implementation specific information about a type. */
struct type_info final {
    /**
     * @brief Constructs a type info object for a given type.
     * @tparam Type Type for which to construct a type info object.
     */
    template<typename Type>
    // NOLINTBEGIN(modernize-use-transparent-functors)
    constexpr type_info(std::in_place_type_t<Type>) noexcept
        : seq{type_index<std::remove_cv_t<std::remove_reference_t<Type>>>::value()},
        identifier{type_hash<std::remove_cv_t<std::remove_reference_t<Type>>>::value()},
        alias{type_name<std::remove_cv_t<std::remove_reference_t<Type>>>::value()} {}
    // NOLINTEND(modernize-use-transparent-functors)

    /**
     * @brief Type index.
     * @return Type index.
     */
    [[nodiscard]] constexpr id_type index() const noexcept {
        return seq;
    }

    /**
     * @brief Type hash.
     * @return Type hash.
     */
    [[nodiscard]] constexpr id_type hash() const noexcept {
        return identifier;
    }

    /**
     * @brief Type name.
     * @return Type name.
     */
    [[nodiscard]] constexpr std::string_view name() const noexcept {
        return alias;
    }

private:
    id_type seq;
    id_type identifier;
    std::string_view alias;
};

/**
 * @brief Compares the contents of two type info objects.
 * @param lhs A type info object.
 * @param rhs A type info object.
 * @return True if the two type info objects are identical, false otherwise.
 */
[[nodiscard]] constexpr bool operator==(const type_info &lhs, const type_info &rhs) noexcept {
    return lhs.hash() == rhs.hash();
}

/**
 * @brief Compares the contents of two type info objects.
 * @param lhs A type info object.
 * @param rhs A type info object.
 * @return True if the two type info objects differ, false otherwise.
 */
[[nodiscard]] constexpr bool operator!=(const type_info &lhs, const type_info &rhs) noexcept {
    return !(lhs == rhs);
}

/**
 * @brief Compares two type info objects.
 * @param lhs A valid type info object.
 * @param rhs A valid type info object.
 * @return True if the first element is less than the second, false otherwise.
 */
[[nodiscard]] constexpr bool operator<(const type_info &lhs, const type_info &rhs) noexcept {
    return lhs.index() < rhs.index();
}

/**
 * @brief Compares two type info objects.
 * @param lhs A valid type info object.
 * @param rhs A valid type info object.
 * @return True if the first element is less than or equal to the second, false
 * otherwise.
 */
[[nodiscard]] constexpr bool operator<=(const type_info &lhs, const type_info &rhs) noexcept {
    return !(rhs < lhs);
}

/**
 * @brief Compares two type info objects.
 * @param lhs A valid type info object.
 * @param rhs A valid type info object.
 * @return True if the first element is greater than the second, false
 * otherwise.
 */
[[nodiscard]] constexpr bool operator>(const type_info &lhs, const type_info &rhs) noexcept {
    return rhs < lhs;
}

/**
 * @brief Compares two type info objects.
 * @param lhs A valid type info object.
 * @param rhs A valid type info object.
 * @return True if the first element is greater than or equal to the second,
 * false otherwise.
 */
[[nodiscard]] constexpr bool operator>=(const type_info &lhs, const type_info &rhs) noexcept {
    return !(lhs < rhs);
}

/**
 * @brief Returns the type info object associated to a given type.
 *
 * The returned element refers to an object with static storage duration.<br/>
 * The type doesn't need to be a complete type. If the type is a reference, the
 * result refers to the referenced type. In all cases, top-level cv-qualifiers
 * are ignored.
 *
 * @tparam Type Type for which to generate a type info object.
 * @return A reference to a properly initialized type info object.
 */
template<typename Type>
[[nodiscard]] const type_info &type_id() noexcept {
    if constexpr(std::is_same_v<Type, std::remove_cv_t<std::remove_reference_t<Type>>>) {
        static const type_info instance{std::in_place_type<Type>};
        return instance;
    } else {
        return type_id<std::remove_cv_t<std::remove_reference_t<Type>>>();
    }
}

/*! @copydoc type_id */
template<typename Type>
// NOLINTNEXTLINE(cppcoreguidelines-missing-std-forward)
[[nodiscard]] const type_info &type_id(Type &&) noexcept {
    return type_id<std::remove_cv_t<std::remove_reference_t<Type>>>();
}


/*! @cond TURN_OFF_DOXYGEN */
namespace internal {

template<typename Type, std::size_t, typename = void>
struct compressed_pair_element {
    using reference = Type &;
    using const_reference = const Type &;

    template<typename Dummy = Type, typename = std::enable_if_t<std::is_default_constructible_v<Dummy>>>
    // NOLINTNEXTLINE(modernize-use-equals-default)
    constexpr compressed_pair_element() noexcept(std::is_nothrow_default_constructible_v<Type>) {}

    template<typename Arg, typename = std::enable_if_t<!std::is_same_v<std::remove_cv_t<std::remove_reference_t<Arg>>, compressed_pair_element>>>
    constexpr compressed_pair_element(Arg &&arg) noexcept(std::is_nothrow_constructible_v<Type, Arg>)
        : value{std::forward<Arg>(arg)} {}

    template<typename... Args, std::size_t... Index>
    constexpr compressed_pair_element(std::tuple<Args...> args, std::index_sequence<Index...>) noexcept(std::is_nothrow_constructible_v<Type, Args...>)
        : value{std::forward<Args>(std::get<Index>(args))...} {}

    [[nodiscard]] constexpr reference get() noexcept {
        return value;
    }

    [[nodiscard]] constexpr const_reference get() const noexcept {
        return value;
    }

private:
    Type value{};
};

template<typename Type, std::size_t Tag>
struct compressed_pair_element<Type, Tag, std::enable_if_t<is_ebco_eligible_v<Type>>>: Type {
    using reference = Type &;
    using const_reference = const Type &;
    using base_type = Type;

    template<typename Dummy = Type, typename = std::enable_if_t<std::is_default_constructible_v<Dummy>>>
    constexpr compressed_pair_element() noexcept(std::is_nothrow_default_constructible_v<base_type>)
        : base_type{} {}

    template<typename Arg, typename = std::enable_if_t<!std::is_same_v<std::remove_cv_t<std::remove_reference_t<Arg>>, compressed_pair_element>>>
    constexpr compressed_pair_element(Arg &&arg) noexcept(std::is_nothrow_constructible_v<base_type, Arg>)
        : base_type{std::forward<Arg>(arg)} {}

    template<typename... Args, std::size_t... Index>
    constexpr compressed_pair_element(std::tuple<Args...> args, std::index_sequence<Index...>) noexcept(std::is_nothrow_constructible_v<base_type, Args...>)
        : base_type{std::forward<Args>(std::get<Index>(args))...} {}

    [[nodiscard]] constexpr reference get() noexcept {
        return *this;
    }

    [[nodiscard]] constexpr const_reference get() const noexcept {
        return *this;
    }
};

} // namespace internal
/*! @endcond */

/**
 * @brief A compressed pair.
 *
 * A pair that exploits the _Empty Base Class Optimization_ (or _EBCO_) to
 * reduce its final size to a minimum.
 *
 * @tparam First The type of the first element that the pair stores.
 * @tparam Second The type of the second element that the pair stores.
 */
template<typename First, typename Second>
class compressed_pair final
    : internal::compressed_pair_element<First, 0u>,
      internal::compressed_pair_element<Second, 1u> {
    using first_base = internal::compressed_pair_element<First, 0u>;
    using second_base = internal::compressed_pair_element<Second, 1u>;

public:
    /*! @brief The type of the first element that the pair stores. */
    using first_type = First;
    /*! @brief The type of the second element that the pair stores. */
    using second_type = Second;

    /**
     * @brief Default constructor, conditionally enabled.
     *
     * This constructor is only available when the types that the pair stores
     * are both at least default constructible.
     *
     * @tparam Dummy Dummy template parameter used for internal purposes.
     */
    template<bool Dummy = true, typename = std::enable_if_t<Dummy && std::is_default_constructible_v<first_type> && std::is_default_constructible_v<second_type>>>
    constexpr compressed_pair() noexcept(std::is_nothrow_default_constructible_v<first_base> && std::is_nothrow_default_constructible_v<second_base>)
        : first_base{},
        second_base{} {}

    /**
     * @brief Copy constructor.
     * @param other The instance to copy from.
     */
    constexpr compressed_pair(const compressed_pair &other) = default;

    /**
     * @brief Move constructor.
     * @param other The instance to move from.
     */
    constexpr compressed_pair(compressed_pair &&other) noexcept = default;

    /**
     * @brief Constructs a pair from its values.
     * @tparam Arg Type of value to use to initialize the first element.
     * @tparam Other Type of value to use to initialize the second element.
     * @param arg Value to use to initialize the first element.
     * @param other Value to use to initialize the second element.
     */
    template<typename Arg, typename Other>
    constexpr compressed_pair(Arg &&arg, Other &&other) noexcept(std::is_nothrow_constructible_v<first_base, Arg> && std::is_nothrow_constructible_v<second_base, Other>)
        : first_base{std::forward<Arg>(arg)},
        second_base{std::forward<Other>(other)} {}

    /**
     * @brief Constructs a pair by forwarding the arguments to its parts.
     * @tparam Args Types of arguments to use to initialize the first element.
     * @tparam Other Types of arguments to use to initialize the second element.
     * @param args Arguments to use to initialize the first element.
     * @param other Arguments to use to initialize the second element.
     */
    template<typename... Args, typename... Other>
    constexpr compressed_pair(std::piecewise_construct_t, std::tuple<Args...> args, std::tuple<Other...> other) noexcept(std::is_nothrow_constructible_v<first_base, Args...> && std::is_nothrow_constructible_v<second_base, Other...>)
        : first_base{std::move(args), std::index_sequence_for<Args...>{}},
        second_base{std::move(other), std::index_sequence_for<Other...>{}} {}

    /*! @brief Default destructor. */
    ~compressed_pair() = default;

    /**
     * @brief Copy assignment operator.
     * @param other The instance to copy from.
     * @return This compressed pair object.
     */
    constexpr compressed_pair &operator=(const compressed_pair &other) = default;

    /**
     * @brief Move assignment operator.
     * @param other The instance to move from.
     * @return This compressed pair object.
     */
    constexpr compressed_pair &operator=(compressed_pair &&other) noexcept = default;

    /**
     * @brief Returns the first element that a pair stores.
     * @return The first element that a pair stores.
     */
    [[nodiscard]] constexpr first_type &first() noexcept {
        return static_cast<first_base &>(*this).get();
    }

    /*! @copydoc first */
    [[nodiscard]] constexpr const first_type &first() const noexcept {
        return static_cast<const first_base &>(*this).get();
    }

    /**
     * @brief Returns the second element that a pair stores.
     * @return The second element that a pair stores.
     */
    [[nodiscard]] constexpr second_type &second() noexcept {
        return static_cast<second_base &>(*this).get();
    }

    /*! @copydoc second */
    [[nodiscard]] constexpr const second_type &second() const noexcept {
        return static_cast<const second_base &>(*this).get();
    }

    /**
     * @brief Swaps two compressed pair objects.
     * @param other The compressed pair to swap with.
     */
    constexpr void swap(compressed_pair &other) noexcept {
        using std::swap;
        swap(first(), other.first());
        swap(second(), other.second());
    }

    /**
     * @brief Extracts an element from the compressed pair.
     * @tparam Index An integer value that is either 0 or 1.
     * @return Returns a reference to the first element if `Index` is 0 and a
     * reference to the second element if `Index` is 1.
     */
    template<std::size_t Index>
    [[nodiscard]] constexpr decltype(auto) get() noexcept {
        if constexpr(Index == 0u) {
            return first();
        } else {
            static_assert(Index == 1u, "Index out of bounds");
            return second();
        }
    }

    /*! @copydoc get */
    template<std::size_t Index>
    [[nodiscard]] constexpr decltype(auto) get() const noexcept {
        if constexpr(Index == 0u) {
            return first();
        } else {
            static_assert(Index == 1u, "Index out of bounds");
            return second();
        }
    }
};

/**
 * @brief Deduction guide.
 * @tparam Type Type of value to use to initialize the first element.
 * @tparam Other Type of value to use to initialize the second element.
 */
template<typename Type, typename Other>
compressed_pair(Type &&, Other &&) -> compressed_pair<std::decay_t<Type>, std::decay_t<Other>>;

/**
 * @brief Swaps two compressed pair objects.
 * @tparam First The type of the first element that the pairs store.
 * @tparam Second The type of the second element that the pairs store.
 * @param lhs A valid compressed pair object.
 * @param rhs A valid compressed pair object.
 */
template<typename First, typename Second>
constexpr void swap(compressed_pair<First, Second> &lhs, compressed_pair<First, Second> &rhs) noexcept {
    lhs.swap(rhs);
}


/**
 * @brief Returns the number of set bits in a value (waiting for C++20 and
 * `std::popcount`).
 * @tparam Type Unsigned integer type.
 * @param value A value of unsigned integer type.
 * @return The number of set bits in the value.
 */
template<typename Type>
[[nodiscard]] constexpr std::enable_if_t<std::is_unsigned_v<Type>, int> popcount(const Type value) noexcept {
    return value ? (int(value & 1) + popcount(static_cast<Type>(value >> 1))) : 0;
}

/**
 * @brief Checks whether a value is a power of two or not (waiting for C++20 and
 * `std::has_single_bit`).
 * @tparam Type Unsigned integer type.
 * @param value A value of unsigned integer type.
 * @return True if the value is a power of two, false otherwise.
 */
template<typename Type>
[[nodiscard]] constexpr std::enable_if_t<std::is_unsigned_v<Type>, bool> has_single_bit(const Type value) noexcept {
    return value && ((value & (value - 1)) == 0);
}

/**
 * @brief Computes the smallest power of two greater than or equal to a value
 * (waiting for C++20 and `std::bit_ceil`).
 * @tparam Type Unsigned integer type.
 * @param value A value of unsigned integer type.
 * @return The smallest power of two greater than or equal to the given value.
 */
template<typename Type>
[[nodiscard]] constexpr std::enable_if_t<std::is_unsigned_v<Type>, Type> next_power_of_two(const Type value) noexcept {
    // NOLINTNEXTLINE(bugprone-assert-side-effect)
    ASSERT_CONSTEXPR(value < (Type{1u} << (std::numeric_limits<Type>::digits - 1)), "Numeric limits exceeded");
    Type curr = value - (value != 0u);

    for(int next = 1; next < std::numeric_limits<Type>::digits; next = next * 2) {
        curr |= (curr >> next);
    }

    return ++curr;
}

/**
 * @brief Fast module utility function (powers of two only).
 * @tparam Type Unsigned integer type.
 * @param value A value of unsigned integer type.
 * @param mod _Modulus_, it must be a power of two.
 * @return The common remainder.
 */
template<typename Type>
[[nodiscard]] constexpr std::enable_if_t<std::is_unsigned_v<Type>, Type> fast_mod(const Type value, const std::size_t mod) noexcept {
    ASSERT_CONSTEXPR(has_single_bit(mod), "Value must be a power of two");
    return static_cast<Type>(value & (mod - 1u));
}


/*! @cond TURN_OFF_DOXYGEN */
namespace internal {

template<typename Key, typename Type>
struct dense_map_node final {
    using value_type = std::pair<Key, Type>;

    template<typename... Args>
    dense_map_node(const std::size_t pos, Args &&...args)
        : next{pos},
        element{std::forward<Args>(args)...} {}

    template<typename Allocator, typename... Args>
    dense_map_node(std::allocator_arg_t, const Allocator &allocator, const std::size_t pos, Args &&...args)
        : next{pos},
        element{make_obj_using_allocator<value_type>(allocator, std::forward<Args>(args)...)} {}

    template<typename Allocator>
    dense_map_node(std::allocator_arg_t, const Allocator &allocator, const dense_map_node &other)
        : next{other.next},
        element{make_obj_using_allocator<value_type>(allocator, other.element)} {}

    template<typename Allocator>
    dense_map_node(std::allocator_arg_t, const Allocator &allocator, dense_map_node &&other)
        : next{other.next},
        element{make_obj_using_allocator<value_type>(allocator, std::move(other.element))} {}

    std::size_t next;
    value_type element;
};

template<typename It>
class dense_map_iterator final {
    template<typename>
    friend class dense_map_iterator;

    using first_type = decltype(std::as_const(std::declval<It>()->element.first));
    using second_type = decltype((std::declval<It>()->element.second));

public:
    using value_type = std::pair<first_type, second_type>;
    using pointer = input_iterator_pointer<value_type>;
    using reference = value_type;
    using difference_type = std::ptrdiff_t;
    using iterator_category = std::input_iterator_tag;
    using iterator_concept = std::random_access_iterator_tag;

    constexpr dense_map_iterator() noexcept
        : it{} {}

    constexpr dense_map_iterator(const It iter) noexcept
        : it{iter} {}

    template<typename Other, typename = std::enable_if_t<!std::is_same_v<It, Other> && std::is_constructible_v<It, Other>>>
    constexpr dense_map_iterator(const dense_map_iterator<Other> &other) noexcept
        : it{other.it} {}

    constexpr dense_map_iterator &operator++() noexcept {
        return ++it, *this;
    }

    constexpr dense_map_iterator operator++(int) noexcept {
        const dense_map_iterator orig = *this;
        return ++(*this), orig;
    }

    constexpr dense_map_iterator &operator--() noexcept {
        return --it, *this;
    }

    constexpr dense_map_iterator operator--(int) noexcept {
        const dense_map_iterator orig = *this;
        return operator--(), orig;
    }

    constexpr dense_map_iterator &operator+=(const difference_type value) noexcept {
        it += value;
        return *this;
    }

    constexpr dense_map_iterator operator+(const difference_type value) const noexcept {
        dense_map_iterator copy = *this;
        return (copy += value);
    }

    constexpr dense_map_iterator &operator-=(const difference_type value) noexcept {
        return (*this += -value);
    }

    constexpr dense_map_iterator operator-(const difference_type value) const noexcept {
        return (*this + -value);
    }

    [[nodiscard]] constexpr reference operator[](const difference_type value) const noexcept {
        return {it[value].element.first, it[value].element.second};
    }

    [[nodiscard]] constexpr pointer operator->() const noexcept {
        return operator*();
    }

    [[nodiscard]] constexpr reference operator*() const noexcept {
        return operator[](0);
    }

    template<typename Lhs, typename Rhs>
    friend constexpr std::ptrdiff_t operator-(const dense_map_iterator<Lhs> &, const dense_map_iterator<Rhs> &) noexcept;

    template<typename Lhs, typename Rhs>
    friend constexpr bool operator==(const dense_map_iterator<Lhs> &, const dense_map_iterator<Rhs> &) noexcept;

    template<typename Lhs, typename Rhs>
    friend constexpr bool operator<(const dense_map_iterator<Lhs> &, const dense_map_iterator<Rhs> &) noexcept;

private:
    It it;
};

template<typename Lhs, typename Rhs>
[[nodiscard]] constexpr std::ptrdiff_t operator-(const dense_map_iterator<Lhs> &lhs, const dense_map_iterator<Rhs> &rhs) noexcept {
    return lhs.it - rhs.it;
}

template<typename Lhs, typename Rhs>
[[nodiscard]] constexpr bool operator==(const dense_map_iterator<Lhs> &lhs, const dense_map_iterator<Rhs> &rhs) noexcept {
    return lhs.it == rhs.it;
}

template<typename Lhs, typename Rhs>
[[nodiscard]] constexpr bool operator!=(const dense_map_iterator<Lhs> &lhs, const dense_map_iterator<Rhs> &rhs) noexcept {
    return !(lhs == rhs);
}

template<typename Lhs, typename Rhs>
[[nodiscard]] constexpr bool operator<(const dense_map_iterator<Lhs> &lhs, const dense_map_iterator<Rhs> &rhs) noexcept {
    return lhs.it < rhs.it;
}

template<typename Lhs, typename Rhs>
[[nodiscard]] constexpr bool operator>(const dense_map_iterator<Lhs> &lhs, const dense_map_iterator<Rhs> &rhs) noexcept {
    return rhs < lhs;
}

template<typename Lhs, typename Rhs>
[[nodiscard]] constexpr bool operator<=(const dense_map_iterator<Lhs> &lhs, const dense_map_iterator<Rhs> &rhs) noexcept {
    return !(lhs > rhs);
}

template<typename Lhs, typename Rhs>
[[nodiscard]] constexpr bool operator>=(const dense_map_iterator<Lhs> &lhs, const dense_map_iterator<Rhs> &rhs) noexcept {
    return !(lhs < rhs);
}

template<typename It>
class dense_map_local_iterator final {
    template<typename>
    friend class dense_map_local_iterator;

    using first_type = decltype(std::as_const(std::declval<It>()->element.first));
    using second_type = decltype((std::declval<It>()->element.second));

public:
    using value_type = std::pair<first_type, second_type>;
    using pointer = input_iterator_pointer<value_type>;
    using reference = value_type;
    using difference_type = std::ptrdiff_t;
    using iterator_category = std::input_iterator_tag;
    using iterator_concept = std::forward_iterator_tag;

    constexpr dense_map_local_iterator() noexcept
        : it{},
        offset{} {}

    constexpr dense_map_local_iterator(It iter, const std::size_t pos) noexcept
        : it{iter},
        offset{pos} {}

    template<typename Other, typename = std::enable_if_t<!std::is_same_v<It, Other> && std::is_constructible_v<It, Other>>>
    constexpr dense_map_local_iterator(const dense_map_local_iterator<Other> &other) noexcept
        : it{other.it},
        offset{other.offset} {}

    constexpr dense_map_local_iterator &operator++() noexcept {
        return (offset = it[static_cast<typename It::difference_type>(offset)].next), *this;
    }

    constexpr dense_map_local_iterator operator++(int) noexcept {
        const dense_map_local_iterator orig = *this;
        return ++(*this), orig;
    }

    [[nodiscard]] constexpr pointer operator->() const noexcept {
        return operator*();
    }

    [[nodiscard]] constexpr reference operator*() const noexcept {
        const auto idx = static_cast<typename It::difference_type>(offset);
        return {it[idx].element.first, it[idx].element.second};
    }

    [[nodiscard]] constexpr std::size_t index() const noexcept {
        return offset;
    }

private:
    It it;
    std::size_t offset;
};

template<typename Lhs, typename Rhs>
[[nodiscard]] constexpr bool operator==(const dense_map_local_iterator<Lhs> &lhs, const dense_map_local_iterator<Rhs> &rhs) noexcept {
    return lhs.index() == rhs.index();
}

template<typename Lhs, typename Rhs>
[[nodiscard]] constexpr bool operator!=(const dense_map_local_iterator<Lhs> &lhs, const dense_map_local_iterator<Rhs> &rhs) noexcept {
    return !(lhs == rhs);
}

} // namespace internal
/*! @endcond */

/**
 * @brief Associative container for key-value pairs with unique keys.
 *
 * Internally, elements are organized into buckets. Which bucket an element is
 * placed into depends entirely on the hash of its key. Keys with the same hash
 * code appear in the same bucket.
 *
 * @tparam Key Key type of the associative container.
 * @tparam Type Mapped type of the associative container.
 * @tparam Hash Type of function to use to hash the keys.
 * @tparam KeyEqual Type of function to use to compare the keys for equality.
 * @tparam Allocator Type of allocator used to manage memory and elements.
 */
template<typename Key, typename Type, typename Hash, typename KeyEqual, typename Allocator>
class dense_map {
    static constexpr float default_threshold = 0.875f;
    static constexpr std::size_t minimum_capacity = 8u;

    using node_type = internal::dense_map_node<Key, Type>;
    using alloc_traits = std::allocator_traits<Allocator>;
    static_assert(std::is_same_v<typename alloc_traits::value_type, std::pair<const Key, Type>>, "Invalid value type");
    using sparse_container_type = std::vector<std::size_t, typename alloc_traits::template rebind_alloc<std::size_t>>;
    using packed_container_type = std::vector<node_type, typename alloc_traits::template rebind_alloc<node_type>>;

    template<typename Other>
    [[nodiscard]] std::size_t key_to_bucket(const Other &key) const noexcept {
        // NOLINTNEXTLINE(cppcoreguidelines-pro-bounds-array-to-pointer-decay)
        return fast_mod(static_cast<size_type>(sparse.second()(key)), bucket_count());
    }

    template<typename Other>
    [[nodiscard]] auto constrained_find(const Other &key, std::size_t bucket) {
        for(auto it = begin(bucket), last = end(bucket); it != last; ++it) {
            if(packed.second()(it->first, key)) {
                return begin() + static_cast<difference_type>(it.index());
            }
        }

        return end();
    }

    template<typename Other>
    [[nodiscard]] auto constrained_find(const Other &key, std::size_t bucket) const {
        for(auto it = cbegin(bucket), last = cend(bucket); it != last; ++it) {
            if(packed.second()(it->first, key)) {
                return cbegin() + static_cast<difference_type>(it.index());
            }
        }

        return cend();
    }

    template<typename Other, typename... Args>
    [[nodiscard]] auto insert_or_do_nothing(Other &&key, Args &&...args) {
        const auto index = key_to_bucket(key);

        if(auto it = constrained_find(key, index); it != end()) {
            return std::make_pair(it, false);
        }

        packed.first().emplace_back(sparse.first()[index], std::piecewise_construct, std::forward_as_tuple(std::forward<Other>(key)), std::forward_as_tuple(std::forward<Args>(args)...));
        sparse.first()[index] = packed.first().size() - 1u;
        rehash_if_required();

        return std::make_pair(--end(), true);
    }

    template<typename Other, typename Arg>
    [[nodiscard]] auto insert_or_overwrite(Other &&key, Arg &&value) {
        const auto index = key_to_bucket(key);

        if(auto it = constrained_find(key, index); it != end()) {
            it->second = std::forward<Arg>(value);
            return std::make_pair(it, false);
        }

        packed.first().emplace_back(sparse.first()[index], std::forward<Other>(key), std::forward<Arg>(value));
        sparse.first()[index] = packed.first().size() - 1u;
        rehash_if_required();

        return std::make_pair(--end(), true);
    }

    void move_and_pop(const std::size_t pos) {
        if(const auto last = size() - 1u; pos != last) {
            size_type *curr = &sparse.first()[key_to_bucket(packed.first().back().element.first)];
            packed.first()[pos] = std::move(packed.first().back());
            for(; *curr != last; curr = &packed.first()[*curr].next) {}
            *curr = pos;
        }

        packed.first().pop_back();
    }

    void rehash_if_required() {
        if(const auto bc = bucket_count(); size() > static_cast<size_type>(static_cast<float>(bc) * max_load_factor())) {
            rehash(bc * 2u);
        }
    }

public:
    /*! @brief Allocator type. */
    using allocator_type = Allocator;
    /*! @brief Key type of the container. */
    using key_type = Key;
    /*! @brief Mapped type of the container. */
    using mapped_type = Type;
    /*! @brief Key-value type of the container. */
    using value_type = std::pair<const Key, Type>;
    /*! @brief Unsigned integer type. */
    using size_type = std::size_t;
    /*! @brief Signed integer type. */
    using difference_type = std::ptrdiff_t;
    /*! @brief Type of function to use to hash the keys. */
    using hasher = Hash;
    /*! @brief Type of function to use to compare the keys for equality. */
    using key_equal = KeyEqual;
    /*! @brief Input iterator type. */
    using iterator = internal::dense_map_iterator<typename packed_container_type::iterator>;
    /*! @brief Constant input iterator type. */
    using const_iterator = internal::dense_map_iterator<typename packed_container_type::const_iterator>;
    /*! @brief Input iterator type. */
    using local_iterator = internal::dense_map_local_iterator<typename packed_container_type::iterator>;
    /*! @brief Constant input iterator type. */
    using const_local_iterator = internal::dense_map_local_iterator<typename packed_container_type::const_iterator>;

    /*! @brief Default constructor. */
    dense_map()
        : dense_map{minimum_capacity} {}

    /**
     * @brief Constructs an empty container with a given allocator.
     * @param allocator The allocator to use.
     */
    explicit dense_map(const allocator_type &allocator)
        : dense_map{minimum_capacity, hasher{}, key_equal{}, allocator} {}

    /**
     * @brief Constructs an empty container with a given allocator and user
     * supplied minimal number of buckets.
     * @param cnt Minimal number of buckets.
     * @param allocator The allocator to use.
     */
    dense_map(const size_type cnt, const allocator_type &allocator)
        : dense_map{cnt, hasher{}, key_equal{}, allocator} {}

    /**
     * @brief Constructs an empty container with a given allocator, hash
     * function and user supplied minimal number of buckets.
     * @param cnt Minimal number of buckets.
     * @param hash Hash function to use.
     * @param allocator The allocator to use.
     */
    dense_map(const size_type cnt, const hasher &hash, const allocator_type &allocator)
        : dense_map{cnt, hash, key_equal{}, allocator} {}

    /**
     * @brief Constructs an empty container with a given allocator, hash
     * function, compare function and user supplied minimal number of buckets.
     * @param cnt Minimal number of buckets.
     * @param hash Hash function to use.
     * @param equal Compare function to use.
     * @param allocator The allocator to use.
     */
    explicit dense_map(const size_type cnt, const hasher &hash = hasher{}, const key_equal &equal = key_equal{}, const allocator_type &allocator = allocator_type{})
        : sparse{allocator, hash},
        packed{allocator, equal} {
        rehash(cnt);
    }

    /*! @brief Default copy constructor. */
    dense_map(const dense_map &) = default;

    /**
     * @brief Allocator-extended copy constructor.
     * @param other The instance to copy from.
     * @param allocator The allocator to use.
     */
    dense_map(const dense_map &other, const allocator_type &allocator)
        : sparse{std::piecewise_construct, std::forward_as_tuple(other.sparse.first(), allocator), std::forward_as_tuple(other.sparse.second())},
        packed{std::piecewise_construct, std::forward_as_tuple(other.packed.first(), allocator), std::forward_as_tuple(other.packed.second())},
        threshold{other.threshold} {}

    /*! @brief Default move constructor. */
    dense_map(dense_map &&) noexcept = default;

    /**
     * @brief Allocator-extended move constructor.
     * @param other The instance to move from.
     * @param allocator The allocator to use.
     */
    dense_map(dense_map &&other, const allocator_type &allocator)
        : sparse{std::piecewise_construct, std::forward_as_tuple(std::move(other.sparse.first()), allocator), std::forward_as_tuple(std::move(other.sparse.second()))},
        packed{std::piecewise_construct, std::forward_as_tuple(std::move(other.packed.first()), allocator), std::forward_as_tuple(std::move(other.packed.second()))},
        threshold{other.threshold} {}

    /*! @brief Default destructor. */
    ~dense_map() = default;

    /**
     * @brief Default copy assignment operator.
     * @return This container.
     */
    dense_map &operator=(const dense_map &) = default;

    /**
     * @brief Default move assignment operator.
     * @return This container.
     */
    dense_map &operator=(dense_map &&) noexcept = default;

    /**
     * @brief Exchanges the contents with those of a given container.
     * @param other Container to exchange the content with.
     */
    void swap(dense_map &other) noexcept {
        using std::swap;
        swap(sparse, other.sparse);
        swap(packed, other.packed);
        swap(threshold, other.threshold);
    }

    /**
     * @brief Returns the associated allocator.
     * @return The associated allocator.
     */
    [[nodiscard]] constexpr allocator_type get_allocator() const noexcept {
        return sparse.first().get_allocator();
    }

    /**
     * @brief Returns an iterator to the beginning.
     *
     * If the array is empty, the returned iterator will be equal to `end()`.
     *
     * @return An iterator to the first instance of the internal array.
     */
    [[nodiscard]] const_iterator cbegin() const noexcept {
        return packed.first().begin();
    }

    /*! @copydoc cbegin */
    [[nodiscard]] const_iterator begin() const noexcept {
        return cbegin();
    }

    /*! @copydoc begin */
    [[nodiscard]] iterator begin() noexcept {
        return packed.first().begin();
    }

    /**
     * @brief Returns an iterator to the end.
     * @return An iterator to the element following the last instance of the
     * internal array.
     */
    [[nodiscard]] const_iterator cend() const noexcept {
        return packed.first().end();
    }

    /*! @copydoc cend */
    [[nodiscard]] const_iterator end() const noexcept {
        return cend();
    }

    /*! @copydoc end */
    [[nodiscard]] iterator end() noexcept {
        return packed.first().end();
    }

    /**
     * @brief Checks whether a container is empty.
     * @return True if the container is empty, false otherwise.
     */
    [[nodiscard]] bool empty() const noexcept {
        return packed.first().empty();
    }

    /**
     * @brief Returns the number of elements in a container.
     * @return Number of elements in a container.
     */
    [[nodiscard]] size_type size() const noexcept {
        return packed.first().size();
    }

    /**
     * @brief Returns the maximum possible number of elements.
     * @return Maximum possible number of elements.
     */
    [[nodiscard]] size_type max_size() const noexcept {
        return packed.first().max_size();
    }

    /*! @brief Clears the container. */
    void clear() noexcept {
        sparse.first().clear();
        packed.first().clear();
        rehash(0u);
    }

    /**
     * @brief Inserts an element into the container, if the key does not exist.
     * @param value A key-value pair eventually convertible to the value type.
     * @return A pair consisting of an iterator to the inserted element (or to
     * the element that prevented the insertion) and a bool denoting whether the
     * insertion took place.
     */
    std::pair<iterator, bool> insert(const value_type &value) {
        return insert_or_do_nothing(value.first, value.second);
    }

    /*! @copydoc insert */
    std::pair<iterator, bool> insert(value_type &&value) {
        return insert_or_do_nothing(std::move(value.first), std::move(value.second));
    }

    /**
     * @copydoc insert
     * @tparam Arg Type of the key-value pair to insert into the container.
     */
    template<typename Arg>
    std::enable_if_t<std::is_constructible_v<value_type, Arg &&>, std::pair<iterator, bool>>
    insert(Arg &&value) {
        return insert_or_do_nothing(std::forward<Arg>(value).first, std::forward<Arg>(value).second);
    }

    /**
     * @brief Inserts elements into the container, if their keys do not exist.
     * @tparam It Type of input iterator.
     * @param first An iterator to the first element of the range of elements.
     * @param last An iterator past the last element of the range of elements.
     */
    template<typename It>
    void insert(It first, It last) {
        for(; first != last; ++first) {
            insert(*first);
        }
    }

    /**
     * @brief Inserts an element into the container or assigns to the current
     * element if the key already exists.
     * @tparam Arg Type of the value to insert or assign.
     * @param key A key used both to look up and to insert if not found.
     * @param value A value to insert or assign.
     * @return A pair consisting of an iterator to the element and a bool
     * denoting whether the insertion took place.
     */
    template<typename Arg>
    std::pair<iterator, bool> insert_or_assign(const key_type &key, Arg &&value) {
        return insert_or_overwrite(key, std::forward<Arg>(value));
    }

    /*! @copydoc insert_or_assign */
    template<typename Arg>
    std::pair<iterator, bool> insert_or_assign(key_type &&key, Arg &&value) {
        return insert_or_overwrite(std::move(key), std::forward<Arg>(value));
    }

    /**
     * @brief Constructs an element in-place, if the key does not exist.
     *
     * The element is also constructed when the container already has the key,
     * in which case the newly constructed object is destroyed immediately.
     *
     * @tparam Args Types of arguments to forward to the constructor of the
     * element.
     * @param args Arguments to forward to the constructor of the element.
     * @return A pair consisting of an iterator to the inserted element (or to
     * the element that prevented the insertion) and a bool denoting whether the
     * insertion took place.
     */
    template<typename... Args>
    std::pair<iterator, bool> emplace([[maybe_unused]] Args &&...args) {
        if constexpr(sizeof...(Args) == 0u) {
            return insert_or_do_nothing(key_type{});
        } else if constexpr(sizeof...(Args) == 1u) {
            return insert_or_do_nothing(std::forward<Args>(args).first..., std::forward<Args>(args).second...);
        } else if constexpr(sizeof...(Args) == 2u) {
            return insert_or_do_nothing(std::forward<Args>(args)...);
        } else {
            auto &node = packed.first().emplace_back(packed.first().size(), std::forward<Args>(args)...);
            const auto index = key_to_bucket(node.element.first);

            if(auto it = constrained_find(node.element.first, index); it != end()) {
                packed.first().pop_back();
                return std::make_pair(it, false);
            }

            std::swap(node.next, sparse.first()[index]);
            rehash_if_required();

            return std::make_pair(--end(), true);
        }
    }

    /**
     * @brief Inserts in-place if the key does not exist, does nothing if the
     * key exists.
     * @tparam Args Types of arguments to forward to the constructor of the
     * element.
     * @param key A key used both to look up and to insert if not found.
     * @param args Arguments to forward to the constructor of the element.
     * @return A pair consisting of an iterator to the inserted element (or to
     * the element that prevented the insertion) and a bool denoting whether the
     * insertion took place.
     */
    template<typename... Args>
    std::pair<iterator, bool> try_emplace(const key_type &key, Args &&...args) {
        return insert_or_do_nothing(key, std::forward<Args>(args)...);
    }

    /*! @copydoc try_emplace */
    template<typename... Args>
    std::pair<iterator, bool> try_emplace(key_type &&key, Args &&...args) {
        return insert_or_do_nothing(std::move(key), std::forward<Args>(args)...);
    }

    /**
     * @brief Removes an element from a given position.
     * @param pos An iterator to the element to remove.
     * @return An iterator following the removed element.
     */
    iterator erase(const_iterator pos) {
        const auto diff = pos - cbegin();
        erase(pos->first);
        return begin() + diff;
    }

    /**
     * @brief Removes the given elements from a container.
     * @param first An iterator to the first element of the range of elements.
     * @param last An iterator past the last element of the range of elements.
     * @return An iterator following the last removed element.
     */
    iterator erase(const_iterator first, const_iterator last) {
        const auto dist = first - cbegin();

        for(auto from = last - cbegin(); from != dist; --from) {
            erase(packed.first()[static_cast<size_type>(from) - 1u].element.first);
        }

        return (begin() + dist);
    }

    /**
     * @brief Removes the element associated with a given key.
     * @param key A key value of an element to remove.
     * @return Number of elements removed (either 0 or 1).
     */
    size_type erase(const key_type &key) {
        for(size_type *curr = &sparse.first()[key_to_bucket(key)]; *curr != (std::numeric_limits<size_type>::max)(); curr = &packed.first()[*curr].next) {
            if(packed.second()(packed.first()[*curr].element.first, key)) {
                const auto index = *curr;
                *curr = packed.first()[*curr].next;
                move_and_pop(index);
                return 1u;
            }
        }

        return 0u;
    }

    /**
     * @brief Accesses a given element with bounds checking.
     * @param key A key of an element to find.
     * @return A reference to the mapped value of the requested element.
     */
    [[nodiscard]] mapped_type &at(const key_type &key) {
        auto it = find(key);
        ASSERT(it != end(), "Invalid key");
        return it->second;
    }

    /*! @copydoc at */
    [[nodiscard]] const mapped_type &at(const key_type &key) const {
        auto it = find(key);
        ASSERT(it != cend(), "Invalid key");
        return it->second;
    }

    /**
     * @brief Accesses or inserts a given element.
     * @param key A key of an element to find or insert.
     * @return A reference to the mapped value of the requested element.
     */
    [[nodiscard]] mapped_type &operator[](const key_type &key) {
        return insert_or_do_nothing(key).first->second;
    }

    /**
     * @brief Accesses or inserts a given element.
     * @param key A key of an element to find or insert.
     * @return A reference to the mapped value of the requested element.
     */
    [[nodiscard]] mapped_type &operator[](key_type &&key) {
        return insert_or_do_nothing(std::move(key)).first->second;
    }

    /**
     * @brief Returns the number of elements matching a key (either 1 or 0).
     * @param key Key value of an element to search for.
     * @return Number of elements matching the key (either 1 or 0).
     */
    [[nodiscard]] size_type count(const key_type &key) const {
        return find(key) != end();
    }

    /**
     * @brief Returns the number of elements matching a key (either 1 or 0).
     * @tparam Other Type of the key value of an element to search for.
     * @param key Key value of an element to search for.
     * @return Number of elements matching the key (either 1 or 0).
     */
    template<typename Other>
    [[nodiscard]] std::enable_if_t<is_transparent_v<hasher> && is_transparent_v<key_equal>, std::conditional_t<false, Other, size_type>>
    count(const Other &key) const {
        return find(key) != end();
    }

    /**
     * @brief Finds an element with a given key.
     * @param key Key value of an element to search for.
     * @return An iterator to an element with the given key. If no such element
     * is found, a past-the-end iterator is returned.
     */
    [[nodiscard]] iterator find(const key_type &key) {
        return constrained_find(key, key_to_bucket(key));
    }

    /*! @copydoc find */
    [[nodiscard]] const_iterator find(const key_type &key) const {
        return constrained_find(key, key_to_bucket(key));
    }

    /**
     * @brief Finds an element with a key that compares _equivalent_ to a given
     * key.
     * @tparam Other Type of the key value of an element to search for.
     * @param key Key value of an element to search for.
     * @return An iterator to an element with the given key. If no such element
     * is found, a past-the-end iterator is returned.
     */
    template<typename Other>
    [[nodiscard]] std::enable_if_t<is_transparent_v<hasher> && is_transparent_v<key_equal>, std::conditional_t<false, Other, iterator>>
    find(const Other &key) {
        return constrained_find(key, key_to_bucket(key));
    }

    /*! @copydoc find */
    template<typename Other>
    [[nodiscard]] std::enable_if_t<is_transparent_v<hasher> && is_transparent_v<key_equal>, std::conditional_t<false, Other, const_iterator>>
    find(const Other &key) const {
        return constrained_find(key, key_to_bucket(key));
    }

    /**
     * @brief Returns a range containing all elements with a given key.
     * @param key Key value of an element to search for.
     * @return A pair of iterators pointing to the first element and past the
     * last element of the range.
     */
    [[nodiscard]] std::pair<iterator, iterator> equal_range(const key_type &key) {
        const auto it = find(key);
        return {it, it + !(it == end())};
    }

    /*! @copydoc equal_range */
    [[nodiscard]] std::pair<const_iterator, const_iterator> equal_range(const key_type &key) const {
        const auto it = find(key);
        return {it, it + !(it == cend())};
    }

    /**
     * @brief Returns a range containing all elements that compare _equivalent_
     * to a given key.
     * @tparam Other Type of an element to search for.
     * @param key Key value of an element to search for.
     * @return A pair of iterators pointing to the first element and past the
     * last element of the range.
     */
    template<typename Other>
    [[nodiscard]] std::enable_if_t<is_transparent_v<hasher> && is_transparent_v<key_equal>, std::conditional_t<false, Other, std::pair<iterator, iterator>>>
    equal_range(const Other &key) {
        const auto it = find(key);
        return {it, it + !(it == end())};
    }

    /*! @copydoc equal_range */
    template<typename Other>
    [[nodiscard]] std::enable_if_t<is_transparent_v<hasher> && is_transparent_v<key_equal>, std::conditional_t<false, Other, std::pair<const_iterator, const_iterator>>>
    equal_range(const Other &key) const {
        const auto it = find(key);
        return {it, it + !(it == cend())};
    }

    /**
     * @brief Checks if the container contains an element with a given key.
     * @param key Key value of an element to search for.
     * @return True if there is such an element, false otherwise.
     */
    [[nodiscard]] bool contains(const key_type &key) const {
        return (find(key) != cend());
    }

    /**
     * @brief Checks if the container contains an element with a key that
     * compares _equivalent_ to a given value.
     * @tparam Other Type of the key value of an element to search for.
     * @param key Key value of an element to search for.
     * @return True if there is such an element, false otherwise.
     */
    template<typename Other>
    [[nodiscard]] std::enable_if_t<is_transparent_v<hasher> && is_transparent_v<key_equal>, std::conditional_t<false, Other, bool>>
    contains(const Other &key) const {
        return (find(key) != cend());
    }

    /**
     * @brief Returns an iterator to the beginning of a given bucket.
     * @param index An index of a bucket to access.
     * @return An iterator to the beginning of the given bucket.
     */
    [[nodiscard]] const_local_iterator cbegin(const size_type index) const {
        return {packed.first().begin(), sparse.first()[index]};
    }

    /**
     * @brief Returns an iterator to the beginning of a given bucket.
     * @param index An index of a bucket to access.
     * @return An iterator to the beginning of the given bucket.
     */
    [[nodiscard]] const_local_iterator begin(const size_type index) const {
        return cbegin(index);
    }

    /**
     * @brief Returns an iterator to the beginning of a given bucket.
     * @param index An index of a bucket to access.
     * @return An iterator to the beginning of the given bucket.
     */
    [[nodiscard]] local_iterator begin(const size_type index) {
        return {packed.first().begin(), sparse.first()[index]};
    }

    /**
     * @brief Returns an iterator to the end of a given bucket.
     * @param index An index of a bucket to access.
     * @return An iterator to the end of the given bucket.
     */
    [[nodiscard]] const_local_iterator cend([[maybe_unused]] const size_type index) const {
        return {packed.first().begin(), (std::numeric_limits<size_type>::max)()};
    }

    /**
     * @brief Returns an iterator to the end of a given bucket.
     * @param index An index of a bucket to access.
     * @return An iterator to the end of the given bucket.
     */
    [[nodiscard]] const_local_iterator end(const size_type index) const {
        return cend(index);
    }

    /**
     * @brief Returns an iterator to the end of a given bucket.
     * @param index An index of a bucket to access.
     * @return An iterator to the end of the given bucket.
     */
    [[nodiscard]] local_iterator end([[maybe_unused]] const size_type index) {
        return {packed.first().begin(), (std::numeric_limits<size_type>::max)()};
    }

    /**
     * @brief Returns the number of buckets.
     * @return The number of buckets.
     */
    [[nodiscard]] size_type bucket_count() const {
        return sparse.first().size();
    }

    /**
     * @brief Returns the maximum number of buckets.
     * @return The maximum number of buckets.
     */
    [[nodiscard]] size_type max_bucket_count() const {
        return sparse.first().max_size();
    }

    /**
     * @brief Returns the number of elements in a given bucket.
     * @param index The index of the bucket to examine.
     * @return The number of elements in the given bucket.
     */
    [[nodiscard]] size_type bucket_size(const size_type index) const {
        return static_cast<size_type>(std::distance(begin(index), end(index)));
    }

    /**
     * @brief Returns the bucket for a given key.
     * @param key The value of the key to examine.
     * @return The bucket for the given key.
     */
    [[nodiscard]] size_type bucket(const key_type &key) const {
        return key_to_bucket(key);
    }

    /**
     * @brief Returns the average number of elements per bucket.
     * @return The average number of elements per bucket.
     */
    [[nodiscard]] float load_factor() const {
        return static_cast<float>(size()) / static_cast<float>(bucket_count());
    }

    /**
     * @brief Returns the maximum average number of elements per bucket.
     * @return The maximum average number of elements per bucket.
     */
    [[nodiscard]] float max_load_factor() const {
        return threshold;
    }

    /**
     * @brief Sets the desired maximum average number of elements per bucket.
     * @param value A desired maximum average number of elements per bucket.
     */
    void max_load_factor(const float value) {
        ASSERT(value > 0.f, "Invalid load factor");
        threshold = value;
        rehash(0u);
    }

    /**
     * @brief Reserves at least the specified number of buckets and regenerates
     * the hash table.
     * @param cnt New number of buckets.
     */
    void rehash(const size_type cnt) {
        auto value = cnt > minimum_capacity ? cnt : minimum_capacity;
        const auto cap = static_cast<size_type>(static_cast<float>(size()) / max_load_factor());
        value = value > cap ? value : cap;

        if(const auto sz = next_power_of_two(value); sz != bucket_count()) {
            sparse.first().resize(sz);

            for(auto &&elem: sparse.first()) {
                elem = (std::numeric_limits<size_type>::max)();
            }

            for(size_type pos{}, last = size(); pos < last; ++pos) {
                const auto index = key_to_bucket(packed.first()[pos].element.first);
                packed.first()[pos].next = std::exchange(sparse.first()[index], pos);
            }
        }
    }

    /**
     * @brief Reserves space for at least the specified number of elements and
     * regenerates the hash table.
     * @param cnt New number of elements.
     */
    void reserve(const size_type cnt) {
        packed.first().reserve(cnt);
        rehash(static_cast<size_type>(std::ceil(static_cast<float>(cnt) / max_load_factor())));
    }

    /**
     * @brief Returns the function used to hash the keys.
     * @return The function used to hash the keys.
     */
    [[nodiscard]] hasher hash_function() const {
        return sparse.second();
    }

    /**
     * @brief Returns the function used to compare keys for equality.
     * @return The function used to compare keys for equality.
     */
    [[nodiscard]] key_equal key_eq() const {
        return packed.second();
    }

private:
    compressed_pair<sparse_container_type, hasher> sparse;
    compressed_pair<packed_container_type, key_equal> packed;
    float threshold{default_threshold};
};



/*! @cond TURN_OFF_DOXYGEN */
namespace internal {

template<typename Ret, typename... Args>
constexpr auto function_pointer(Ret (*)(Args...)) -> Ret (*)(Args...);

template<typename Ret, typename Type, typename... Args, typename Other>
constexpr auto function_pointer(Ret (*)(Type, Args...), Other &&) -> Ret (*)(Args...);

template<typename Class, typename Ret, typename... Args, typename... Other>
constexpr auto function_pointer(Ret (Class::*)(Args...), Other &&...) -> Ret (*)(Args...);

template<typename Class, typename Ret, typename... Args, typename... Other>
constexpr auto function_pointer(Ret (Class::*)(Args...) const, Other &&...) -> Ret (*)(Args...);

template<typename Class, typename Type, typename... Other, typename = std::enable_if_t<std::is_member_object_pointer_v<Type Class::*>>>
constexpr auto function_pointer(Type Class::*, Other &&...) -> Type (*)();

template<typename... Type>
using function_pointer_t = decltype(function_pointer(std::declval<Type>()...));

template<typename... Class, typename Ret, typename... Args>
[[nodiscard]] constexpr auto index_sequence_for(Ret (*)(Args...)) {
    return std::index_sequence_for<Class..., Args...>{};
}

} // namespace internal
/*! @endcond */

/**
 * @brief Basic delegate implementation.
 *
 * Primary template isn't defined on purpose. All the specializations give a
 * compile-time error unless the template parameter is a function type.
 */
template<typename>
class delegate;

/**
 * @brief Utility class to use to send around functions and members.
 *
 * Unmanaged delegate for function pointers and members. Users of this class are
 * in charge of disconnecting instances before deleting them.
 *
 * A delegate can be used as a general purpose invoker without memory overhead
 * for free functions possibly with payloads and bound or unbound members.
 *
 * @tparam Ret Return type of a function type.
 * @tparam Args Types of arguments of a function type.
 */
template<typename Ret, typename... Args>
class delegate<Ret(Args...)> {
    using return_type = std::remove_const_t<Ret>;
    using delegate_type = return_type(const void *, Args...);

    template<auto Candidate, std::size_t... Index>
    [[nodiscard]] auto wrap(std::index_sequence<Index...>) noexcept {
        return [](const void *, Args... args) -> return_type {
            [[maybe_unused]] const auto arguments = std::forward_as_tuple(std::forward<Args>(args)...);
            [[maybe_unused]] constexpr auto offset = !std::is_invocable_r_v<Ret, decltype(Candidate), type_list_element_t<Index, type_list<Args...>>...> * (sizeof...(Args) - sizeof...(Index));
            return static_cast<Ret>(std::invoke(Candidate, std::forward<type_list_element_t<Index + offset, type_list<Args...>>>(std::get<Index + offset>(arguments))...));
        };
    }

    template<auto Candidate, typename Type, std::size_t... Index>
    [[nodiscard]] auto wrap(Type &, std::index_sequence<Index...>) noexcept {
        return [](const void *payload, Args... args) -> return_type {
            Type *curr = static_cast<Type *>(const_cast<constness_as_t<void, Type> *>(payload));
            [[maybe_unused]] const auto arguments = std::forward_as_tuple(std::forward<Args>(args)...);
            [[maybe_unused]] constexpr auto offset = !std::is_invocable_r_v<Ret, decltype(Candidate), Type &, type_list_element_t<Index, type_list<Args...>>...> * (sizeof...(Args) - sizeof...(Index));
            return static_cast<Ret>(std::invoke(Candidate, *curr, std::forward<type_list_element_t<Index + offset, type_list<Args...>>>(std::get<Index + offset>(arguments))...));
        };
    }

    template<auto Candidate, typename Type, std::size_t... Index>
    [[nodiscard]] auto wrap(Type *, std::index_sequence<Index...>) noexcept {
        return [](const void *payload, Args... args) -> return_type {
            Type *curr = static_cast<Type *>(const_cast<constness_as_t<void, Type> *>(payload));
            [[maybe_unused]] const auto arguments = std::forward_as_tuple(std::forward<Args>(args)...);
            [[maybe_unused]] constexpr auto offset = !std::is_invocable_r_v<Ret, decltype(Candidate), Type *, type_list_element_t<Index, type_list<Args...>>...> * (sizeof...(Args) - sizeof...(Index));
            return static_cast<Ret>(std::invoke(Candidate, curr, std::forward<type_list_element_t<Index + offset, type_list<Args...>>>(std::get<Index + offset>(arguments))...));
        };
    }

public:
    /*! @brief Function type of the contained target. */
    using function_type = Ret(const void *, Args...);
    /*! @brief Function type of the delegate. */
    using type = Ret(Args...);
    /*! @brief Return type of the delegate. */
    using result_type = Ret;

    /*! @brief Default constructor. */
    delegate() noexcept = default;

    /**
     * @brief Constructs a delegate with a given object or payload, if any.
     * @tparam Candidate Function or member to connect to the delegate.
     * @tparam Type Type of class or type of payload, if any.
     * @param value_or_instance Optional valid object that fits the purpose.
     */
    template<auto Candidate, typename... Type>
    delegate(connect_arg_t<Candidate>, Type &&...value_or_instance) noexcept {
        connect<Candidate>(std::forward<Type>(value_or_instance)...);
    }

    /**
     * @brief Constructs a delegate and connects an user defined function with
     * optional payload.
     * @param function Function to connect to the delegate.
     * @param payload User defined arbitrary data.
     */
    delegate(function_type *function, const void *payload = nullptr) noexcept {
        connect(function, payload);
    }

    /**
     * @brief Connects a free function or an unbound member to a delegate.
     * @tparam Candidate Function or member to connect to the delegate.
     */
    template<auto Candidate>
    void connect() noexcept {
        instance = nullptr;

        if constexpr(std::is_invocable_r_v<Ret, decltype(Candidate), Args...>) {
            fn = [](const void *, Args... args) -> return_type {
                return Ret(std::invoke(Candidate, std::forward<Args>(args)...));
            };
        } else if constexpr(std::is_member_pointer_v<decltype(Candidate)>) {
            fn = wrap<Candidate>(internal::index_sequence_for<type_list_element_t<0, type_list<Args...>>>(internal::function_pointer_t<decltype(Candidate)>{}));
        } else {
            fn = wrap<Candidate>(internal::index_sequence_for(internal::function_pointer_t<decltype(Candidate)>{}));
        }
    }

    /**
     * @brief Connects a free function with payload or a bound member to a
     * delegate.
     *
     * The delegate isn't responsible for the connected object or the payload.
     * Users must always guarantee that the lifetime of the instance overcomes
     * the one of the delegate.<br/>
     * When used to connect a free function with payload, its signature must be
     * such that the instance is the first argument before the ones used to
     * define the delegate itself.
     *
     * @tparam Candidate Function or member to connect to the delegate.
     * @tparam Type Type of class or type of payload.
     * @param value_or_instance A valid reference that fits the purpose.
     */
    template<auto Candidate, typename Type>
    void connect(Type &value_or_instance) noexcept {
        instance = &value_or_instance;

        if constexpr(std::is_invocable_r_v<Ret, decltype(Candidate), Type &, Args...>) {
            fn = [](const void *payload, Args... args) -> return_type {
                Type *curr = static_cast<Type *>(const_cast<constness_as_t<void, Type> *>(payload));
                return Ret(std::invoke(Candidate, *curr, std::forward<Args>(args)...));
            };
        } else {
            fn = wrap<Candidate>(value_or_instance, internal::index_sequence_for(internal::function_pointer_t<decltype(Candidate), Type>{}));
        }
    }

    /**
     * @brief Connects a free function with payload or a bound member to a
     * delegate.
     *
     * @sa connect(Type &)
     *
     * @tparam Candidate Function or member to connect to the delegate.
     * @tparam Type Type of class or type of payload.
     * @param value_or_instance A valid pointer that fits the purpose.
     */
    template<auto Candidate, typename Type>
    void connect(Type *value_or_instance) noexcept {
        instance = value_or_instance;

        if constexpr(std::is_invocable_r_v<Ret, decltype(Candidate), Type *, Args...>) {
            fn = [](const void *payload, Args... args) -> return_type {
                Type *curr = static_cast<Type *>(const_cast<constness_as_t<void, Type> *>(payload));
                return Ret(std::invoke(Candidate, curr, std::forward<Args>(args)...));
            };
        } else {
            fn = wrap<Candidate>(value_or_instance, internal::index_sequence_for(internal::function_pointer_t<decltype(Candidate), Type>{}));
        }
    }

    /**
     * @brief Connects an user defined function with optional payload to a
     * delegate.
     *
     * The delegate isn't responsible for the connected object or the payload.
     * Users must always guarantee that the lifetime of an instance overcomes
     * the one of the delegate.<br/>
     * The payload is returned as the first argument to the target function in
     * all cases.
     *
     * @param function Function to connect to the delegate.
     * @param payload User defined arbitrary data.
     */
    void connect(function_type *function, const void *payload = nullptr) noexcept {
        ASSERT(function != nullptr, "Uninitialized function pointer");
        instance = payload;
        fn = function;
    }

    /**
     * @brief Resets a delegate.
     *
     * After a reset, a delegate cannot be invoked anymore.
     */
    void reset() noexcept {
        instance = nullptr;
        fn = nullptr;
    }

    /**
     * @brief Returns a pointer to the stored callable function target, if any.
     * @return An opaque pointer to the stored callable function target.
     */
    [[nodiscard]] function_type *target() const noexcept {
        return fn;
    }

    /**
     * @brief Returns the instance or the payload linked to a delegate, if any.
     * @return An opaque pointer to the underlying data.
     */
    [[nodiscard]] const void *data() const noexcept {
        return instance;
    }

    /**
     * @brief Triggers a delegate.
     *
     * The delegate invokes the underlying function and returns the result.
     *
     * @warning
     * Attempting to trigger an invalid delegate results in undefined
     * behavior.
     *
     * @param args Arguments to use to invoke the underlying function.
     * @return The value returned by the underlying function.
     */
    Ret operator()(Args... args) const {
        ASSERT(static_cast<bool>(*this), "Uninitialized delegate");
        return fn(instance, std::forward<Args>(args)...);
    }

    /**
     * @brief Checks whether a delegate actually stores a listener.
     * @return False if the delegate is empty, true otherwise.
     */
    [[nodiscard]] explicit operator bool() const noexcept {
        // no need to also test instance
        return !(fn == nullptr);
    }

    /**
     * @brief Compares the contents of two delegates.
     * @param other Delegate with which to compare.
     * @return False if the two contents differ, true otherwise.
     */
    [[nodiscard]] bool operator==(const delegate<Ret(Args...)> &other) const noexcept {
        return fn == other.fn && instance == other.instance;
    }

private:
    const void *instance{};
    delegate_type *fn{};
};

/**
 * @brief Compares the contents of two delegates.
 * @tparam Ret Return type of a function type.
 * @tparam Args Types of arguments of a function type.
 * @param lhs A valid delegate object.
 * @param rhs A valid delegate object.
 * @return True if the two contents differ, false otherwise.
 */
template<typename Ret, typename... Args>
[[nodiscard]] bool operator!=(const delegate<Ret(Args...)> &lhs, const delegate<Ret(Args...)> &rhs) noexcept {
    return !(lhs == rhs);
}

/**
 * @brief Deduction guide.
 * @tparam Candidate Function or member to connect to the delegate.
 */
template<auto Candidate>
delegate(connect_arg_t<Candidate>) -> delegate<std::remove_pointer_t<internal::function_pointer_t<decltype(Candidate)>>>;

/**
 * @brief Deduction guide.
 * @tparam Candidate Function or member to connect to the delegate.
 * @tparam Type Type of class or type of payload.
 */
template<auto Candidate, typename Type>
delegate(connect_arg_t<Candidate>, Type &&) -> delegate<std::remove_pointer_t<internal::function_pointer_t<decltype(Candidate), Type>>>;

/**
 * @brief Deduction guide.
 * @tparam Ret Return type of a function type.
 * @tparam Args Types of arguments of a function type.
 */
template<typename Ret, typename... Args>
delegate(Ret (*)(const void *, Args...), const void * = nullptr) -> delegate<Ret(Args...)>;



/**
 * @brief Sink class.
 *
 * Primary template isn't defined on purpose. All the specializations give a
 * compile-time error unless the template parameter is a function type.
 *
 * @tparam Type A valid signal handler type.
 */
template<typename Type>
class sink;

/**
 * @brief Unmanaged signal handler.
 *
 * Primary template isn't defined on purpose. All the specializations give a
 * compile-time error unless the template parameter is a function type.
 *
 * @tparam Type A valid function type.
 * @tparam Allocator Type of allocator used to manage memory and elements.
 */
template<typename Type, typename Allocator>
class sigh;

/**
 * @brief Unmanaged signal handler.
 *
 * It works directly with references to classes and pointers to member functions
 * as well as pointers to free functions. Users of this class are in charge of
 * disconnecting instances before deleting them.
 *
 * This class serves mainly two purposes:
 *
 * * Creating signals to use later to notify a bunch of listeners.
 * * Collecting results from a set of functions like in a voting system.
 *
 * @tparam Ret Return type of a function type.
 * @tparam Args Types of arguments of a function type.
 * @tparam Allocator Type of allocator used to manage memory and elements.
 */
template<typename Ret, typename... Args, typename Allocator>
class sigh<Ret(Args...), Allocator> {
    friend class sink<sigh<Ret(Args...), Allocator>>;

    using alloc_traits = std::allocator_traits<Allocator>;
    using delegate_type = delegate<Ret(Args...)>;
    using container_type = std::vector<delegate_type, typename alloc_traits::template rebind_alloc<delegate_type>>;

public:
    /*! @brief Allocator type. */
    using allocator_type = Allocator;
    /*! @brief Unsigned integer type. */
    using size_type = std::size_t;
    /*! @brief Sink type. */
    using sink_type = sink<sigh<Ret(Args...), Allocator>>;

    /*! @brief Default constructor. */
    sigh() noexcept(noexcept(allocator_type{}))
        : sigh{allocator_type{}} {}

    /**
     * @brief Constructs a signal handler with a given allocator.
     * @param allocator The allocator to use.
     */
    explicit sigh(const allocator_type &allocator) noexcept
        : calls{allocator} {}

    /**
     * @brief Copy constructor.
     * @param other The instance to copy from.
     */
    sigh(const sigh &other)
        : calls{other.calls} {}

    /**
     * @brief Allocator-extended copy constructor.
     * @param other The instance to copy from.
     * @param allocator The allocator to use.
     */
    sigh(const sigh &other, const allocator_type &allocator)
        : calls{other.calls, allocator} {}

    /**
     * @brief Move constructor.
     * @param other The instance to move from.
     */
    sigh(sigh &&other) noexcept
        : calls{std::move(other.calls)} {}

    /**
     * @brief Allocator-extended move constructor.
     * @param other The instance to move from.
     * @param allocator The allocator to use.
     */
    sigh(sigh &&other, const allocator_type &allocator)
        : calls{std::move(other.calls), allocator} {}

    /*! @brief Default destructor. */
    ~sigh() = default;

    /**
     * @brief Copy assignment operator.
     * @param other The instance to copy from.
     * @return This signal handler.
     */
    sigh &operator=(const sigh &other) {
        calls = other.calls;
        return *this;
    }

    /**
     * @brief Move assignment operator.
     * @param other The instance to move from.
     * @return This signal handler.
     */
    sigh &operator=(sigh &&other) noexcept {
        swap(other);
        return *this;
    }

    /**
     * @brief Exchanges the contents with those of a given signal handler.
     * @param other Signal handler to exchange the content with.
     */
    void swap(sigh &other) noexcept {
        using std::swap;
        swap(calls, other.calls);
    }

    /**
     * @brief Returns the associated allocator.
     * @return The associated allocator.
     */
    [[nodiscard]] constexpr allocator_type get_allocator() const noexcept {
        return calls.get_allocator();
    }

    /**
     * @brief Number of listeners connected to the signal.
     * @return Number of listeners currently connected.
     */
    [[nodiscard]] size_type size() const noexcept {
        return calls.size();
    }

    /**
     * @brief Returns false if at least a listener is connected to the signal.
     * @return True if the signal has no listeners connected, false otherwise.
     */
    [[nodiscard]] bool empty() const noexcept {
        return calls.empty();
    }

    /**
     * @brief Triggers a signal.
     *
     * All the listeners are notified. Order isn't guaranteed.
     *
     * @param args Arguments to use to invoke listeners.
     */
    void publish(Args... args) const {
        for(auto pos = calls.size(); pos; --pos) {
            calls[pos - 1u](args...);
        }
    }

    /**
     * @brief Collects return values from the listeners.
     *
     * The collector must expose a call operator with the following properties:
     *
     * * The return type is either `void` or such that it's convertible to
     *   `bool`. In the second case, a true value will stop the iteration.
     * * The list of parameters is empty if `Ret` is `void`, otherwise it
     *   contains a single element such that `Ret` is convertible to it.
     *
     * @tparam Func Type of collector to use, if any.
     * @param func A valid function object.
     * @param args Arguments to use to invoke listeners.
     */
    template<typename Func>
    void collect(Func func, Args... args) const {
        for(auto pos = calls.size(); pos; --pos) {
            if constexpr(std::is_void_v<Ret> || !std::is_invocable_v<Func, Ret>) {
                calls[pos - 1u](args...);

                if constexpr(std::is_invocable_r_v<bool, Func>) {
                    if(func()) {
                        break;
                    }
                } else {
                    func();
                }
            } else {
                if constexpr(std::is_invocable_r_v<bool, Func, Ret>) {
                    if(func(calls[pos - 1u](args...))) {
                        break;
                    }
                } else {
                    func(calls[pos - 1u](args...));
                }
            }
        }
    }

private:
    container_type calls;
};

/**
 * @brief Connection class.
 *
 * Opaque object the aim of which is to allow users to release an already
 * estabilished connection without having to keep a reference to the signal or
 * the sink that generated it.
 */
class connection {
    template<typename>
    friend class sink;

    connection(delegate<void(void *)> fn, void *ref)
        : disconnect{fn}, signal{ref} {}

public:
    /*! @brief Default constructor. */
    connection()
        : signal{} {}

    /**
     * @brief Checks whether a connection is properly initialized.
     * @return True if the connection is properly initialized, false otherwise.
     */
    [[nodiscard]] explicit operator bool() const noexcept {
        return static_cast<bool>(disconnect);
    }

    /*! @brief Breaks the connection. */
    void release() {
        if(disconnect) {
            disconnect(signal);
            disconnect.reset();
        }
    }

private:
    delegate<void(void *)> disconnect;
    void *signal;
};

/**
 * @brief Scoped connection class.
 *
 * Opaque object the aim of which is to allow users to release an already
 * estabilished connection without having to keep a reference to the signal or
 * the sink that generated it.<br/>
 * A scoped connection automatically breaks the link between the two objects
 * when it goes out of scope.
 */
struct scoped_connection {
    /*! @brief Default constructor. */
    scoped_connection() = default;

    /**
     * @brief Constructs a scoped connection from a basic connection.
     * @param other A valid connection object.
     */
    scoped_connection(const connection &other)
        : conn{other} {}

    /*! @brief Default copy constructor, deleted on purpose. */
    scoped_connection(const scoped_connection &) = delete;

    /**
     * @brief Move constructor.
     * @param other The scoped connection to move from.
     */
    scoped_connection(scoped_connection &&other) noexcept
        : conn{std::exchange(other.conn, {})} {}

    /*! @brief Automatically breaks the link on destruction. */
    ~scoped_connection() {
        conn.release();
    }

    /**
     * @brief Default copy assignment operator, deleted on purpose.
     * @return This scoped connection.
     */
    scoped_connection &operator=(const scoped_connection &) = delete;

    /**
     * @brief Move assignment operator.
     * @param other The scoped connection to move from.
     * @return This scoped connection.
     */
    scoped_connection &operator=(scoped_connection &&other) noexcept {
        conn = std::exchange(other.conn, {});
        return *this;
    }

    /**
     * @brief Acquires a connection.
     * @param other The connection object to acquire.
     * @return This scoped connection.
     */
    scoped_connection &operator=(connection other) {
        conn = other;
        return *this;
    }

    /**
     * @brief Checks whether a scoped connection is properly initialized.
     * @return True if the connection is properly initialized, false otherwise.
     */
    [[nodiscard]] explicit operator bool() const noexcept {
        return static_cast<bool>(conn);
    }

    /*! @brief Breaks the connection. */
    void release() {
        conn.release();
    }

private:
    connection conn;
};

/**
 * @brief Sink class.
 *
 * A sink is used to connect listeners to signals and to disconnect them.<br/>
 * The function type for a listener is the one of the signal to which it
 * belongs.
 *
 * The clear separation between a signal and a sink permits to store the former
 * as private data member without exposing the publish functionality to the
 * users of the class.
 *
 * @warning
 * Lifetime of a sink must not overcome that of the signal to which it refers.
 * In any other case, attempting to use a sink results in undefined behavior.
 *
 * @tparam Ret Return type of a function type.
 * @tparam Args Types of arguments of a function type.
 * @tparam Allocator Type of allocator used to manage memory and elements.
 */
template<typename Ret, typename... Args, typename Allocator>
class sink<sigh<Ret(Args...), Allocator>> {
    using signal_type = sigh<Ret(Args...), Allocator>;
    using delegate_type = typename signal_type::delegate_type;
    using difference_type = typename signal_type::container_type::difference_type;

    template<auto Candidate, typename Type>
    static void release(Type value_or_instance, void *signal) {
        sink{*static_cast<signal_type *>(signal)}.disconnect<Candidate>(value_or_instance);
    }

    template<auto Candidate>
    static void release(void *signal) {
        sink{*static_cast<signal_type *>(signal)}.disconnect<Candidate>();
    }

    template<typename Func>
    void disconnect_if(Func callback) {
        auto &ref = signal_or_assert();

        for(auto pos = ref.calls.size(); pos; --pos) {
            if(auto &elem = ref.calls[pos - 1u]; callback(elem)) {
                elem = std::move(ref.calls.back());
                ref.calls.pop_back();
            }
        }
    }

    [[nodiscard]] auto &signal_or_assert() const noexcept {
        ASSERT(signal != nullptr, "Invalid pointer to signal");
        return *signal;
    }

public:
    /*! @brief Constructs an invalid sink. */
    sink() noexcept
        : signal{} {}

    /**
     * @brief Constructs a sink that is allowed to modify a given signal.
     * @param ref A valid reference to a signal object.
     */
    sink(sigh<Ret(Args...), Allocator> &ref) noexcept
        : signal{&ref} {}

    /**
     * @brief Returns false if at least a listener is connected to the sink.
     * @return True if the sink has no listeners connected, false otherwise.
     */
    [[nodiscard]] bool empty() const noexcept {
        return signal_or_assert().calls.empty();
    }

    /**
     * @brief Connects a free function or an unbound member to a signal.
     * @tparam Candidate Function or member to connect to the signal.
     * @return A properly initialized connection object.
     */
    template<auto Candidate>
    connection connect() {
        disconnect<Candidate>();

        delegate_type call{};
        call.template connect<Candidate>();
        signal_or_assert().calls.push_back(std::move(call));

        delegate<void(void *)> conn{};
        conn.template connect<&release<Candidate>>();
        return {conn, signal};
    }

    /**
     * @brief Connects a free function with payload or a bound member to a
     * signal.
     *
     * The signal isn't responsible for the connected object or the payload.
     * Users must always guarantee that the lifetime of the instance overcomes
     * the one of the signal.<br/>
     * When used to connect a free function with payload, its signature must be
     * such that the instance is the first argument before the ones used to
     * define the signal itself.
     *
     * @tparam Candidate Function or member to connect to the signal.
     * @tparam Type Type of class or type of payload.
     * @param value_or_instance A valid reference that fits the purpose.
     * @return A properly initialized connection object.
     */
    template<auto Candidate, typename Type>
    connection connect(Type &value_or_instance) {
        disconnect<Candidate>(value_or_instance);

        delegate_type call{};
        call.template connect<Candidate>(value_or_instance);
        signal_or_assert().calls.push_back(std::move(call));

        delegate<void(void *)> conn{};
        conn.template connect<&release<Candidate, Type &>>(value_or_instance);
        return {conn, signal};
    }

    /**
     * @brief Connects a free function with payload or a bound member to a
     * signal.
     *
     * @sa connect(Type &)
     *
     * @tparam Candidate Function or member to connect to the signal.
     * @tparam Type Type of class or type of payload.
     * @param value_or_instance A valid pointer that fits the purpose.
     * @return A properly initialized connection object.
     */
    template<auto Candidate, typename Type>
    connection connect(Type *value_or_instance) {
        disconnect<Candidate>(value_or_instance);

        delegate_type call{};
        call.template connect<Candidate>(value_or_instance);
        signal_or_assert().calls.push_back(std::move(call));

        delegate<void(void *)> conn{};
        conn.template connect<&release<Candidate, Type *>>(value_or_instance);
        return {conn, signal};
    }

    /**
     * @brief Disconnects a free function or an unbound member from a signal.
     * @tparam Candidate Function or member to disconnect from the signal.
     */
    template<auto Candidate>
    void disconnect() {
        delegate_type call{};
        call.template connect<Candidate>();
        disconnect_if([&call](const auto &elem) { return elem == call; });
    }

    /**
     * @brief Disconnects a free function with payload or a bound member from a
     * signal.
     *
     * The signal isn't responsible for the connected object or the payload.
     * Users must always guarantee that the lifetime of the instance overcomes
     * the one of the signal.<br/>
     * When used to connect a free function with payload, its signature must be
     * such that the instance is the first argument before the ones used to
     * define the signal itself.
     *
     * @tparam Candidate Function or member to disconnect from the signal.
     * @tparam Type Type of class or type of payload, if any.
     * @param value_or_instance A valid reference that fits the purpose.
     */
    template<auto Candidate, typename Type>
    void disconnect(Type &value_or_instance) {
        delegate_type call{};
        call.template connect<Candidate>(value_or_instance);
        disconnect_if([&call](const auto &elem) { return elem == call; });
    }

    /**
     * @brief Disconnects a free function with payload or a bound member from a
     * signal.
     *
     * @sa disconnect(Type &)
     *
     * @tparam Candidate Function or member to disconnect from the signal.
     * @tparam Type Type of class or type of payload, if any.
     * @param value_or_instance A valid pointer that fits the purpose.
     */
    template<auto Candidate, typename Type>
    void disconnect(Type *value_or_instance) {
        delegate_type call{};
        call.template connect<Candidate>(value_or_instance);
        disconnect_if([&call](const auto &elem) { return elem == call; });
    }

    /**
     * @brief Disconnects free functions with payload or bound members from a
     * signal.
     * @param value_or_instance A valid object that fits the purpose.
     */
    void disconnect(const void *value_or_instance) {
        ASSERT(value_or_instance != nullptr, "Invalid value or instance");
        disconnect_if([value_or_instance](const auto &elem) { return elem.data() == value_or_instance; });
    }

    /*! @brief Disconnects all the listeners from a signal. */
    void disconnect() {
        signal_or_assert().calls.clear();
    }

    /**
     * @brief Returns true if a sink is correctly initialized, false otherwise.
     * @return True if a sink is correctly initialized, false otherwise.
     */
    [[nodiscard]] explicit operator bool() const noexcept {
        return signal != nullptr;
    }

private:
    signal_type *signal;
};

/**
 * @brief Deduction guide.
 *
 * It allows to deduce the signal handler type of a sink directly from the
 * signal it refers to.
 *
 * @tparam Ret Return type of a function type.
 * @tparam Args Types of arguments of a function type.
 * @tparam Allocator Type of allocator used to manage memory and elements.
 */
template<typename Ret, typename... Args, typename Allocator>
sink(sigh<Ret(Args...), Allocator> &) -> sink<sigh<Ret(Args...), Allocator>>;



/**
 * @brief General purpose event emitter.
 *
 * To create an emitter type, derived classes must inherit from the base as:
 *
 * @code{.cpp}
 * struct my_emitter: emitter<my_emitter> {
 *     // ...
 * }
 * @endcode
 *
 * Handlers for the different events are created internally on the fly. It's not
 * required to specify in advance the full list of accepted events.<br/>
 * Moreover, whenever an event is published, an emitter also passes a reference
 * to itself to its listeners.
 *
 * @tparam Derived Emitter type.
 * @tparam Allocator Type of allocator used to manage memory and elements.
 */
template<typename Derived, typename Allocator>
class emitter {
    using key_type = id_type;
    using mapped_type = std::function<void(void *)>;

    using alloc_traits = std::allocator_traits<Allocator>;
    using container_allocator = typename alloc_traits::template rebind_alloc<std::pair<const key_type, mapped_type>>;
    using container_type = dense_map<key_type, mapped_type, identity, std::equal_to<>, container_allocator>;

public:
    /*! @brief Allocator type. */
    using allocator_type = Allocator;
    /*! @brief Unsigned integer type. */
    using size_type = std::size_t;

    /*! @brief Default constructor. */
    emitter()
        : emitter{allocator_type{}} {}

    /**
     * @brief Constructs an emitter with a given allocator.
     * @param allocator The allocator to use.
     */
    explicit emitter(const allocator_type &allocator)
        : handlers{allocator, allocator} {}

    /*! @brief Default copy constructor, deleted on purpose. */
    emitter(const emitter &) = delete;

    /**
     * @brief Move constructor.
     * @param other The instance to move from.
     */
    emitter(emitter &&other) noexcept
        : handlers{std::move(other.handlers)} {}

    /**
     * @brief Allocator-extended move constructor.
     * @param other The instance to move from.
     * @param allocator The allocator to use.
     */
    emitter(emitter &&other, const allocator_type &allocator)
        : handlers{container_type{std::move(other.handlers.first()), allocator}, allocator} {
        ASSERT(alloc_traits::is_always_equal::value || handlers.second() == other.handlers.second(), "Copying an emitter is not allowed");
    }

    /*! @brief Default destructor. */
    virtual ~emitter() {
        static_assert(std::is_base_of_v<emitter<Derived, Allocator>, Derived>, "Invalid emitter type");
    }

    /**
     * @brief Default copy assignment operator, deleted on purpose.
     * @return This emitter.
     */
    emitter &operator=(const emitter &) = delete;

    /**
     * @brief Move assignment operator.
     * @param other The instance to move from.
     * @return This emitter.
     */
    emitter &operator=(emitter &&other) noexcept {
        ASSERT(alloc_traits::is_always_equal::value || handlers.second() == other.handlers.second(), "Copying an emitter is not allowed");
        swap(other);
        return *this;
    }

    /**
     * @brief Exchanges the contents with those of a given emitter.
     * @param other Emitter to exchange the content with.
     */
    void swap(emitter &other) noexcept {
        using std::swap;
        swap(handlers, other.handlers);
    }

    /**
     * @brief Returns the associated allocator.
     * @return The associated allocator.
     */
    [[nodiscard]] constexpr allocator_type get_allocator() const noexcept {
        return handlers.second();
    }

    /**
     * @brief Publishes a given event.
     * @tparam Type Type of event to trigger.
     * @param value An instance of the given type of event.
     */
    template<typename Type>
    void publish(Type value) {
        if(const auto id = type_id<Type>().hash(); handlers.first().contains(id)) {
            handlers.first()[id](&value);
        }
    }

    /**
     * @brief Registers a listener with the event emitter.
     * @tparam Type Type of event to which to connect the listener.
     * @param func The listener to register.
     */
    template<typename Type>
    void on(std::function<void(Type &, Derived &)> func) {
        handlers.first().insert_or_assign(type_id<Type>().hash(), [func = std::move(func), this](void *value) {
            func(*static_cast<Type *>(value), static_cast<Derived &>(*this));
        });
    }

    /**
     * @brief Disconnects a listener from the event emitter.
     * @tparam Type Type of event of the listener.
     */
    template<typename Type>
    void erase() {
        handlers.first().erase(type_hash<std::remove_cv_t<std::remove_reference_t<Type>>>::value());
    }

    /*! @brief Disconnects all the listeners. */
    void clear() noexcept {
        handlers.first().clear();
    }

    /**
     * @brief Checks if there are listeners registered for the specific event.
     * @tparam Type Type of event to test.
     * @return True if there are no listeners registered, false otherwise.
     */
    template<typename Type>
    [[nodiscard]] bool contains() const {
        return handlers.first().contains(type_hash<std::remove_cv_t<std::remove_reference_t<Type>>>::value());
    }

    /**
     * @brief Checks if there are listeners registered with the event emitter.
     * @return True if there are no listeners registered, false otherwise.
     */
    [[nodiscard]] bool empty() const noexcept {
        return handlers.first().empty();
    }

private:
    compressed_pair<container_type, allocator_type> handlers;
};



/*! @cond TURN_OFF_DOXYGEN */
namespace internal {

struct basic_dispatcher_handler {
    virtual ~basic_dispatcher_handler() = default;
    virtual void publish() = 0;
    virtual void disconnect(void *) = 0;
    virtual void clear() noexcept = 0;
    [[nodiscard]] virtual std::size_t size() const noexcept = 0;
};

template<typename Type, typename Allocator>
class dispatcher_handler final: public basic_dispatcher_handler {
    static_assert(std::is_same_v<Type, std::decay_t<Type>>, "Invalid type");

    using alloc_traits = std::allocator_traits<Allocator>;
    using signal_type = sigh<void(Type &), Allocator>;
    using container_type = std::vector<Type, typename alloc_traits::template rebind_alloc<Type>>;

public:
    using allocator_type = Allocator;

    dispatcher_handler(const allocator_type &allocator)
        : signal{allocator},
        events{allocator} {}

    void publish() override {
        const auto length = events.size();

        for(std::size_t pos{}; pos < length; ++pos) {
            signal.publish(events[pos]);
        }

        events.erase(events.cbegin(), events.cbegin() + static_cast<typename container_type::difference_type>(length));
    }

    void disconnect(void *instance) override {
        bucket().disconnect(instance);
    }

    void clear() noexcept override {
        events.clear();
    }

    [[nodiscard]] auto bucket() noexcept {
        return typename signal_type::sink_type{signal};
    }

    void trigger(Type event) {
        signal.publish(event);
    }

    template<typename... Args>
    void enqueue(Args &&...args) {
        if constexpr(std::is_aggregate_v<Type> && (sizeof...(Args) != 0u || !std::is_default_constructible_v<Type>)) {
            events.push_back(Type{std::forward<Args>(args)...});
        } else {
            events.emplace_back(std::forward<Args>(args)...);
        }
    }

    [[nodiscard]] std::size_t size() const noexcept override {
        return events.size();
    }

private:
    signal_type signal;
    container_type events;
};

} // namespace internal
/*! @endcond */

/**
 * @brief Basic dispatcher implementation.
 *
 * A dispatcher can be used either to trigger an immediate event or to enqueue
 * events to be published all together once per tick.<br/>
 * Listeners are provided in the form of member functions. For each event of
 * type `Type`, listeners are such that they can be invoked with an argument of
 * type `Type &`, no matter what the return type is.
 *
 * The dispatcher creates instances of the `sigh` class internally. Refer to the
 * documentation of the latter for more details.
 *
 * @tparam Allocator Type of allocator used to manage memory and elements.
 */
template<typename Allocator>
class basic_dispatcher {
    template<typename Type>
    using handler_type = internal::dispatcher_handler<Type, Allocator>;

    using key_type = id_type;
    // std::shared_ptr because of its type erased allocator which is useful here
    using mapped_type = std::shared_ptr<internal::basic_dispatcher_handler>;

    using alloc_traits = std::allocator_traits<Allocator>;
    using container_allocator = typename alloc_traits::template rebind_alloc<std::pair<const key_type, mapped_type>>;
    using container_type = dense_map<key_type, mapped_type, identity, std::equal_to<>, container_allocator>;

    template<typename Type>
    [[nodiscard]] handler_type<Type> &assure(const id_type id) {
        static_assert(std::is_same_v<Type, std::decay_t<Type>>, "Non-decayed types not allowed");
        auto &&ptr = pools.first()[id];

        if(!ptr) {
            const auto &allocator = get_allocator();
            ptr = std::allocate_shared<handler_type<Type>>(allocator, allocator);
        }

        return static_cast<handler_type<Type> &>(*ptr);
    }

    template<typename Type>
    [[nodiscard]] const handler_type<Type> *assure(const id_type id) const {
        static_assert(std::is_same_v<Type, std::decay_t<Type>>, "Non-decayed types not allowed");

        if(auto it = pools.first().find(id); it != pools.first().cend()) {
            return static_cast<const handler_type<Type> *>(it->second.get());
        }

        return nullptr;
    }

public:
    /*! @brief Allocator type. */
    using allocator_type = Allocator;
    /*! @brief Unsigned integer type. */
    using size_type = std::size_t;

    /*! @brief Default constructor. */
    basic_dispatcher()
        : basic_dispatcher{allocator_type{}} {}

    /**
     * @brief Constructs a dispatcher with a given allocator.
     * @param allocator The allocator to use.
     */
    explicit basic_dispatcher(const allocator_type &allocator)
        : pools{allocator, allocator} {}

    /*! @brief Default copy constructor, deleted on purpose. */
    basic_dispatcher(const basic_dispatcher &) = delete;

    /**
     * @brief Move constructor.
     * @param other The instance to move from.
     */
    basic_dispatcher(basic_dispatcher &&other) noexcept
        : pools{std::move(other.pools)} {}

    /**
     * @brief Allocator-extended move constructor.
     * @param other The instance to move from.
     * @param allocator The allocator to use.
     */
    basic_dispatcher(basic_dispatcher &&other, const allocator_type &allocator)
        : pools{container_type{std::move(other.pools.first()), allocator}, allocator} {
        ASSERT(alloc_traits::is_always_equal::value || get_allocator() == other.get_allocator(), "Copying a dispatcher is not allowed");
    }

    /*! @brief Default destructor. */
    ~basic_dispatcher() = default;

    /**
     * @brief Default copy assignment operator, deleted on purpose.
     * @return This dispatcher.
     */
    basic_dispatcher &operator=(const basic_dispatcher &) = delete;

    /**
     * @brief Move assignment operator.
     * @param other The instance to move from.
     * @return This dispatcher.
     */
    basic_dispatcher &operator=(basic_dispatcher &&other) noexcept {
        ASSERT(alloc_traits::is_always_equal::value || get_allocator() == other.get_allocator(), "Copying a dispatcher is not allowed");
        swap(other);
        return *this;
    }

    /**
     * @brief Exchanges the contents with those of a given dispatcher.
     * @param other Dispatcher to exchange the content with.
     */
    void swap(basic_dispatcher &other) noexcept {
        using std::swap;
        swap(pools, other.pools);
    }

    /**
     * @brief Returns the associated allocator.
     * @return The associated allocator.
     */
    [[nodiscard]] constexpr allocator_type get_allocator() const noexcept {
        return pools.second();
    }

    /**
     * @brief Returns the number of pending events for a given type.
     * @tparam Type Type of event for which to return the count.
     * @param id Name used to map the event queue within the dispatcher.
     * @return The number of pending events for the given type.
     */
    template<typename Type>
    [[nodiscard]] size_type size(const id_type id = type_hash<Type>::value()) const noexcept {
        const auto *cpool = assure<std::decay_t<Type>>(id);
        return cpool ? cpool->size() : 0u;
    }

    /**
     * @brief Returns the total number of pending events.
     * @return The total number of pending events.
     */
    [[nodiscard]] size_type size() const noexcept {
        size_type count{};

        for(auto &&cpool: pools.first()) {
            count += cpool.second->size();
        }

        return count;
    }

    /**
     * @brief Returns a sink object for the given event and queue.
     *
     * A sink is an opaque object used to connect listeners to events.
     *
     * The function type for a listener is _compatible_ with:
     *
     * @code{.cpp}
     * void(Type &);
     * @endcode
     *
     * The order of invocation of the listeners isn't guaranteed.
     *
     * @sa sink
     *
     * @tparam Type Type of event of which to get the sink.
     * @param id Name used to map the event queue within the dispatcher.
     * @return A temporary sink object.
     */
    template<typename Type>
    [[nodiscard]] auto sink(const id_type id = type_hash<Type>::value()) {
        return assure<Type>(id).bucket();
    }

    /**
     * @brief Triggers an immediate event of a given type.
     * @tparam Type Type of event to trigger.
     * @param value An instance of the given type of event.
     */
    template<typename Type>
    void trigger(Type &&value = {}) {
        trigger(type_hash<std::decay_t<Type>>::value(), std::forward<Type>(value));
    }

    /**
     * @brief Triggers an immediate event on a queue of a given type.
     * @tparam Type Type of event to trigger.
     * @param value An instance of the given type of event.
     * @param id Name used to map the event queue within the dispatcher.
     */
    template<typename Type>
    void trigger(const id_type id, Type &&value = {}) {
        assure<std::decay_t<Type>>(id).trigger(std::forward<Type>(value));
    }

    /**
     * @brief Enqueues an event of the given type.
     * @tparam Type Type of event to enqueue.
     * @tparam Args Types of arguments to use to construct the event.
     * @param args Arguments to use to construct the event.
     */
    template<typename Type, typename... Args>
        requires requires { Type{std::declval<Args>()...}; }
    void enqueue(Args &&...args) {
        enqueue_hint<Type>(type_hash<Type>::value(), std::forward<Args>(args)...);
    }

    /**
     * @brief Enqueues an event of the given type.
     * @tparam Type Type of event to enqueue.
     * @param value An instance of the given type of event.
     */
    template<typename Type>
    void enqueue(Type &&value) {
        enqueue_hint(type_hash<std::decay_t<Type>>::value(), std::forward<Type>(value));
    }

    /**
     * @brief Enqueues an event of the given type.
     * @tparam Type Type of event to enqueue.
     * @tparam Args Types of arguments to use to construct the event.
     * @param id Name used to map the event queue within the dispatcher.
     * @param args Arguments to use to construct the event.
     */
    template<typename Type, typename... Args>
    void enqueue_hint(const id_type id, Args &&...args) {
        assure<Type>(id).enqueue(std::forward<Args>(args)...);
    }

    /**
     * @brief Enqueues an event of the given type.
     * @tparam Type Type of event to enqueue.
     * @param id Name used to map the event queue within the dispatcher.
     * @param value An instance of the given type of event.
     */
    template<typename Type>
    void enqueue_hint(const id_type id, Type &&value) {
        assure<std::decay_t<Type>>(id).enqueue(std::forward<Type>(value));
    }

    /**
     * @brief Utility function to disconnect everything related to a given value
     * or instance from a dispatcher.
     * @tparam Type Type of class or type of payload.
     * @param value_or_instance A valid object that fits the purpose.
     */
    template<typename Type>
    void disconnect(Type &value_or_instance) {
        disconnect(&value_or_instance);
    }

    /**
     * @brief Utility function to disconnect everything related to a given value
     * or instance from a dispatcher.
     * @tparam Type Type of class or type of payload.
     * @param value_or_instance A valid object that fits the purpose.
     */
    template<typename Type>
    void disconnect(Type *value_or_instance) {
        for(auto &&cpool: pools.first()) {
            cpool.second->disconnect(value_or_instance);
        }
    }

    /**
     * @brief Discards all the events stored so far in a given queue.
     * @tparam Type Type of event to discard.
     * @param id Name used to map the event queue within the dispatcher.
     */
    template<typename Type>
    void clear(const id_type id = type_hash<Type>::value()) {
        assure<Type>(id).clear();
    }

    /*! @brief Discards all the events queued so far. */
    void clear() noexcept {
        for(auto &&cpool: pools.first()) {
            cpool.second->clear();
        }
    }

    /**
     * @brief Delivers all the pending events of a given queue.
     * @tparam Type Type of event to send.
     * @param id Name used to map the event queue within the dispatcher.
     */
    template<typename Type>
    void update(const id_type id = type_hash<Type>::value()) {
        assure<Type>(id).publish();
    }

    /*! @brief Delivers all the pending events. */
    void update() const {
        for(auto &&cpool: pools.first()) {
            cpool.second->publish();
        }
    }

private:
    compressed_pair<container_type, allocator_type> pools;
};

} // namespace event
