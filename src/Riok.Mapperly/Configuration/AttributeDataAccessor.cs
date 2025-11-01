using System.ComponentModel;
using System.Diagnostics.CodeAnalysis;
using System.Reflection;
using System.Runtime.Serialization;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Microsoft.CodeAnalysis.Operations;
using Riok.Mapperly.Abstractions;
using Riok.Mapperly.Configuration.MethodReferences;
using Riok.Mapperly.Configuration.PropertyReferences;
using Riok.Mapperly.Descriptors;
using Riok.Mapperly.Helpers;

namespace Riok.Mapperly.Configuration;

/// <summary>
/// Creates <see cref="Attribute"/> instances by resolving attribute data from provided symbols.
/// </summary>
public class AttributeDataAccessor(SymbolAccessor symbolAccessor)
{
    private const char FullNameOfPrefix = '@';
    private readonly Dictionary<CacheKey, object?> _cache = new();

    public static MapperConfiguration ReadMapperDefaultsAttribute(AttributeData attrData)
    {
        return Access<MapperDefaultsAttribute, MapperConfiguration>(attrData);
    }

    public FormatProviderAttribute ReadFormatProviderAttribute(ISymbol symbol)
    {
        return GetOrCreateRequiredAttribute<FormatProviderAttribute, FormatProviderAttribute>(
            symbol,
            static (a, data) => a.Access<FormatProviderAttribute, FormatProviderAttribute>(data)
        );
    }

    public MapperConfiguration ReadMapperAttribute(ISymbol symbol)
    {
        return GetOrCreateRequiredAttribute<MapperAttribute, MapperConfiguration>(
            symbol,
            static (a, data) => a.Access<MapperAttribute, MapperConfiguration>(data)
        );
    }

    public MapperIgnoreObsoleteMembersAttribute? ReadMapperIgnoreObsoleteMembersAttribute(ISymbol symbol)
    {
        return GetOrCreateAttribute<MapperIgnoreObsoleteMembersAttribute, MapperIgnoreObsoleteMembersAttribute>(
            symbol,
            static (a, data) => a.Access<MapperIgnoreObsoleteMembersAttribute, MapperIgnoreObsoleteMembersAttribute>(data)
        );
    }

    public IReadOnlyList<NestedMembersMappingConfiguration> ReadMapNestedPropertiesAttribute(ISymbol symbol)
    {
        return GetOrCreateAttributes<MapNestedPropertiesAttribute, NestedMembersMappingConfiguration>(
            symbol,
            static (a, data) => a.Access<MapNestedPropertiesAttribute, NestedMembersMappingConfiguration>(data)
        );
    }

    public MapperRequiredMappingAttribute? ReadMapperRequiredMappingAttribute(ISymbol symbol)
    {
        return GetOrCreateAttribute<MapperRequiredMappingAttribute, MapperRequiredMappingAttribute>(
            symbol,
            static (a, data) => a.Access<MapperRequiredMappingAttribute, MapperRequiredMappingAttribute>(data)
        );
    }

    public EnumMemberAttribute? ReadEnumMemberAttribute(ISymbol symbol)
    {
        return GetOrCreateAttribute<EnumMemberAttribute, EnumMemberAttribute>(
            symbol,
            static (a, data) => a.Access<EnumMemberAttribute, EnumMemberAttribute>(data)
        );
    }

    public EnumConfiguration? ReadMapEnumAttribute(ISymbol symbol)
    {
        return GetOrCreateAttribute<MapEnumAttribute, EnumConfiguration>(
            symbol,
            static (a, data) => a.Access<MapEnumAttribute, EnumConfiguration>(data)
        );
    }

    public IReadOnlyList<EnumValueMappingConfiguration> ReadMapEnumValueAttribute(ISymbol symbol)
    {
        return GetOrCreateAttributes<MapEnumValueAttribute, EnumValueMappingConfiguration>(
            symbol,
            static (a, data) => a.Access<MapEnumValueAttribute, EnumValueMappingConfiguration>(data)
        );
    }

    public IReadOnlyList<MapperIgnoreEnumValueConfiguration> ReadMapperIgnoreSourceValueAttribute(ISymbol symbol)
    {
        return GetOrCreateAttributes<MapperIgnoreSourceValueAttribute, MapperIgnoreEnumValueConfiguration>(
            symbol,
            static (a, data) => a.Access<MapperIgnoreSourceValueAttribute, MapperIgnoreEnumValueConfiguration>(data)
        );
    }

    public IReadOnlyList<MapperIgnoreEnumValueConfiguration> ReadMapperIgnoreTargetValueAttribute(ISymbol symbol)
    {
        return GetOrCreateAttributes<MapperIgnoreTargetValueAttribute, MapperIgnoreEnumValueConfiguration>(
            symbol,
            static (a, data) => a.Access<MapperIgnoreTargetValueAttribute, MapperIgnoreEnumValueConfiguration>(data)
        );
    }

    public ComponentModelDescriptionAttributeConfiguration? ReadDescriptionAttribute(ISymbol symbol)
    {
        return GetOrCreateAttribute<DescriptionAttribute, ComponentModelDescriptionAttributeConfiguration>(
            symbol,
            static (a, data) => a.Access<DescriptionAttribute, ComponentModelDescriptionAttributeConfiguration>(data)
        );
    }

    public UserMappingConfiguration? ReadUserMappingAttribute(ISymbol symbol)
    {
        return GetOrCreateAttribute<UserMappingAttribute, UserMappingConfiguration>(
            symbol,
            static (a, data) => a.Access<UserMappingAttribute, UserMappingConfiguration>(data)
        );
    }

    public bool HasUseMapperAttribute(ISymbol symbol)
    {
        return symbolAccessor.GetAttributes<UseMapperAttribute>(symbol).Any();
    }

    public IReadOnlyList<MapperIgnoreSourceAttribute> ReadMapperIgnoreSourceAttributes(ISymbol symbol)
    {
        return GetOrCreateAttributes<MapperIgnoreSourceAttribute, MapperIgnoreSourceAttribute>(
            symbol,
            static (a, data) => a.Access<MapperIgnoreSourceAttribute, MapperIgnoreSourceAttribute>(data)
        );
    }

    public IReadOnlyList<MapperIgnoreTargetAttribute> ReadMapperIgnoreTargetAttributes(ISymbol symbol)
    {
        return GetOrCreateAttributes<MapperIgnoreTargetAttribute, MapperIgnoreTargetAttribute>(
            symbol,
            static (a, data) => a.Access<MapperIgnoreTargetAttribute, MapperIgnoreTargetAttribute>(data)
        );
    }

    public IReadOnlyList<MemberValueMappingConfiguration> ReadMapValueAttribute(ISymbol symbol)
    {
        return GetOrCreateAttributes<MapValueAttribute, MemberValueMappingConfiguration>(
            symbol,
            static (a, data) => a.Access<MapValueAttribute, MemberValueMappingConfiguration>(data)
        );
    }

    public IReadOnlyList<MemberMappingConfiguration> ReadMapPropertyAttributes(ISymbol symbol)
    {
        return GetOrCreateAttributes<MapPropertyAttribute, MemberMappingConfiguration>(
            symbol,
            static (a, data) => a.Access<MapPropertyAttribute, MemberMappingConfiguration>(data)
        );
    }

    public IReadOnlyList<IncludeMappingConfiguration> ReadIncludeMappingConfigurationAttributes(ISymbol symbol)
    {
        return GetOrCreateAttributes<IncludeMappingConfigurationAttribute, IncludeMappingConfiguration>(
            symbol,
            static (a, data) => a.Access<IncludeMappingConfigurationAttribute, IncludeMappingConfiguration>(data)
        );
    }

    public IReadOnlyList<DerivedTypeMappingConfiguration> ReadMapDerivedTypeAttributes(ISymbol symbol)
    {
        return GetOrCreateAttributes<MapDerivedTypeAttribute, DerivedTypeMappingConfiguration>(
            symbol,
            static (a, data) => a.Access<MapDerivedTypeAttribute, DerivedTypeMappingConfiguration>(data)
        );
    }

    public IReadOnlyList<DerivedTypeMappingConfiguration> ReadGenericMapDerivedTypeAttributes(ISymbol symbol)
    {
        return GetOrCreateAttributes<MapDerivedTypeAttribute<object, object>, DerivedTypeMappingConfiguration>(
            symbol,
            static (a, data) => a.Access<MapDerivedTypeAttribute<object, object>, DerivedTypeMappingConfiguration>(data)
        );
    }

    public IReadOnlyList<MemberMappingConfiguration> ReadMapPropertyFromSourceAttributes(ISymbol symbol)
    {
        return GetOrCreateAttributes<MapPropertyFromSourceAttribute, MemberMappingConfiguration>(
            symbol,
            static (a, data) => a.Access<MapPropertyFromSourceAttribute, MemberMappingConfiguration>(data)
        );
    }

    public IReadOnlyList<UseStaticMapperConfiguration> ReadUseStaticMapperAttributes(ISymbol symbol)
    {
        return GetOrCreateAttributes<UseStaticMapperAttribute, UseStaticMapperConfiguration>(
            symbol,
            static (a, data) => a.Access<UseStaticMapperAttribute, UseStaticMapperConfiguration>(data)
        );
    }

    public IReadOnlyList<UseStaticMapperConfiguration> ReadGenericUseStaticMapperAttributes(ISymbol symbol)
    {
        return GetOrCreateAttributes<UseStaticMapperAttribute<object>, UseStaticMapperConfiguration>(
            symbol,
            static (a, data) => a.Access<UseStaticMapperAttribute<object>, UseStaticMapperConfiguration>(data)
        );
    }

    public string GetMappingName(IMethodSymbol methodSymbol)
    {
        return GetOrCreateAttribute<NamedMappingAttribute, NamedMappingAttribute>(
                methodSymbol,
                static (a, data) => a.Access<NamedMappingAttribute, NamedMappingAttribute>(data)
            )?.Name ?? methodSymbol.Name;
    }

    public bool IsMappingNameEqualTo(IMethodSymbol methodSymbol, string name)
    {
        return string.Equals(GetMappingName(methodSymbol), name, StringComparison.Ordinal);
    }

    internal IEnumerable<NotNullIfNotNullAttribute> TryReadNotNullIfNotNullAttributes(IMethodSymbol symbol)
    {
        return TryAccess<NotNullIfNotNullAttribute, NotNullIfNotNullAttribute>(symbol.GetReturnTypeAttributes());
    }

    private IEnumerable<TData> TryAccess<TAttribute, TData>(IEnumerable<AttributeData> attributes)
        where TAttribute : Attribute
        where TData : notnull
    {
        var attrDatas = symbolAccessor.TryGetAttributes<TAttribute>(attributes);
        return attrDatas.Select(static a => Access<TAttribute, TData>(a, null));
    }

    private IReadOnlyList<TData> GetOrCreateAttributes<TAttribute, TData>(
        ISymbol symbol,
        Func<AttributeDataAccessor, AttributeData, TData?> createAttribute
    )
        where TAttribute : Attribute
    {
        var key = new CacheKey(typeof(TAttribute), symbol);
        if (_cache.TryGetValue(key, out var cachedAttribute))
        {
            return (IReadOnlyList<TData>)(cachedAttribute ?? Enumerable.Empty<TData>());
        }

        var collector = new List<TData>();

        foreach (var attrData in symbolAccessor.GetAttributes<TAttribute>(symbol))
        {
            var data = createAttribute(this, attrData);
            if (data is not null)
            {
                collector.Add(data);
            }
        }

        _cache.Add(key, collector.AsReadOnly());
        return collector;
    }

    private TData GetOrCreateRequiredAttribute<TAttribute, TData>(
        ISymbol symbol,
        Func<AttributeDataAccessor, AttributeData, TData?> createAttribute
    )
        where TAttribute : Attribute
    {
        return GetOrCreateAttribute<TAttribute, TData>(symbol, createAttribute)
            ?? throw new InvalidOperationException($"Attribute {typeof(TAttribute).FullName} not found on {symbol.Name}");
    }

    private TData? GetOrCreateAttribute<TAttribute, TData>(
        ISymbol symbol,
        Func<AttributeDataAccessor, AttributeData, TData?> createAttribute
    )
        where TAttribute : Attribute
    {
        var key = new CacheKey(typeof(TAttribute), symbol);
        if (_cache.TryGetValue(key, out var cachedAttribute))
        {
            return (TData?)cachedAttribute;
        }

        var attributeData = symbolAccessor.GetAttributes<TAttribute>(symbol).FirstOrDefault();
        var data = attributeData is not null ? createAttribute(this, attributeData) : default;

        _cache.Add(key, data);

        return data;
    }

    private TData Access<TAttribute, TData>(AttributeData attrData)
        where TAttribute : Attribute
        where TData : notnull
    {
        return Access<TAttribute, TData>(attrData, symbolAccessor);
    }

    private static TData Access<TAttribute, TData>(AttributeData attrData, SymbolAccessor? symbolAccessor = null)
        where TAttribute : Attribute
        where TData : notnull
    {
        var attrType = typeof(TAttribute);
        var dataType = typeof(TData);

        var syntax = (AttributeSyntax?)attrData.ApplicationSyntaxReference?.GetSyntax();
        var syntaxArguments =
            (IReadOnlyList<AttributeArgumentSyntax>?)syntax?.ArgumentList?.Arguments
            ?? new AttributeArgumentSyntax[attrData.ConstructorArguments.Length + attrData.NamedArguments.Length];
        var typeArguments = (IReadOnlyCollection<ITypeSymbol>?)attrData.AttributeClass?.TypeArguments ?? [];
        var attr = Create<TData>(typeArguments, attrData.ConstructorArguments, syntaxArguments, symbolAccessor);

        var syntaxIndex = attrData.ConstructorArguments.Length;
        var propertiesByName = dataType.GetProperties().GroupBy(x => x.Name).ToDictionary(x => x.Key, x => x.First());
        foreach (var namedArgument in attrData.NamedArguments)
        {
            if (!propertiesByName.TryGetValue(namedArgument.Key, out var prop))
                throw new InvalidOperationException($"Could not get property {namedArgument.Key} of attribute {attrType.FullName}");

            var value = BuildArgumentValue(namedArgument.Value, prop.PropertyType, syntaxArguments[syntaxIndex], symbolAccessor);
            prop.SetValue(attr, value);
            syntaxIndex++;
        }

        if (attr is HasSyntaxReference symbolRefHolder)
        {
            symbolRefHolder.SyntaxReference = attrData.ApplicationSyntaxReference?.GetSyntax();
        }

        return attr;
    }

    private static TData Create<TData>(
        IReadOnlyCollection<ITypeSymbol> typeArguments,
        IReadOnlyCollection<TypedConstant> constructorArguments,
        IReadOnlyList<AttributeArgumentSyntax> argumentSyntax,
        SymbolAccessor? symbolAccessor
    )
        where TData : notnull
    {
        // The data class should have a constructor
        // with generic type parameters of the attribute class
        // as ITypeSymbol parameters followed by all other parameters
        // of the attribute constructor.
        // Multiple attribute class constructors/generic data classes are not yet supported.
        var argCount = typeArguments.Count + constructorArguments.Count;
        foreach (var constructor in typeof(TData).GetConstructors())
        {
            var parameters = constructor.GetParameters();
            if (parameters.Length != argCount)
                continue;

            var constructorArgumentValues = constructorArguments.Select(
                (arg, i) => BuildArgumentValue(arg, parameters[i + typeArguments.Count].ParameterType, argumentSyntax[i], symbolAccessor)
            );
            var constructorTypeAndValueArguments = typeArguments.Concat(constructorArgumentValues).ToArray();
            if (!ValidateParameterTypes(constructorTypeAndValueArguments, parameters))
                continue;

            return (TData?)Activator.CreateInstance(typeof(TData), constructorTypeAndValueArguments)
                ?? throw new InvalidOperationException($"Could not create instance of {typeof(TData)}");
        }

        throw new InvalidOperationException(
            $"{typeof(TData)} does not have a constructor with {argCount} parameters and matchable arguments"
        );
    }

    private static object? BuildArgumentValue(
        TypedConstant arg,
        Type targetType,
        AttributeArgumentSyntax? syntax,
        SymbolAccessor? symbolAccessor
    )
    {
        return arg.Kind switch
        {
            _ when (targetType == typeof(AttributeValue?) || targetType == typeof(AttributeValue)) && syntax != null => new AttributeValue(
                arg,
                syntax.Expression
            ),
            _ when arg.IsNull => null,
            _ when targetType == typeof(IMemberPathConfiguration) => CreateMemberPath(arg, syntax, symbolAccessor),
            _ when targetType == typeof(IMethodReferenceConfiguration) => CreateMethodReference(arg, syntax, symbolAccessor),
            TypedConstantKind.Enum => GetEnumValue(arg, targetType),
            TypedConstantKind.Array => BuildArrayValue(arg, targetType, symbolAccessor),
            TypedConstantKind.Primitive => arg.Value,
            TypedConstantKind.Type when targetType == typeof(ITypeSymbol) => arg.Value,
            _ => throw new ArgumentOutOfRangeException(
                $"{nameof(AttributeDataAccessor)} does not support constructor arguments of kind {arg.Kind.ToString()} or cannot convert it to {targetType}"
            ),
        };
    }

    private static IMemberPathConfiguration CreateMemberPath(
        TypedConstant arg,
        AttributeArgumentSyntax? syntax,
        SymbolAccessor? symbolAccessor
    )
    {
        ThrowHelpers.ThrowIfNull(symbolAccessor);

        if (arg.Kind == TypedConstantKind.Array)
        {
            var values = arg
                .Values.Select(x => (string?)BuildArgumentValue(x, typeof(string), null, symbolAccessor))
                .WhereNotNull()
                .ToImmutableEquatableArray();
            return new StringMemberPath(values);
        }

        if (arg.Kind == TypedConstantKind.Primitive && syntax.TryGetNameOfSyntax(out var invocationExpressionSyntax))
        {
            return CreateNameOfMemberPath(invocationExpressionSyntax, symbolAccessor);
        }

        if (arg is { Kind: TypedConstantKind.Primitive, Value: string v })
        {
            return new StringMemberPath(v.Split(MemberPathConstants.MemberAccessSeparator).ToImmutableEquatableArray());
        }

        throw new InvalidOperationException($"Cannot create {nameof(StringMemberPath)} from {arg.Kind}");
    }

    private static IMemberPathConfiguration CreateNameOfMemberPath(InvocationExpressionSyntax nameofSyntax, SymbolAccessor symbolAccessor)
    {
        // @ prefix opts-in to full nameof
        var fullNameOf = nameofSyntax.IsFullNameOfSyntax();

        var nameOfOperation = symbolAccessor.GetOperation<INameOfOperation>(nameofSyntax);
        var memberRefOperation = nameOfOperation?.GetFirstChildOperation<IMemberReferenceOperation>();
        if (memberRefOperation == null)
        {
            // fall back to old skip-first-segment approach
            // to ensure backwards compability.

            var argMemberPathStr = nameofSyntax.ArgumentList.Arguments[0].ToFullString();
            var argMemberPath = argMemberPathStr
                .TrimStart(FullNameOfPrefix)
                .Split(MemberPathConstants.MemberAccessSeparator)
                .Skip(1)
                .ToImmutableEquatableArray();
            return new StringMemberPath(argMemberPath);
        }

        var memberPath = new List<ISymbol>();
        while (memberRefOperation != null)
        {
            memberPath.Add(memberRefOperation.Member);
            memberRefOperation = memberRefOperation.GetFirstChildOperation<IMemberReferenceOperation>();

            // if not fullNameOf only consider the last member path segment
            if (!fullNameOf && memberPath.Count > 1)
                break;
        }

        memberPath.Reverse();
        return new SymbolMemberPath(memberPath.ToImmutableEquatableArray());
    }

    private static IMethodReferenceConfiguration CreateMethodReference(
        TypedConstant arg,
        AttributeArgumentSyntax? syntax,
        SymbolAccessor? symbolAccessor
    )
    {
        ThrowHelpers.ThrowIfNull(symbolAccessor);

        if (arg.Kind != TypedConstantKind.Primitive)
        {
            throw new InvalidOperationException($"Cannot create {nameof(IMethodReferenceConfiguration)} from {arg.Kind}");
        }

        if (
            syntax.TryGetNameOfSyntax(out var invocationExpressionSyntax)
            && invocationExpressionSyntax.IsFullNameOfSyntax()
            && TryCreateNameOfMethodReferenceConfiguration(invocationExpressionSyntax, symbolAccessor, out var configuration)
        )
        {
            return configuration;
        }

        if (arg.Value is not string fullName)
        {
            throw new InvalidOperationException($"Unknown method reference configuration: {arg.Value}");
        }

        var splitPoint = fullName.LastIndexOf(MemberPathConstants.MemberAccessSeparator);
        var methodName = splitPoint == -1 ? fullName : fullName[(splitPoint + 1)..];
        var targetName = splitPoint == -1 ? null : fullName[..splitPoint];
        return new StringMethodReferenceConfiguration(methodName, targetName, fullName);
    }

    private static bool TryCreateNameOfMethodReferenceConfiguration(
        InvocationExpressionSyntax nameofSyntax,
        SymbolAccessor symbolAccessor,
        [NotNullWhen(true)] out IMethodReferenceConfiguration? configuration
    )
    {
        configuration = null;
        var nameOfOperation = symbolAccessor.GetOperation<INameOfOperation>(nameofSyntax);
        var operation = nameOfOperation?.GetFirstChildOperation<IOperation>();
        var memberName = operation?.Syntax.TryGetInferredMemberName();
        if (memberName is null || operation is null)
        {
            return false;
        }

        operation = operation.GetFirstChildOperation<IOperation>();
        if (operation is null)
        {
            return false;
        }

        if (operation is IInvalidOperation)
        {
            var targetName = operation.Syntax.ToString();
            configuration = new StringMethodReferenceConfiguration(memberName, targetName, $"{targetName}.{memberName}");
            return true;
        }

        if (operation.Type is not INamedTypeSymbol typeSymbol)
        {
            return false;
        }

        var field = operation.GetMemberSymbol();
        if (field is null)
        {
            configuration = new ExternalStaticMethodReferenceConfiguration(memberName, typeSymbol);
            return true;
        }

        configuration = new ExternalInstanceMethodReferenceConfiguration(memberName, field, typeSymbol);
        return true;
    }

    private static object?[] BuildArrayValue(TypedConstant arg, Type targetType, SymbolAccessor? symbolAccessor)
    {
        if (!targetType.IsGenericType || targetType.GetGenericTypeDefinition() != typeof(IReadOnlyCollection<>))
            throw new InvalidOperationException($"{nameof(IReadOnlyCollection<object>)} is the only supported array type");

        var elementTargetType = targetType.GetGenericArguments()[0];
        return arg.Values.Select(x => BuildArgumentValue(x, elementTargetType, null, symbolAccessor)).ToArray();
    }

    private static object? GetEnumValue(TypedConstant arg, Type targetType)
    {
        if (arg.Value == null)
            return null;

        var enumRoslynType = arg.Type ?? throw new InvalidOperationException("Type is null");
        if (targetType == typeof(IFieldSymbol))
            return enumRoslynType.GetFields().First(f => Equals(f.ConstantValue, arg.Value));

        if (targetType.IsConstructedGenericType && targetType.GetGenericTypeDefinition() == typeof(Nullable<>))
        {
            targetType = Nullable.GetUnderlyingType(targetType)!;
        }

        return Enum.ToObject(targetType, arg.Value);
    }

    private static bool ValidateParameterTypes(object?[] arguments, ParameterInfo[] parameters)
    {
        if (arguments.Length != parameters.Length)
            return false;

        for (var argIdx = 0; argIdx < arguments.Length; argIdx++)
        {
            var value = arguments[argIdx];
            var param = parameters[argIdx];
            if (value == null && param.ParameterType.IsValueType)
                return false;

            if (value?.GetType().IsAssignableTo(param.ParameterType) == false)
                return false;
        }

        return true;
    }

    private static TValue? GetSimpleValue<TValue>(AttributeData attrData, string propertyName, TValue? defaultValue = null)
        where TValue : struct
    {
        var value = attrData.NamedArguments.FirstOrDefault(kv => kv.Key == propertyName).Value.Value;
        if (typeof(TValue).IsEnum && value is int i)
        {
            return (TValue)(object)i;
        }

        if (value is TValue tValue)
        {
            return tValue;
        }

        return defaultValue;
    }

    private record struct CacheKey(Type Attribute, ISymbol Symbol);
}
