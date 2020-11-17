
method isPrefix(pre: string, str: string) returns (res:bool)
    requires |pre| <= |str|
{
    return forall i :: 0 <= i < |pre| ==> pre[i] == str[i];
}

method isSubstring(sub: string, str: string) returns (res:bool)
    requires |sub| <= |str|
{
    var isPre : bool := isPrefix(sub, str);
    if isPre
    {
        return true;
    }
    var i : nat := 1;
    while (i <= (|str| - |sub|))
    {
        isPre := isPrefix(sub, str[i..]);
        i := i + 1;    
    }
}

method haveCommonKSubstring(k: nat, str1: string, str2: string) returns (found: bool)
    requires (k <= |str1| || k <= |str2|)
{
    var slice : string;
    var isSub : bool;
    var i: nat := 0;

    while (i <= |str1| - k)
    {
        slice := str1[i..i+k];
        isSub := isSubstring(slice, str1);
        if (isSub)
        {
            return true;
        }
        i := i + 1;
    }
    return false;
}


method maxCommonSubstringLength(str1: string, str2: string) returns (len:nat)
{
    var hasCommon : bool := false;
    len := 0;
    var shortStr : string := str1;
    var longStr : string := str2;

    if (|str1| > |str2|)
    {
        shortStr := str2;
        longStr := str1;
    }
    
    while (len < |shortStr|)
    {
        hasCommon := haveCommonKSubstring(len, shortStr, longStr);
        if (hasCommon)
        {
            len := len + 1;
        }
        else 
        {
            return 0;
        }
    }
}