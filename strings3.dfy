predicate isPrefixPred(pre:string, str:string)
{
	(|pre| <= |str|) && 
	pre == str[..|pre|]
}

predicate isNotPrefixPred(pre:string, str:string)
{
	(|pre| > |str|) || 
	pre != str[..|pre|]
}

lemma PrefixNegationLemma(pre:string, str:string)
	ensures  isPrefixPred(pre,str) <==> !isNotPrefixPred(pre,str)
	ensures !isPrefixPred(pre,str) <==>  isNotPrefixPred(pre,str)
{}

method isPrefix(pre: string, str: string) returns (res:bool)
	ensures !res <==> isNotPrefixPred(pre,str)
	ensures  res <==> isPrefixPred(pre,str)
{
    return |pre| <= |str| && forall i :: 0 <= i < |pre| ==> pre[i] == str[i];
}
predicate isSubstringPred(sub:string, str:string)
{
	(exists i :: 0 <= i <= |str| &&  isPrefixPred(sub, str[i..]))
}

predicate isNotSubstringPred(sub:string, str:string)
{
	(forall i :: 0 <= i <= |str| ==> isNotPrefixPred(sub,str[i..]))
}

lemma SubstringNegationLemma(sub:string, str:string)
	ensures  isSubstringPred(sub,str) <==> !isNotSubstringPred(sub,str)
	ensures !isSubstringPred(sub,str) <==>  isNotSubstringPred(sub,str)
{}

function add(x : nat, y : nat): nat {
	x + y
}

method isSubstring(sub: string, str: string) returns (res:bool)
	// ensures  res <==> isSubstringPred(sub, str)
	ensures  res ==> isSubstringPred(sub, str)
	ensures  !res ==> !isSubstringPred(sub, str)
	ensures  isSubstringPred(sub, str) ==> res
	ensures  isSubstringPred(sub, str) ==> res
	// ensures !res <==> isNotSubstringPred(sub, str) // This postcondition follows from the above lemma.
{
	var isPre : bool := isPrefix(sub, str);
	var isSub : bool := false;
    var i : nat := 0;
    while (i < |str|)
			invariant (isSub) ==> ((|sub| <= |str|) && exists x :: (0 <= x <= i && |sub| +  x <= |str| && sub == str[x..|sub| + x]))
			invariant ((|sub| <= |str|) && exists x :: (0 <= x < i && |sub| + x <= |str| && sub == str[x..|sub| + x])) ==> isSub
			invariant ((!isSub) ==> (|sub| > |str|) || forall x :: (( 0 <= x < i ==> (|sub| +  x) >= |str| || !(sub == str[x..|sub| + x]))))
			invariant ((|sub| >= |str|) || forall x :: (( 0 <= x < i ==> (|sub| +  x >= |str| || !(sub == str[x..|sub| + x])))) ==> !isSub)
			invariant i <= |str|;
			decreases |str| - i;
    {
        isPre := isPrefix(sub, str[i..]);
		if isPre
		{
			isSub := true;
			// break;
			return true;
		}
        i := i + 1;    
    }
	// isPre := isPrefix(sub, str[i..]);

	return false;
}


predicate haveCommonKSubstringPred(k:nat, str1:string, str2:string)
{
	exists i1, j1 :: 0 <= i1 <= |str1|- k && j1 == i1 + k && isSubstringPred(str1[i1..j1],str2)
}

predicate haveNotCommonKSubstringPred(k:nat, str1:string, str2:string)
{
	forall i1, j1 :: 0 <= i1 <= |str1|- k && j1 == i1 + k ==>  isNotSubstringPred(str1[i1..j1],str2)
}

lemma commonKSubstringLemma(k:nat, str1:string, str2:string)
	ensures  haveCommonKSubstringPred(k,str1,str2) <==> !haveNotCommonKSubstringPred(k,str1,str2)
	ensures !haveCommonKSubstringPred(k,str1,str2) <==>  haveNotCommonKSubstringPred(k,str1,str2)
{}

method haveCommonKSubstring(k: nat, str1: string, str2: string) returns (found: bool)
	ensures found  <==>  haveCommonKSubstringPred(k,str1,str2)
	//ensures !found <==> haveNotCommonKSubstringPred(k,str1,str2) // This postcondition follows from the above lemma.
{
//TODO: insert your code here
}

method maxCommonSubstringLength(str1: string, str2: string) returns (len:nat)
	requires (|str1| <= |str2|)
	ensures (forall k :: len < k <= |str1| ==> !haveCommonKSubstringPred(k,str1,str2))
	ensures haveCommonKSubstringPred(len,str1,str2)
{
//TODO: insert your code here
}


