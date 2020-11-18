predicate isPrefixPred(pre:string, str:string)
{
	(|pre| <= |str|) && pre == str[..|pre|]
}

predicate isNotPrefixPred(pre:string, str:string)
{
	!(|pre| <= |str|) || !(pre == str[..|pre|])
}

// Sanity check: Dafny should be able to automatically prove the following lemma
lemma PrefixNegationLemma(pre:string, str:string)
	ensures  isPrefixPred(pre,str) <==> !isNotPrefixPred(pre,str)
	ensures !isPrefixPred(pre,str) <==>  isNotPrefixPred(pre,str)
{}


predicate isSubstringPred(sub:string, str:string)
{
  (|sub| <= |str|) && exists x :: (x >= 0 && |sub| + x <= |str| && sub == str[x..|sub| + x])
}

predicate isNotSubstringPred(sub:string, str:string)
{

	(|sub| > |str|) || forall x :: ((x < 0 || |sub| + x > |str| || !(sub == str[x..|sub| + x])))
}

// Sanity check: Dafny should be able to automatically prove the following lemma
lemma SubstringNegationLemma(sub:string, str:string)
	ensures  isSubstringPred(sub,str) <==> !isNotSubstringPred(sub,str)
	ensures !isSubstringPred(sub,str) <==>  isNotSubstringPred(sub,str)
{}


predicate haveCommonKSubstringPred(k:nat, str1:string, str2:string)
{
  k <= |str1| && k <= |str2| && exists i :: (exists j :: ( i >= 0 && j >= 0 && i + k <= |str1| && j + k <= |str2|  && str1[i..i+k] == str2[j..j+k]) )
    // forall i :: (forall j :: (i < 0 || j < 0 || i + k > |str1| || j + k > |str2| || !(str1[i..i+k] == str2[j..j+k])))
}

predicate haveNotCommonKSubstringPred(k:nat, str1:string, str2:string)
{
    k > |str1| || k > |str2| || forall i :: (forall j :: (i < 0 || j < 0 || i + k > |str1| || j + k > |str2| || !(str1[i..i+k] == str2[j..j+k])))
}

// Sanity check: Dafny should be able to automatically prove the following lemma
lemma commonKSubstringLemma(k:nat, str1:string, str2:string)
	ensures  haveCommonKSubstringPred(k,str1,str2) <==> !haveNotCommonKSubstringPred(k,str1,str2)
	ensures !haveCommonKSubstringPred(k,str1,str2) <==> haveNotCommonKSubstringPred(k,str1,str2)
{}
