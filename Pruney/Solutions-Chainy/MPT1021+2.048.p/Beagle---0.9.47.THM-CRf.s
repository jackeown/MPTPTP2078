%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:07 EST 2020

% Result     : Theorem 6.36s
% Output     : CNFRefutation 6.68s
% Verified   : 
% Statistics : Number of formulae       :  176 (13279 expanded)
%              Number of leaves         :   42 (5365 expanded)
%              Depth                    :   23
%              Number of atoms          :  427 (48761 expanded)
%              Number of equality atoms :   61 (2450 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k2_funct_2,type,(
    k2_funct_2: ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v2_funct_2,type,(
    v2_funct_2: ( $i * $i ) > $o )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v3_funct_2,type,(
    v3_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_105,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_116,axiom,(
    ! [A,B] :
    ? [C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
      & v1_relat_1(C)
      & v4_relat_1(C,A)
      & v5_relat_1(C,B)
      & v1_funct_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_partfun1)).

tff(f_73,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(f_159,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & v3_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ( r2_relset_1(A,A,k1_partfun1(A,A,A,A,B,k2_funct_2(A,B)),k6_partfun1(A))
          & r2_relset_1(A,A,k1_partfun1(A,A,A,A,k2_funct_2(A,B),B),k6_partfun1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_funct_2)).

tff(f_136,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k2_funct_2(A,B) = k2_funct_1(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

tff(f_101,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => ( v1_funct_1(k2_funct_2(A,B))
        & v1_funct_2(k2_funct_2(A,B),A,A)
        & v3_funct_2(k2_funct_2(A,B),A,A)
        & m1_subset_1(k2_funct_2(A,B),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_2)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_146,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k1_relset_1(A,A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_2)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_59,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(k2_funct_1(A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).

tff(f_138,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_43,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_126,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(c_36,plain,(
    ! [A_20] : m1_subset_1(k6_partfun1(A_20),k1_zfmisc_1(k2_zfmisc_1(A_20,A_20))) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_46,plain,(
    ! [A_21,B_22] : m1_subset_1('#skF_1'(A_21,B_22),k1_zfmisc_1(k2_zfmisc_1(A_21,B_22))) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_2443,plain,(
    ! [A_196,B_197,C_198,D_199] :
      ( r2_relset_1(A_196,B_197,C_198,C_198)
      | ~ m1_subset_1(D_199,k1_zfmisc_1(k2_zfmisc_1(A_196,B_197)))
      | ~ m1_subset_1(C_198,k1_zfmisc_1(k2_zfmisc_1(A_196,B_197))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_2453,plain,(
    ! [A_200,B_201,C_202] :
      ( r2_relset_1(A_200,B_201,C_202,C_202)
      | ~ m1_subset_1(C_202,k1_zfmisc_1(k2_zfmisc_1(A_200,B_201))) ) ),
    inference(resolution,[status(thm)],[c_46,c_2443])).

tff(c_2461,plain,(
    ! [A_20] : r2_relset_1(A_20,A_20,k6_partfun1(A_20),k6_partfun1(A_20)) ),
    inference(resolution,[status(thm)],[c_36,c_2453])).

tff(c_64,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_62,plain,(
    v1_funct_2('#skF_3','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_60,plain,(
    v3_funct_2('#skF_3','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_58,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_2515,plain,(
    ! [A_214,B_215] :
      ( k2_funct_2(A_214,B_215) = k2_funct_1(B_215)
      | ~ m1_subset_1(B_215,k1_zfmisc_1(k2_zfmisc_1(A_214,A_214)))
      | ~ v3_funct_2(B_215,A_214,A_214)
      | ~ v1_funct_2(B_215,A_214,A_214)
      | ~ v1_funct_1(B_215) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_2525,plain,
    ( k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_2515])).

tff(c_2532,plain,(
    k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_2525])).

tff(c_2494,plain,(
    ! [A_209,B_210] :
      ( v1_funct_1(k2_funct_2(A_209,B_210))
      | ~ m1_subset_1(B_210,k1_zfmisc_1(k2_zfmisc_1(A_209,A_209)))
      | ~ v3_funct_2(B_210,A_209,A_209)
      | ~ v1_funct_2(B_210,A_209,A_209)
      | ~ v1_funct_1(B_210) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_2504,plain,
    ( v1_funct_1(k2_funct_2('#skF_2','#skF_3'))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_2494])).

tff(c_2511,plain,(
    v1_funct_1(k2_funct_2('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_2504])).

tff(c_2533,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2532,c_2511])).

tff(c_85,plain,(
    ! [C_50,A_51,B_52] :
      ( v1_relat_1(C_50)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k2_zfmisc_1(A_51,B_52))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_98,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_85])).

tff(c_2405,plain,(
    ! [C_184,A_185,B_186] :
      ( v2_funct_1(C_184)
      | ~ v3_funct_2(C_184,A_185,B_186)
      | ~ v1_funct_1(C_184)
      | ~ m1_subset_1(C_184,k1_zfmisc_1(k2_zfmisc_1(A_185,B_186))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_2414,plain,
    ( v2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_2405])).

tff(c_2421,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60,c_2414])).

tff(c_2575,plain,(
    ! [A_225,B_226] :
      ( m1_subset_1(k2_funct_2(A_225,B_226),k1_zfmisc_1(k2_zfmisc_1(A_225,A_225)))
      | ~ m1_subset_1(B_226,k1_zfmisc_1(k2_zfmisc_1(A_225,A_225)))
      | ~ v3_funct_2(B_226,A_225,A_225)
      | ~ v1_funct_2(B_226,A_225,A_225)
      | ~ v1_funct_1(B_226) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_2605,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2532,c_2575])).

tff(c_2617,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_58,c_2605])).

tff(c_14,plain,(
    ! [C_7,A_5,B_6] :
      ( v1_relat_1(C_7)
      | ~ m1_subset_1(C_7,k1_zfmisc_1(k2_zfmisc_1(A_5,B_6))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2668,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2617,c_14])).

tff(c_2558,plain,(
    ! [A_221,B_222] :
      ( v3_funct_2(k2_funct_2(A_221,B_222),A_221,A_221)
      | ~ m1_subset_1(B_222,k1_zfmisc_1(k2_zfmisc_1(A_221,A_221)))
      | ~ v3_funct_2(B_222,A_221,A_221)
      | ~ v1_funct_2(B_222,A_221,A_221)
      | ~ v1_funct_1(B_222) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_2565,plain,
    ( v3_funct_2(k2_funct_2('#skF_2','#skF_3'),'#skF_2','#skF_2')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_2558])).

tff(c_2572,plain,(
    v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_2532,c_2565])).

tff(c_22,plain,(
    ! [C_17,A_15,B_16] :
      ( v2_funct_1(C_17)
      | ~ v3_funct_2(C_17,A_15,B_16)
      | ~ v1_funct_1(C_17)
      | ~ m1_subset_1(C_17,k1_zfmisc_1(k2_zfmisc_1(A_15,B_16))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_2638,plain,
    ( v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2617,c_22])).

tff(c_2666,plain,(
    v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2533,c_2572,c_2638])).

tff(c_2542,plain,(
    ! [A_218,B_219] :
      ( v1_funct_2(k2_funct_2(A_218,B_219),A_218,A_218)
      | ~ m1_subset_1(B_219,k1_zfmisc_1(k2_zfmisc_1(A_218,A_218)))
      | ~ v3_funct_2(B_219,A_218,A_218)
      | ~ v1_funct_2(B_219,A_218,A_218)
      | ~ v1_funct_1(B_219) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_2549,plain,
    ( v1_funct_2(k2_funct_2('#skF_2','#skF_3'),'#skF_2','#skF_2')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_2542])).

tff(c_2556,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_2532,c_2549])).

tff(c_54,plain,(
    ! [A_33,B_34] :
      ( k1_relset_1(A_33,A_33,B_34) = A_33
      | ~ m1_subset_1(B_34,k1_zfmisc_1(k2_zfmisc_1(A_33,A_33)))
      | ~ v1_funct_2(B_34,A_33,A_33)
      | ~ v1_funct_1(B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_2630,plain,
    ( k1_relset_1('#skF_2','#skF_2',k2_funct_1('#skF_3')) = '#skF_2'
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2617,c_54])).

tff(c_2659,plain,(
    k1_relset_1('#skF_2','#skF_2',k2_funct_1('#skF_3')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2533,c_2556,c_2630])).

tff(c_16,plain,(
    ! [A_8,B_9,C_10] :
      ( k1_relset_1(A_8,B_9,C_10) = k1_relat_1(C_10)
      | ~ m1_subset_1(C_10,k1_zfmisc_1(k2_zfmisc_1(A_8,B_9))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_2667,plain,(
    k1_relset_1('#skF_2','#skF_2',k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2617,c_16])).

tff(c_2749,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2659,c_2667])).

tff(c_12,plain,(
    ! [A_4] :
      ( k2_funct_1(k2_funct_1(A_4)) = A_4
      | ~ v2_funct_1(A_4)
      | ~ v1_funct_1(A_4)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_52,plain,(
    ! [A_32] : k6_relat_1(A_32) = k6_partfun1(A_32) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_8,plain,(
    ! [A_2] :
      ( k5_relat_1(A_2,k2_funct_1(A_2)) = k6_relat_1(k1_relat_1(A_2))
      | ~ v2_funct_1(A_2)
      | ~ v1_funct_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2363,plain,(
    ! [A_179] :
      ( k5_relat_1(A_179,k2_funct_1(A_179)) = k6_partfun1(k1_relat_1(A_179))
      | ~ v2_funct_1(A_179)
      | ~ v1_funct_1(A_179)
      | ~ v1_relat_1(A_179) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_8])).

tff(c_3220,plain,(
    ! [A_247] :
      ( k6_partfun1(k1_relat_1(k2_funct_1(A_247))) = k5_relat_1(k2_funct_1(A_247),A_247)
      | ~ v2_funct_1(k2_funct_1(A_247))
      | ~ v1_funct_1(k2_funct_1(A_247))
      | ~ v1_relat_1(k2_funct_1(A_247))
      | ~ v2_funct_1(A_247)
      | ~ v1_funct_1(A_247)
      | ~ v1_relat_1(A_247) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_2363])).

tff(c_3280,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2')
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2749,c_3220])).

tff(c_3294,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_64,c_2421,c_2668,c_2533,c_2666,c_3280])).

tff(c_26,plain,(
    ! [A_18,B_19] :
      ( m1_subset_1(k2_funct_2(A_18,B_19),k1_zfmisc_1(k2_zfmisc_1(A_18,A_18)))
      | ~ m1_subset_1(B_19,k1_zfmisc_1(k2_zfmisc_1(A_18,A_18)))
      | ~ v3_funct_2(B_19,A_18,A_18)
      | ~ v1_funct_2(B_19,A_18,A_18)
      | ~ v1_funct_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_2669,plain,(
    ! [C_227,D_232,E_229,B_228,F_230,A_231] :
      ( k1_partfun1(A_231,B_228,C_227,D_232,E_229,F_230) = k5_relat_1(E_229,F_230)
      | ~ m1_subset_1(F_230,k1_zfmisc_1(k2_zfmisc_1(C_227,D_232)))
      | ~ v1_funct_1(F_230)
      | ~ m1_subset_1(E_229,k1_zfmisc_1(k2_zfmisc_1(A_231,B_228)))
      | ~ v1_funct_1(E_229) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_2679,plain,(
    ! [A_231,B_228,E_229] :
      ( k1_partfun1(A_231,B_228,'#skF_2','#skF_2',E_229,'#skF_3') = k5_relat_1(E_229,'#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(E_229,k1_zfmisc_1(k2_zfmisc_1(A_231,B_228)))
      | ~ v1_funct_1(E_229) ) ),
    inference(resolution,[status(thm)],[c_58,c_2669])).

tff(c_2705,plain,(
    ! [A_233,B_234,E_235] :
      ( k1_partfun1(A_233,B_234,'#skF_2','#skF_2',E_235,'#skF_3') = k5_relat_1(E_235,'#skF_3')
      | ~ m1_subset_1(E_235,k1_zfmisc_1(k2_zfmisc_1(A_233,B_234)))
      | ~ v1_funct_1(E_235) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_2679])).

tff(c_3310,plain,(
    ! [A_248,B_249] :
      ( k1_partfun1(A_248,A_248,'#skF_2','#skF_2',k2_funct_2(A_248,B_249),'#skF_3') = k5_relat_1(k2_funct_2(A_248,B_249),'#skF_3')
      | ~ v1_funct_1(k2_funct_2(A_248,B_249))
      | ~ m1_subset_1(B_249,k1_zfmisc_1(k2_zfmisc_1(A_248,A_248)))
      | ~ v3_funct_2(B_249,A_248,A_248)
      | ~ v1_funct_2(B_249,A_248,A_248)
      | ~ v1_funct_1(B_249) ) ),
    inference(resolution,[status(thm)],[c_26,c_2705])).

tff(c_3323,plain,
    ( k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_2('#skF_2','#skF_3'),'#skF_3') = k5_relat_1(k2_funct_2('#skF_2','#skF_3'),'#skF_3')
    | ~ v1_funct_1(k2_funct_2('#skF_2','#skF_3'))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_3310])).

tff(c_3337,plain,(
    k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_2533,c_2532,c_3294,c_2532,c_2532,c_3323])).

tff(c_225,plain,(
    ! [A_76,B_77,C_78,D_79] :
      ( r2_relset_1(A_76,B_77,C_78,C_78)
      | ~ m1_subset_1(D_79,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77)))
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_235,plain,(
    ! [A_80,B_81,C_82] :
      ( r2_relset_1(A_80,B_81,C_82,C_82)
      | ~ m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1(A_80,B_81))) ) ),
    inference(resolution,[status(thm)],[c_46,c_225])).

tff(c_243,plain,(
    ! [A_20] : r2_relset_1(A_20,A_20,k6_partfun1(A_20),k6_partfun1(A_20)) ),
    inference(resolution,[status(thm)],[c_36,c_235])).

tff(c_295,plain,(
    ! [A_92,B_93] :
      ( k2_funct_2(A_92,B_93) = k2_funct_1(B_93)
      | ~ m1_subset_1(B_93,k1_zfmisc_1(k2_zfmisc_1(A_92,A_92)))
      | ~ v3_funct_2(B_93,A_92,A_92)
      | ~ v1_funct_2(B_93,A_92,A_92)
      | ~ v1_funct_1(B_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_305,plain,
    ( k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_295])).

tff(c_312,plain,(
    k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_305])).

tff(c_357,plain,(
    ! [A_106,B_107] :
      ( m1_subset_1(k2_funct_2(A_106,B_107),k1_zfmisc_1(k2_zfmisc_1(A_106,A_106)))
      | ~ m1_subset_1(B_107,k1_zfmisc_1(k2_zfmisc_1(A_106,A_106)))
      | ~ v3_funct_2(B_107,A_106,A_106)
      | ~ v1_funct_2(B_107,A_106,A_106)
      | ~ v1_funct_1(B_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_387,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_312,c_357])).

tff(c_399,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_58,c_387])).

tff(c_450,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_399,c_14])).

tff(c_275,plain,(
    ! [A_88,B_89] :
      ( v1_funct_1(k2_funct_2(A_88,B_89))
      | ~ m1_subset_1(B_89,k1_zfmisc_1(k2_zfmisc_1(A_88,A_88)))
      | ~ v3_funct_2(B_89,A_88,A_88)
      | ~ v1_funct_2(B_89,A_88,A_88)
      | ~ v1_funct_1(B_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_285,plain,
    ( v1_funct_1(k2_funct_2('#skF_2','#skF_3'))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_275])).

tff(c_292,plain,(
    v1_funct_1(k2_funct_2('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_285])).

tff(c_313,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_312,c_292])).

tff(c_321,plain,(
    ! [A_96,B_97] :
      ( v3_funct_2(k2_funct_2(A_96,B_97),A_96,A_96)
      | ~ m1_subset_1(B_97,k1_zfmisc_1(k2_zfmisc_1(A_96,A_96)))
      | ~ v3_funct_2(B_97,A_96,A_96)
      | ~ v1_funct_2(B_97,A_96,A_96)
      | ~ v1_funct_1(B_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_328,plain,
    ( v3_funct_2(k2_funct_2('#skF_2','#skF_3'),'#skF_2','#skF_2')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_321])).

tff(c_335,plain,(
    v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_312,c_328])).

tff(c_420,plain,
    ( v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_399,c_22])).

tff(c_448,plain,(
    v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_313,c_335,c_420])).

tff(c_338,plain,(
    ! [A_100,B_101] :
      ( v1_funct_2(k2_funct_2(A_100,B_101),A_100,A_100)
      | ~ m1_subset_1(B_101,k1_zfmisc_1(k2_zfmisc_1(A_100,A_100)))
      | ~ v3_funct_2(B_101,A_100,A_100)
      | ~ v1_funct_2(B_101,A_100,A_100)
      | ~ v1_funct_1(B_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_345,plain,
    ( v1_funct_2(k2_funct_2('#skF_2','#skF_3'),'#skF_2','#skF_2')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_338])).

tff(c_352,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_312,c_345])).

tff(c_50,plain,(
    ! [A_30,B_31] :
      ( k2_funct_2(A_30,B_31) = k2_funct_1(B_31)
      | ~ m1_subset_1(B_31,k1_zfmisc_1(k2_zfmisc_1(A_30,A_30)))
      | ~ v3_funct_2(B_31,A_30,A_30)
      | ~ v1_funct_2(B_31,A_30,A_30)
      | ~ v1_funct_1(B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_406,plain,
    ( k2_funct_2('#skF_2',k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3'))
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_399,c_50])).

tff(c_435,plain,(
    k2_funct_2('#skF_2',k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_313,c_352,c_335,c_406])).

tff(c_483,plain,
    ( m1_subset_1(k2_funct_1(k2_funct_1('#skF_3')),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_435,c_26])).

tff(c_487,plain,(
    m1_subset_1(k2_funct_1(k2_funct_1('#skF_3')),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_313,c_352,c_335,c_399,c_483])).

tff(c_600,plain,(
    v1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_487,c_14])).

tff(c_32,plain,(
    ! [A_18,B_19] :
      ( v1_funct_1(k2_funct_2(A_18,B_19))
      | ~ m1_subset_1(B_19,k1_zfmisc_1(k2_zfmisc_1(A_18,A_18)))
      | ~ v3_funct_2(B_19,A_18,A_18)
      | ~ v1_funct_2(B_19,A_18,A_18)
      | ~ v1_funct_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_409,plain,
    ( v1_funct_1(k2_funct_2('#skF_2',k2_funct_1('#skF_3')))
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_399,c_32])).

tff(c_438,plain,(
    v1_funct_1(k2_funct_2('#skF_2',k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_313,c_352,c_335,c_409])).

tff(c_479,plain,(
    v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_435,c_438])).

tff(c_28,plain,(
    ! [A_18,B_19] :
      ( v3_funct_2(k2_funct_2(A_18,B_19),A_18,A_18)
      | ~ m1_subset_1(B_19,k1_zfmisc_1(k2_zfmisc_1(A_18,A_18)))
      | ~ v3_funct_2(B_19,A_18,A_18)
      | ~ v1_funct_2(B_19,A_18,A_18)
      | ~ v1_funct_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_403,plain,
    ( v3_funct_2(k2_funct_2('#skF_2',k2_funct_1('#skF_3')),'#skF_2','#skF_2')
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_399,c_28])).

tff(c_432,plain,(
    v3_funct_2(k2_funct_2('#skF_2',k2_funct_1('#skF_3')),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_313,c_352,c_335,c_403])).

tff(c_477,plain,(
    v3_funct_2(k2_funct_1(k2_funct_1('#skF_3')),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_435,c_432])).

tff(c_561,plain,
    ( v2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v3_funct_2(k2_funct_1(k2_funct_1('#skF_3')),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_487,c_22])).

tff(c_598,plain,(
    v2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_479,c_477,c_561])).

tff(c_30,plain,(
    ! [A_18,B_19] :
      ( v1_funct_2(k2_funct_2(A_18,B_19),A_18,A_18)
      | ~ m1_subset_1(B_19,k1_zfmisc_1(k2_zfmisc_1(A_18,A_18)))
      | ~ v3_funct_2(B_19,A_18,A_18)
      | ~ v1_funct_2(B_19,A_18,A_18)
      | ~ v1_funct_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_401,plain,
    ( v1_funct_2(k2_funct_2('#skF_2',k2_funct_1('#skF_3')),'#skF_2','#skF_2')
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_399,c_30])).

tff(c_429,plain,(
    v1_funct_2(k2_funct_2('#skF_2',k2_funct_1('#skF_3')),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_313,c_352,c_335,c_401])).

tff(c_478,plain,(
    v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_435,c_429])).

tff(c_553,plain,
    ( k1_relset_1('#skF_2','#skF_2',k2_funct_1(k2_funct_1('#skF_3'))) = '#skF_2'
    | ~ v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_487,c_54])).

tff(c_591,plain,(
    k1_relset_1('#skF_2','#skF_2',k2_funct_1(k2_funct_1('#skF_3'))) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_479,c_478,c_553])).

tff(c_599,plain,(
    k1_relset_1('#skF_2','#skF_2',k2_funct_1(k2_funct_1('#skF_3'))) = k1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_487,c_16])).

tff(c_922,plain,(
    k1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_591,c_599])).

tff(c_175,plain,(
    ! [A_63] :
      ( k5_relat_1(A_63,k2_funct_1(A_63)) = k6_partfun1(k1_relat_1(A_63))
      | ~ v2_funct_1(A_63)
      | ~ v1_funct_1(A_63)
      | ~ v1_relat_1(A_63) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_8])).

tff(c_1053,plain,(
    ! [A_128] :
      ( k6_partfun1(k1_relat_1(k2_funct_1(A_128))) = k5_relat_1(k2_funct_1(A_128),A_128)
      | ~ v2_funct_1(k2_funct_1(A_128))
      | ~ v1_funct_1(k2_funct_1(A_128))
      | ~ v1_relat_1(k2_funct_1(A_128))
      | ~ v2_funct_1(A_128)
      | ~ v1_funct_1(A_128)
      | ~ v1_relat_1(A_128) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_175])).

tff(c_187,plain,(
    ! [C_64,A_65,B_66] :
      ( v2_funct_1(C_64)
      | ~ v3_funct_2(C_64,A_65,B_66)
      | ~ v1_funct_1(C_64)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_196,plain,
    ( v2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_187])).

tff(c_203,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60,c_196])).

tff(c_547,plain,
    ( k2_funct_2('#skF_2',k2_funct_1(k2_funct_1('#skF_3'))) = k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v3_funct_2(k2_funct_1(k2_funct_1('#skF_3')),'#skF_2','#skF_2')
    | ~ v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_487,c_50])).

tff(c_585,plain,(
    k2_funct_2('#skF_2',k2_funct_1(k2_funct_1('#skF_3'))) = k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_479,c_478,c_477,c_547])).

tff(c_696,plain,
    ( k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) = k2_funct_2('#skF_2','#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_585])).

tff(c_702,plain,(
    k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_64,c_203,c_312,c_696])).

tff(c_6,plain,(
    ! [A_2] :
      ( k5_relat_1(k2_funct_1(A_2),A_2) = k6_relat_1(k2_relat_1(A_2))
      | ~ v2_funct_1(A_2)
      | ~ v1_funct_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_163,plain,(
    ! [A_62] :
      ( k5_relat_1(k2_funct_1(A_62),A_62) = k6_partfun1(k2_relat_1(A_62))
      | ~ v2_funct_1(A_62)
      | ~ v1_funct_1(A_62)
      | ~ v1_relat_1(A_62) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_6])).

tff(c_853,plain,(
    ! [A_126] :
      ( k6_partfun1(k2_relat_1(k2_funct_1(A_126))) = k5_relat_1(A_126,k2_funct_1(A_126))
      | ~ v2_funct_1(k2_funct_1(A_126))
      | ~ v1_funct_1(k2_funct_1(A_126))
      | ~ v1_relat_1(k2_funct_1(A_126))
      | ~ v2_funct_1(A_126)
      | ~ v1_funct_1(A_126)
      | ~ v1_relat_1(A_126) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_163])).

tff(c_908,plain,
    ( k6_partfun1(k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))))) = k5_relat_1(k2_funct_1(k2_funct_1('#skF_3')),k2_funct_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_702,c_853])).

tff(c_920,plain,(
    k5_relat_1(k2_funct_1(k2_funct_1('#skF_3')),k2_funct_1('#skF_3')) = k6_partfun1(k2_relat_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_600,c_479,c_598,c_450,c_702,c_313,c_702,c_448,c_702,c_702,c_908])).

tff(c_942,plain,
    ( k6_partfun1(k2_relat_1(k2_funct_1('#skF_3'))) = k5_relat_1('#skF_3',k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_920])).

tff(c_952,plain,(
    k6_partfun1(k2_relat_1(k2_funct_1('#skF_3'))) = k5_relat_1('#skF_3',k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_64,c_203,c_942])).

tff(c_956,plain,(
    k5_relat_1(k2_funct_1(k2_funct_1('#skF_3')),k2_funct_1('#skF_3')) = k5_relat_1('#skF_3',k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_952,c_920])).

tff(c_1062,plain,
    ( k6_partfun1(k1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))) = k5_relat_1('#skF_3',k2_funct_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1053,c_956])).

tff(c_1129,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_450,c_313,c_448,c_600,c_479,c_598,c_922,c_1062])).

tff(c_455,plain,(
    ! [A_112,C_108,E_110,B_109,D_113,F_111] :
      ( k1_partfun1(A_112,B_109,C_108,D_113,E_110,F_111) = k5_relat_1(E_110,F_111)
      | ~ m1_subset_1(F_111,k1_zfmisc_1(k2_zfmisc_1(C_108,D_113)))
      | ~ v1_funct_1(F_111)
      | ~ m1_subset_1(E_110,k1_zfmisc_1(k2_zfmisc_1(A_112,B_109)))
      | ~ v1_funct_1(E_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_457,plain,(
    ! [A_112,B_109,E_110] :
      ( k1_partfun1(A_112,B_109,'#skF_2','#skF_2',E_110,k2_funct_1('#skF_3')) = k5_relat_1(E_110,k2_funct_1('#skF_3'))
      | ~ v1_funct_1(k2_funct_1('#skF_3'))
      | ~ m1_subset_1(E_110,k1_zfmisc_1(k2_zfmisc_1(A_112,B_109)))
      | ~ v1_funct_1(E_110) ) ),
    inference(resolution,[status(thm)],[c_399,c_455])).

tff(c_2287,plain,(
    ! [A_173,B_174,E_175] :
      ( k1_partfun1(A_173,B_174,'#skF_2','#skF_2',E_175,k2_funct_1('#skF_3')) = k5_relat_1(E_175,k2_funct_1('#skF_3'))
      | ~ m1_subset_1(E_175,k1_zfmisc_1(k2_zfmisc_1(A_173,B_174)))
      | ~ v1_funct_1(E_175) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_313,c_457])).

tff(c_2320,plain,
    ( k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_1('#skF_3')) = k5_relat_1('#skF_3',k2_funct_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_2287])).

tff(c_2339,plain,(
    k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_1129,c_2320])).

tff(c_56,plain,
    ( ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_2('#skF_2','#skF_3'),'#skF_3'),k6_partfun1('#skF_2'))
    | ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_2('#skF_2','#skF_3')),k6_partfun1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_127,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_2('#skF_2','#skF_3')),k6_partfun1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_314,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_1('#skF_3')),k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_312,c_127])).

tff(c_2340,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k6_partfun1('#skF_2'),k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2339,c_314])).

tff(c_2343,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_243,c_2340])).

tff(c_2344,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_2('#skF_2','#skF_3'),'#skF_3'),k6_partfun1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_2534,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_1('#skF_3'),'#skF_3'),k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2532,c_2344])).

tff(c_3501,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k6_partfun1('#skF_2'),k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3337,c_2534])).

tff(c_3504,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2461,c_3501])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:35:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.36/2.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.36/2.30  
% 6.36/2.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.36/2.30  %$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 6.36/2.30  
% 6.36/2.30  %Foreground sorts:
% 6.36/2.30  
% 6.36/2.30  
% 6.36/2.30  %Background operators:
% 6.36/2.30  
% 6.36/2.30  
% 6.36/2.30  %Foreground operators:
% 6.36/2.30  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.36/2.30  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 6.36/2.30  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 6.36/2.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.36/2.30  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 6.36/2.30  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 6.36/2.30  tff(k2_funct_2, type, k2_funct_2: ($i * $i) > $i).
% 6.36/2.30  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.36/2.30  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.36/2.30  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.36/2.30  tff('#skF_2', type, '#skF_2': $i).
% 6.36/2.30  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 6.36/2.30  tff('#skF_3', type, '#skF_3': $i).
% 6.36/2.30  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 6.36/2.30  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 6.36/2.30  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 6.36/2.30  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.36/2.30  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 6.36/2.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.36/2.30  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.36/2.30  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.36/2.30  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 6.36/2.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.36/2.30  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 6.36/2.30  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 6.36/2.30  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.36/2.30  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.36/2.30  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.36/2.30  
% 6.68/2.33  tff(f_105, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 6.68/2.33  tff(f_116, axiom, (![A, B]: (?[C]: ((((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & v1_relat_1(C)) & v4_relat_1(C, A)) & v5_relat_1(C, B)) & v1_funct_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc1_partfun1)).
% 6.68/2.33  tff(f_73, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 6.68/2.33  tff(f_159, negated_conjecture, ~(![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, k2_funct_2(A, B)), k6_partfun1(A)) & r2_relset_1(A, A, k1_partfun1(A, A, A, A, k2_funct_2(A, B), B), k6_partfun1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_funct_2)).
% 6.68/2.33  tff(f_136, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k2_funct_2(A, B) = k2_funct_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 6.68/2.33  tff(f_101, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (((v1_funct_1(k2_funct_2(A, B)) & v1_funct_2(k2_funct_2(A, B), A, A)) & v3_funct_2(k2_funct_2(A, B), A, A)) & m1_subset_1(k2_funct_2(A, B), k1_zfmisc_1(k2_zfmisc_1(A, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_2)).
% 6.68/2.33  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 6.68/2.33  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_funct_2)).
% 6.68/2.33  tff(f_146, axiom, (![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k1_relset_1(A, A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_funct_2)).
% 6.68/2.33  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 6.68/2.33  tff(f_59, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(k2_funct_1(A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_1)).
% 6.68/2.33  tff(f_138, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 6.68/2.33  tff(f_43, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_1)).
% 6.68/2.33  tff(f_126, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 6.68/2.33  tff(c_36, plain, (![A_20]: (m1_subset_1(k6_partfun1(A_20), k1_zfmisc_1(k2_zfmisc_1(A_20, A_20))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 6.68/2.33  tff(c_46, plain, (![A_21, B_22]: (m1_subset_1('#skF_1'(A_21, B_22), k1_zfmisc_1(k2_zfmisc_1(A_21, B_22))))), inference(cnfTransformation, [status(thm)], [f_116])).
% 6.68/2.33  tff(c_2443, plain, (![A_196, B_197, C_198, D_199]: (r2_relset_1(A_196, B_197, C_198, C_198) | ~m1_subset_1(D_199, k1_zfmisc_1(k2_zfmisc_1(A_196, B_197))) | ~m1_subset_1(C_198, k1_zfmisc_1(k2_zfmisc_1(A_196, B_197))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.68/2.33  tff(c_2453, plain, (![A_200, B_201, C_202]: (r2_relset_1(A_200, B_201, C_202, C_202) | ~m1_subset_1(C_202, k1_zfmisc_1(k2_zfmisc_1(A_200, B_201))))), inference(resolution, [status(thm)], [c_46, c_2443])).
% 6.68/2.33  tff(c_2461, plain, (![A_20]: (r2_relset_1(A_20, A_20, k6_partfun1(A_20), k6_partfun1(A_20)))), inference(resolution, [status(thm)], [c_36, c_2453])).
% 6.68/2.33  tff(c_64, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_159])).
% 6.68/2.33  tff(c_62, plain, (v1_funct_2('#skF_3', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_159])).
% 6.68/2.33  tff(c_60, plain, (v3_funct_2('#skF_3', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_159])).
% 6.68/2.33  tff(c_58, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_159])).
% 6.68/2.33  tff(c_2515, plain, (![A_214, B_215]: (k2_funct_2(A_214, B_215)=k2_funct_1(B_215) | ~m1_subset_1(B_215, k1_zfmisc_1(k2_zfmisc_1(A_214, A_214))) | ~v3_funct_2(B_215, A_214, A_214) | ~v1_funct_2(B_215, A_214, A_214) | ~v1_funct_1(B_215))), inference(cnfTransformation, [status(thm)], [f_136])).
% 6.68/2.33  tff(c_2525, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_58, c_2515])).
% 6.68/2.33  tff(c_2532, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_2525])).
% 6.68/2.33  tff(c_2494, plain, (![A_209, B_210]: (v1_funct_1(k2_funct_2(A_209, B_210)) | ~m1_subset_1(B_210, k1_zfmisc_1(k2_zfmisc_1(A_209, A_209))) | ~v3_funct_2(B_210, A_209, A_209) | ~v1_funct_2(B_210, A_209, A_209) | ~v1_funct_1(B_210))), inference(cnfTransformation, [status(thm)], [f_101])).
% 6.68/2.33  tff(c_2504, plain, (v1_funct_1(k2_funct_2('#skF_2', '#skF_3')) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_58, c_2494])).
% 6.68/2.33  tff(c_2511, plain, (v1_funct_1(k2_funct_2('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_2504])).
% 6.68/2.33  tff(c_2533, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2532, c_2511])).
% 6.68/2.33  tff(c_85, plain, (![C_50, A_51, B_52]: (v1_relat_1(C_50) | ~m1_subset_1(C_50, k1_zfmisc_1(k2_zfmisc_1(A_51, B_52))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.68/2.33  tff(c_98, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_58, c_85])).
% 6.68/2.33  tff(c_2405, plain, (![C_184, A_185, B_186]: (v2_funct_1(C_184) | ~v3_funct_2(C_184, A_185, B_186) | ~v1_funct_1(C_184) | ~m1_subset_1(C_184, k1_zfmisc_1(k2_zfmisc_1(A_185, B_186))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 6.68/2.33  tff(c_2414, plain, (v2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_58, c_2405])).
% 6.68/2.33  tff(c_2421, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_60, c_2414])).
% 6.68/2.33  tff(c_2575, plain, (![A_225, B_226]: (m1_subset_1(k2_funct_2(A_225, B_226), k1_zfmisc_1(k2_zfmisc_1(A_225, A_225))) | ~m1_subset_1(B_226, k1_zfmisc_1(k2_zfmisc_1(A_225, A_225))) | ~v3_funct_2(B_226, A_225, A_225) | ~v1_funct_2(B_226, A_225, A_225) | ~v1_funct_1(B_226))), inference(cnfTransformation, [status(thm)], [f_101])).
% 6.68/2.33  tff(c_2605, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2532, c_2575])).
% 6.68/2.33  tff(c_2617, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_58, c_2605])).
% 6.68/2.33  tff(c_14, plain, (![C_7, A_5, B_6]: (v1_relat_1(C_7) | ~m1_subset_1(C_7, k1_zfmisc_1(k2_zfmisc_1(A_5, B_6))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.68/2.33  tff(c_2668, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_2617, c_14])).
% 6.68/2.33  tff(c_2558, plain, (![A_221, B_222]: (v3_funct_2(k2_funct_2(A_221, B_222), A_221, A_221) | ~m1_subset_1(B_222, k1_zfmisc_1(k2_zfmisc_1(A_221, A_221))) | ~v3_funct_2(B_222, A_221, A_221) | ~v1_funct_2(B_222, A_221, A_221) | ~v1_funct_1(B_222))), inference(cnfTransformation, [status(thm)], [f_101])).
% 6.68/2.33  tff(c_2565, plain, (v3_funct_2(k2_funct_2('#skF_2', '#skF_3'), '#skF_2', '#skF_2') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_58, c_2558])).
% 6.68/2.33  tff(c_2572, plain, (v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_2532, c_2565])).
% 6.68/2.33  tff(c_22, plain, (![C_17, A_15, B_16]: (v2_funct_1(C_17) | ~v3_funct_2(C_17, A_15, B_16) | ~v1_funct_1(C_17) | ~m1_subset_1(C_17, k1_zfmisc_1(k2_zfmisc_1(A_15, B_16))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 6.68/2.33  tff(c_2638, plain, (v2_funct_1(k2_funct_1('#skF_3')) | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_2617, c_22])).
% 6.68/2.33  tff(c_2666, plain, (v2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2533, c_2572, c_2638])).
% 6.68/2.33  tff(c_2542, plain, (![A_218, B_219]: (v1_funct_2(k2_funct_2(A_218, B_219), A_218, A_218) | ~m1_subset_1(B_219, k1_zfmisc_1(k2_zfmisc_1(A_218, A_218))) | ~v3_funct_2(B_219, A_218, A_218) | ~v1_funct_2(B_219, A_218, A_218) | ~v1_funct_1(B_219))), inference(cnfTransformation, [status(thm)], [f_101])).
% 6.68/2.33  tff(c_2549, plain, (v1_funct_2(k2_funct_2('#skF_2', '#skF_3'), '#skF_2', '#skF_2') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_58, c_2542])).
% 6.68/2.33  tff(c_2556, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_2532, c_2549])).
% 6.68/2.33  tff(c_54, plain, (![A_33, B_34]: (k1_relset_1(A_33, A_33, B_34)=A_33 | ~m1_subset_1(B_34, k1_zfmisc_1(k2_zfmisc_1(A_33, A_33))) | ~v1_funct_2(B_34, A_33, A_33) | ~v1_funct_1(B_34))), inference(cnfTransformation, [status(thm)], [f_146])).
% 6.68/2.33  tff(c_2630, plain, (k1_relset_1('#skF_2', '#skF_2', k2_funct_1('#skF_3'))='#skF_2' | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_2617, c_54])).
% 6.68/2.33  tff(c_2659, plain, (k1_relset_1('#skF_2', '#skF_2', k2_funct_1('#skF_3'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2533, c_2556, c_2630])).
% 6.68/2.33  tff(c_16, plain, (![A_8, B_9, C_10]: (k1_relset_1(A_8, B_9, C_10)=k1_relat_1(C_10) | ~m1_subset_1(C_10, k1_zfmisc_1(k2_zfmisc_1(A_8, B_9))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 6.68/2.33  tff(c_2667, plain, (k1_relset_1('#skF_2', '#skF_2', k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_2617, c_16])).
% 6.68/2.33  tff(c_2749, plain, (k1_relat_1(k2_funct_1('#skF_3'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2659, c_2667])).
% 6.68/2.33  tff(c_12, plain, (![A_4]: (k2_funct_1(k2_funct_1(A_4))=A_4 | ~v2_funct_1(A_4) | ~v1_funct_1(A_4) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.68/2.33  tff(c_52, plain, (![A_32]: (k6_relat_1(A_32)=k6_partfun1(A_32))), inference(cnfTransformation, [status(thm)], [f_138])).
% 6.68/2.33  tff(c_8, plain, (![A_2]: (k5_relat_1(A_2, k2_funct_1(A_2))=k6_relat_1(k1_relat_1(A_2)) | ~v2_funct_1(A_2) | ~v1_funct_1(A_2) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.68/2.33  tff(c_2363, plain, (![A_179]: (k5_relat_1(A_179, k2_funct_1(A_179))=k6_partfun1(k1_relat_1(A_179)) | ~v2_funct_1(A_179) | ~v1_funct_1(A_179) | ~v1_relat_1(A_179))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_8])).
% 6.68/2.33  tff(c_3220, plain, (![A_247]: (k6_partfun1(k1_relat_1(k2_funct_1(A_247)))=k5_relat_1(k2_funct_1(A_247), A_247) | ~v2_funct_1(k2_funct_1(A_247)) | ~v1_funct_1(k2_funct_1(A_247)) | ~v1_relat_1(k2_funct_1(A_247)) | ~v2_funct_1(A_247) | ~v1_funct_1(A_247) | ~v1_relat_1(A_247))), inference(superposition, [status(thm), theory('equality')], [c_12, c_2363])).
% 6.68/2.33  tff(c_3280, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2') | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2749, c_3220])).
% 6.68/2.33  tff(c_3294, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_98, c_64, c_2421, c_2668, c_2533, c_2666, c_3280])).
% 6.68/2.33  tff(c_26, plain, (![A_18, B_19]: (m1_subset_1(k2_funct_2(A_18, B_19), k1_zfmisc_1(k2_zfmisc_1(A_18, A_18))) | ~m1_subset_1(B_19, k1_zfmisc_1(k2_zfmisc_1(A_18, A_18))) | ~v3_funct_2(B_19, A_18, A_18) | ~v1_funct_2(B_19, A_18, A_18) | ~v1_funct_1(B_19))), inference(cnfTransformation, [status(thm)], [f_101])).
% 6.68/2.33  tff(c_2669, plain, (![C_227, D_232, E_229, B_228, F_230, A_231]: (k1_partfun1(A_231, B_228, C_227, D_232, E_229, F_230)=k5_relat_1(E_229, F_230) | ~m1_subset_1(F_230, k1_zfmisc_1(k2_zfmisc_1(C_227, D_232))) | ~v1_funct_1(F_230) | ~m1_subset_1(E_229, k1_zfmisc_1(k2_zfmisc_1(A_231, B_228))) | ~v1_funct_1(E_229))), inference(cnfTransformation, [status(thm)], [f_126])).
% 6.68/2.33  tff(c_2679, plain, (![A_231, B_228, E_229]: (k1_partfun1(A_231, B_228, '#skF_2', '#skF_2', E_229, '#skF_3')=k5_relat_1(E_229, '#skF_3') | ~v1_funct_1('#skF_3') | ~m1_subset_1(E_229, k1_zfmisc_1(k2_zfmisc_1(A_231, B_228))) | ~v1_funct_1(E_229))), inference(resolution, [status(thm)], [c_58, c_2669])).
% 6.68/2.33  tff(c_2705, plain, (![A_233, B_234, E_235]: (k1_partfun1(A_233, B_234, '#skF_2', '#skF_2', E_235, '#skF_3')=k5_relat_1(E_235, '#skF_3') | ~m1_subset_1(E_235, k1_zfmisc_1(k2_zfmisc_1(A_233, B_234))) | ~v1_funct_1(E_235))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_2679])).
% 6.68/2.33  tff(c_3310, plain, (![A_248, B_249]: (k1_partfun1(A_248, A_248, '#skF_2', '#skF_2', k2_funct_2(A_248, B_249), '#skF_3')=k5_relat_1(k2_funct_2(A_248, B_249), '#skF_3') | ~v1_funct_1(k2_funct_2(A_248, B_249)) | ~m1_subset_1(B_249, k1_zfmisc_1(k2_zfmisc_1(A_248, A_248))) | ~v3_funct_2(B_249, A_248, A_248) | ~v1_funct_2(B_249, A_248, A_248) | ~v1_funct_1(B_249))), inference(resolution, [status(thm)], [c_26, c_2705])).
% 6.68/2.33  tff(c_3323, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_2('#skF_2', '#skF_3'), '#skF_3')=k5_relat_1(k2_funct_2('#skF_2', '#skF_3'), '#skF_3') | ~v1_funct_1(k2_funct_2('#skF_2', '#skF_3')) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_58, c_3310])).
% 6.68/2.33  tff(c_3337, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_2533, c_2532, c_3294, c_2532, c_2532, c_3323])).
% 6.68/2.33  tff(c_225, plain, (![A_76, B_77, C_78, D_79]: (r2_relset_1(A_76, B_77, C_78, C_78) | ~m1_subset_1(D_79, k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))) | ~m1_subset_1(C_78, k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.68/2.33  tff(c_235, plain, (![A_80, B_81, C_82]: (r2_relset_1(A_80, B_81, C_82, C_82) | ~m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1(A_80, B_81))))), inference(resolution, [status(thm)], [c_46, c_225])).
% 6.68/2.33  tff(c_243, plain, (![A_20]: (r2_relset_1(A_20, A_20, k6_partfun1(A_20), k6_partfun1(A_20)))), inference(resolution, [status(thm)], [c_36, c_235])).
% 6.68/2.33  tff(c_295, plain, (![A_92, B_93]: (k2_funct_2(A_92, B_93)=k2_funct_1(B_93) | ~m1_subset_1(B_93, k1_zfmisc_1(k2_zfmisc_1(A_92, A_92))) | ~v3_funct_2(B_93, A_92, A_92) | ~v1_funct_2(B_93, A_92, A_92) | ~v1_funct_1(B_93))), inference(cnfTransformation, [status(thm)], [f_136])).
% 6.68/2.33  tff(c_305, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_58, c_295])).
% 6.68/2.33  tff(c_312, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_305])).
% 6.68/2.33  tff(c_357, plain, (![A_106, B_107]: (m1_subset_1(k2_funct_2(A_106, B_107), k1_zfmisc_1(k2_zfmisc_1(A_106, A_106))) | ~m1_subset_1(B_107, k1_zfmisc_1(k2_zfmisc_1(A_106, A_106))) | ~v3_funct_2(B_107, A_106, A_106) | ~v1_funct_2(B_107, A_106, A_106) | ~v1_funct_1(B_107))), inference(cnfTransformation, [status(thm)], [f_101])).
% 6.68/2.33  tff(c_387, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_312, c_357])).
% 6.68/2.33  tff(c_399, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_58, c_387])).
% 6.68/2.33  tff(c_450, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_399, c_14])).
% 6.68/2.33  tff(c_275, plain, (![A_88, B_89]: (v1_funct_1(k2_funct_2(A_88, B_89)) | ~m1_subset_1(B_89, k1_zfmisc_1(k2_zfmisc_1(A_88, A_88))) | ~v3_funct_2(B_89, A_88, A_88) | ~v1_funct_2(B_89, A_88, A_88) | ~v1_funct_1(B_89))), inference(cnfTransformation, [status(thm)], [f_101])).
% 6.68/2.33  tff(c_285, plain, (v1_funct_1(k2_funct_2('#skF_2', '#skF_3')) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_58, c_275])).
% 6.68/2.33  tff(c_292, plain, (v1_funct_1(k2_funct_2('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_285])).
% 6.68/2.33  tff(c_313, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_312, c_292])).
% 6.68/2.33  tff(c_321, plain, (![A_96, B_97]: (v3_funct_2(k2_funct_2(A_96, B_97), A_96, A_96) | ~m1_subset_1(B_97, k1_zfmisc_1(k2_zfmisc_1(A_96, A_96))) | ~v3_funct_2(B_97, A_96, A_96) | ~v1_funct_2(B_97, A_96, A_96) | ~v1_funct_1(B_97))), inference(cnfTransformation, [status(thm)], [f_101])).
% 6.68/2.33  tff(c_328, plain, (v3_funct_2(k2_funct_2('#skF_2', '#skF_3'), '#skF_2', '#skF_2') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_58, c_321])).
% 6.68/2.33  tff(c_335, plain, (v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_312, c_328])).
% 6.68/2.33  tff(c_420, plain, (v2_funct_1(k2_funct_1('#skF_3')) | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_399, c_22])).
% 6.68/2.33  tff(c_448, plain, (v2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_313, c_335, c_420])).
% 6.68/2.33  tff(c_338, plain, (![A_100, B_101]: (v1_funct_2(k2_funct_2(A_100, B_101), A_100, A_100) | ~m1_subset_1(B_101, k1_zfmisc_1(k2_zfmisc_1(A_100, A_100))) | ~v3_funct_2(B_101, A_100, A_100) | ~v1_funct_2(B_101, A_100, A_100) | ~v1_funct_1(B_101))), inference(cnfTransformation, [status(thm)], [f_101])).
% 6.68/2.33  tff(c_345, plain, (v1_funct_2(k2_funct_2('#skF_2', '#skF_3'), '#skF_2', '#skF_2') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_58, c_338])).
% 6.68/2.33  tff(c_352, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_312, c_345])).
% 6.68/2.33  tff(c_50, plain, (![A_30, B_31]: (k2_funct_2(A_30, B_31)=k2_funct_1(B_31) | ~m1_subset_1(B_31, k1_zfmisc_1(k2_zfmisc_1(A_30, A_30))) | ~v3_funct_2(B_31, A_30, A_30) | ~v1_funct_2(B_31, A_30, A_30) | ~v1_funct_1(B_31))), inference(cnfTransformation, [status(thm)], [f_136])).
% 6.68/2.33  tff(c_406, plain, (k2_funct_2('#skF_2', k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3')) | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_399, c_50])).
% 6.68/2.33  tff(c_435, plain, (k2_funct_2('#skF_2', k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_313, c_352, c_335, c_406])).
% 6.68/2.33  tff(c_483, plain, (m1_subset_1(k2_funct_1(k2_funct_1('#skF_3')), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_435, c_26])).
% 6.68/2.33  tff(c_487, plain, (m1_subset_1(k2_funct_1(k2_funct_1('#skF_3')), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_313, c_352, c_335, c_399, c_483])).
% 6.68/2.33  tff(c_600, plain, (v1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(resolution, [status(thm)], [c_487, c_14])).
% 6.68/2.33  tff(c_32, plain, (![A_18, B_19]: (v1_funct_1(k2_funct_2(A_18, B_19)) | ~m1_subset_1(B_19, k1_zfmisc_1(k2_zfmisc_1(A_18, A_18))) | ~v3_funct_2(B_19, A_18, A_18) | ~v1_funct_2(B_19, A_18, A_18) | ~v1_funct_1(B_19))), inference(cnfTransformation, [status(thm)], [f_101])).
% 6.68/2.33  tff(c_409, plain, (v1_funct_1(k2_funct_2('#skF_2', k2_funct_1('#skF_3'))) | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_399, c_32])).
% 6.68/2.33  tff(c_438, plain, (v1_funct_1(k2_funct_2('#skF_2', k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_313, c_352, c_335, c_409])).
% 6.68/2.33  tff(c_479, plain, (v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_435, c_438])).
% 6.68/2.33  tff(c_28, plain, (![A_18, B_19]: (v3_funct_2(k2_funct_2(A_18, B_19), A_18, A_18) | ~m1_subset_1(B_19, k1_zfmisc_1(k2_zfmisc_1(A_18, A_18))) | ~v3_funct_2(B_19, A_18, A_18) | ~v1_funct_2(B_19, A_18, A_18) | ~v1_funct_1(B_19))), inference(cnfTransformation, [status(thm)], [f_101])).
% 6.68/2.33  tff(c_403, plain, (v3_funct_2(k2_funct_2('#skF_2', k2_funct_1('#skF_3')), '#skF_2', '#skF_2') | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_399, c_28])).
% 6.68/2.33  tff(c_432, plain, (v3_funct_2(k2_funct_2('#skF_2', k2_funct_1('#skF_3')), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_313, c_352, c_335, c_403])).
% 6.68/2.33  tff(c_477, plain, (v3_funct_2(k2_funct_1(k2_funct_1('#skF_3')), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_435, c_432])).
% 6.68/2.33  tff(c_561, plain, (v2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v3_funct_2(k2_funct_1(k2_funct_1('#skF_3')), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(resolution, [status(thm)], [c_487, c_22])).
% 6.68/2.33  tff(c_598, plain, (v2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_479, c_477, c_561])).
% 6.68/2.33  tff(c_30, plain, (![A_18, B_19]: (v1_funct_2(k2_funct_2(A_18, B_19), A_18, A_18) | ~m1_subset_1(B_19, k1_zfmisc_1(k2_zfmisc_1(A_18, A_18))) | ~v3_funct_2(B_19, A_18, A_18) | ~v1_funct_2(B_19, A_18, A_18) | ~v1_funct_1(B_19))), inference(cnfTransformation, [status(thm)], [f_101])).
% 6.68/2.33  tff(c_401, plain, (v1_funct_2(k2_funct_2('#skF_2', k2_funct_1('#skF_3')), '#skF_2', '#skF_2') | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_399, c_30])).
% 6.68/2.33  tff(c_429, plain, (v1_funct_2(k2_funct_2('#skF_2', k2_funct_1('#skF_3')), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_313, c_352, c_335, c_401])).
% 6.68/2.33  tff(c_478, plain, (v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_435, c_429])).
% 6.68/2.33  tff(c_553, plain, (k1_relset_1('#skF_2', '#skF_2', k2_funct_1(k2_funct_1('#skF_3')))='#skF_2' | ~v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(resolution, [status(thm)], [c_487, c_54])).
% 6.68/2.33  tff(c_591, plain, (k1_relset_1('#skF_2', '#skF_2', k2_funct_1(k2_funct_1('#skF_3')))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_479, c_478, c_553])).
% 6.68/2.33  tff(c_599, plain, (k1_relset_1('#skF_2', '#skF_2', k2_funct_1(k2_funct_1('#skF_3')))=k1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(resolution, [status(thm)], [c_487, c_16])).
% 6.68/2.33  tff(c_922, plain, (k1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_591, c_599])).
% 6.68/2.33  tff(c_175, plain, (![A_63]: (k5_relat_1(A_63, k2_funct_1(A_63))=k6_partfun1(k1_relat_1(A_63)) | ~v2_funct_1(A_63) | ~v1_funct_1(A_63) | ~v1_relat_1(A_63))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_8])).
% 6.68/2.33  tff(c_1053, plain, (![A_128]: (k6_partfun1(k1_relat_1(k2_funct_1(A_128)))=k5_relat_1(k2_funct_1(A_128), A_128) | ~v2_funct_1(k2_funct_1(A_128)) | ~v1_funct_1(k2_funct_1(A_128)) | ~v1_relat_1(k2_funct_1(A_128)) | ~v2_funct_1(A_128) | ~v1_funct_1(A_128) | ~v1_relat_1(A_128))), inference(superposition, [status(thm), theory('equality')], [c_12, c_175])).
% 6.68/2.33  tff(c_187, plain, (![C_64, A_65, B_66]: (v2_funct_1(C_64) | ~v3_funct_2(C_64, A_65, B_66) | ~v1_funct_1(C_64) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 6.68/2.33  tff(c_196, plain, (v2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_58, c_187])).
% 6.68/2.33  tff(c_203, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_60, c_196])).
% 6.68/2.33  tff(c_547, plain, (k2_funct_2('#skF_2', k2_funct_1(k2_funct_1('#skF_3')))=k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v3_funct_2(k2_funct_1(k2_funct_1('#skF_3')), '#skF_2', '#skF_2') | ~v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(resolution, [status(thm)], [c_487, c_50])).
% 6.68/2.33  tff(c_585, plain, (k2_funct_2('#skF_2', k2_funct_1(k2_funct_1('#skF_3')))=k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_479, c_478, c_477, c_547])).
% 6.68/2.33  tff(c_696, plain, (k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))=k2_funct_2('#skF_2', '#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_12, c_585])).
% 6.68/2.33  tff(c_702, plain, (k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_98, c_64, c_203, c_312, c_696])).
% 6.68/2.33  tff(c_6, plain, (![A_2]: (k5_relat_1(k2_funct_1(A_2), A_2)=k6_relat_1(k2_relat_1(A_2)) | ~v2_funct_1(A_2) | ~v1_funct_1(A_2) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.68/2.33  tff(c_163, plain, (![A_62]: (k5_relat_1(k2_funct_1(A_62), A_62)=k6_partfun1(k2_relat_1(A_62)) | ~v2_funct_1(A_62) | ~v1_funct_1(A_62) | ~v1_relat_1(A_62))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_6])).
% 6.68/2.33  tff(c_853, plain, (![A_126]: (k6_partfun1(k2_relat_1(k2_funct_1(A_126)))=k5_relat_1(A_126, k2_funct_1(A_126)) | ~v2_funct_1(k2_funct_1(A_126)) | ~v1_funct_1(k2_funct_1(A_126)) | ~v1_relat_1(k2_funct_1(A_126)) | ~v2_funct_1(A_126) | ~v1_funct_1(A_126) | ~v1_relat_1(A_126))), inference(superposition, [status(thm), theory('equality')], [c_12, c_163])).
% 6.68/2.33  tff(c_908, plain, (k6_partfun1(k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))))=k5_relat_1(k2_funct_1(k2_funct_1('#skF_3')), k2_funct_1('#skF_3')) | ~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))) | ~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))) | ~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))) | ~v2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_702, c_853])).
% 6.68/2.33  tff(c_920, plain, (k5_relat_1(k2_funct_1(k2_funct_1('#skF_3')), k2_funct_1('#skF_3'))=k6_partfun1(k2_relat_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_600, c_479, c_598, c_450, c_702, c_313, c_702, c_448, c_702, c_702, c_908])).
% 6.68/2.33  tff(c_942, plain, (k6_partfun1(k2_relat_1(k2_funct_1('#skF_3')))=k5_relat_1('#skF_3', k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_12, c_920])).
% 6.68/2.33  tff(c_952, plain, (k6_partfun1(k2_relat_1(k2_funct_1('#skF_3')))=k5_relat_1('#skF_3', k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_64, c_203, c_942])).
% 6.68/2.33  tff(c_956, plain, (k5_relat_1(k2_funct_1(k2_funct_1('#skF_3')), k2_funct_1('#skF_3'))=k5_relat_1('#skF_3', k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_952, c_920])).
% 6.68/2.33  tff(c_1062, plain, (k6_partfun1(k1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))))=k5_relat_1('#skF_3', k2_funct_1('#skF_3')) | ~v2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1053, c_956])).
% 6.68/2.33  tff(c_1129, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_450, c_313, c_448, c_600, c_479, c_598, c_922, c_1062])).
% 6.68/2.33  tff(c_455, plain, (![A_112, C_108, E_110, B_109, D_113, F_111]: (k1_partfun1(A_112, B_109, C_108, D_113, E_110, F_111)=k5_relat_1(E_110, F_111) | ~m1_subset_1(F_111, k1_zfmisc_1(k2_zfmisc_1(C_108, D_113))) | ~v1_funct_1(F_111) | ~m1_subset_1(E_110, k1_zfmisc_1(k2_zfmisc_1(A_112, B_109))) | ~v1_funct_1(E_110))), inference(cnfTransformation, [status(thm)], [f_126])).
% 6.68/2.33  tff(c_457, plain, (![A_112, B_109, E_110]: (k1_partfun1(A_112, B_109, '#skF_2', '#skF_2', E_110, k2_funct_1('#skF_3'))=k5_relat_1(E_110, k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~m1_subset_1(E_110, k1_zfmisc_1(k2_zfmisc_1(A_112, B_109))) | ~v1_funct_1(E_110))), inference(resolution, [status(thm)], [c_399, c_455])).
% 6.68/2.33  tff(c_2287, plain, (![A_173, B_174, E_175]: (k1_partfun1(A_173, B_174, '#skF_2', '#skF_2', E_175, k2_funct_1('#skF_3'))=k5_relat_1(E_175, k2_funct_1('#skF_3')) | ~m1_subset_1(E_175, k1_zfmisc_1(k2_zfmisc_1(A_173, B_174))) | ~v1_funct_1(E_175))), inference(demodulation, [status(thm), theory('equality')], [c_313, c_457])).
% 6.68/2.33  tff(c_2320, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_1('#skF_3'))=k5_relat_1('#skF_3', k2_funct_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_58, c_2287])).
% 6.68/2.33  tff(c_2339, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_1129, c_2320])).
% 6.68/2.33  tff(c_56, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_2('#skF_2', '#skF_3'), '#skF_3'), k6_partfun1('#skF_2')) | ~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_2('#skF_2', '#skF_3')), k6_partfun1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_159])).
% 6.68/2.33  tff(c_127, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_2('#skF_2', '#skF_3')), k6_partfun1('#skF_2'))), inference(splitLeft, [status(thm)], [c_56])).
% 6.68/2.33  tff(c_314, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_1('#skF_3')), k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_312, c_127])).
% 6.68/2.33  tff(c_2340, plain, (~r2_relset_1('#skF_2', '#skF_2', k6_partfun1('#skF_2'), k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2339, c_314])).
% 6.68/2.33  tff(c_2343, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_243, c_2340])).
% 6.68/2.33  tff(c_2344, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_2('#skF_2', '#skF_3'), '#skF_3'), k6_partfun1('#skF_2'))), inference(splitRight, [status(thm)], [c_56])).
% 6.68/2.33  tff(c_2534, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_1('#skF_3'), '#skF_3'), k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2532, c_2344])).
% 6.68/2.33  tff(c_3501, plain, (~r2_relset_1('#skF_2', '#skF_2', k6_partfun1('#skF_2'), k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_3337, c_2534])).
% 6.68/2.33  tff(c_3504, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2461, c_3501])).
% 6.68/2.33  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.68/2.33  
% 6.68/2.33  Inference rules
% 6.68/2.33  ----------------------
% 6.68/2.33  #Ref     : 0
% 6.68/2.33  #Sup     : 820
% 6.68/2.33  #Fact    : 0
% 6.68/2.33  #Define  : 0
% 6.68/2.33  #Split   : 2
% 6.68/2.33  #Chain   : 0
% 6.68/2.33  #Close   : 0
% 6.68/2.33  
% 6.68/2.33  Ordering : KBO
% 6.68/2.33  
% 6.68/2.33  Simplification rules
% 6.68/2.33  ----------------------
% 6.68/2.33  #Subsume      : 84
% 6.68/2.33  #Demod        : 1580
% 6.68/2.33  #Tautology    : 350
% 6.68/2.33  #SimpNegUnit  : 0
% 6.68/2.33  #BackRed      : 35
% 6.68/2.33  
% 6.68/2.33  #Partial instantiations: 0
% 6.68/2.33  #Strategies tried      : 1
% 6.68/2.33  
% 6.68/2.33  Timing (in seconds)
% 6.68/2.33  ----------------------
% 6.68/2.34  Preprocessing        : 0.43
% 6.68/2.34  Parsing              : 0.21
% 6.68/2.34  CNF conversion       : 0.04
% 6.68/2.34  Main loop            : 1.10
% 6.68/2.34  Inferencing          : 0.39
% 6.68/2.34  Reduction            : 0.42
% 6.68/2.34  Demodulation         : 0.33
% 6.68/2.34  BG Simplification    : 0.05
% 6.68/2.34  Subsumption          : 0.17
% 6.68/2.34  Abstraction          : 0.05
% 6.68/2.34  MUC search           : 0.00
% 6.68/2.34  Cooper               : 0.00
% 6.68/2.34  Total                : 1.59
% 6.68/2.34  Index Insertion      : 0.00
% 6.68/2.34  Index Deletion       : 0.00
% 6.68/2.34  Index Matching       : 0.00
% 6.68/2.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
