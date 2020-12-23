%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:08 EST 2020

% Result     : Theorem 5.65s
% Output     : CNFRefutation 5.81s
% Verified   : 
% Statistics : Number of formulae       :  192 (6949 expanded)
%              Number of leaves         :   42 (2812 expanded)
%              Depth                    :   21
%              Number of atoms          :  439 (25426 expanded)
%              Number of equality atoms :   66 (1291 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   2 average)

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

tff(f_101,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_114,axiom,(
    ! [A,B] :
    ? [C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
      & v1_relat_1(C)
      & v4_relat_1(C,A)
      & v5_relat_1(C,B)
      & v1_funct_1(C)
      & v1_funct_2(C,A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_funct_2)).

tff(f_69,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(f_157,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & v3_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ( r2_relset_1(A,A,k1_partfun1(A,A,A,A,B,k2_funct_2(A,B)),k6_partfun1(A))
          & r2_relset_1(A,A,k1_partfun1(A,A,A,A,k2_funct_2(A,B),B),k6_partfun1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_funct_2)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_55,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(k2_funct_1(A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).

tff(f_134,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k2_funct_2(A,B) = k2_funct_1(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

tff(f_97,axiom,(
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

tff(f_144,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k1_relset_1(A,A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_2)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_136,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_47,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_124,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(c_36,plain,(
    ! [A_19] : m1_subset_1(k6_partfun1(A_19),k1_zfmisc_1(k2_zfmisc_1(A_19,A_19))) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_48,plain,(
    ! [A_20,B_21] : m1_subset_1('#skF_1'(A_20,B_21),k1_zfmisc_1(k2_zfmisc_1(A_20,B_21))) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_2364,plain,(
    ! [A_201,B_202,C_203,D_204] :
      ( r2_relset_1(A_201,B_202,C_203,C_203)
      | ~ m1_subset_1(D_204,k1_zfmisc_1(k2_zfmisc_1(A_201,B_202)))
      | ~ m1_subset_1(C_203,k1_zfmisc_1(k2_zfmisc_1(A_201,B_202))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_2404,plain,(
    ! [A_208,B_209,C_210] :
      ( r2_relset_1(A_208,B_209,C_210,C_210)
      | ~ m1_subset_1(C_210,k1_zfmisc_1(k2_zfmisc_1(A_208,B_209))) ) ),
    inference(resolution,[status(thm)],[c_48,c_2364])).

tff(c_2412,plain,(
    ! [A_19] : r2_relset_1(A_19,A_19,k6_partfun1(A_19),k6_partfun1(A_19)) ),
    inference(resolution,[status(thm)],[c_36,c_2404])).

tff(c_60,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_86,plain,(
    ! [C_49,A_50,B_51] :
      ( v1_relat_1(C_49)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(k2_zfmisc_1(A_50,B_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_99,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_86])).

tff(c_66,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_62,plain,(
    v3_funct_2('#skF_3','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_2288,plain,(
    ! [C_185,A_186,B_187] :
      ( v2_funct_1(C_185)
      | ~ v3_funct_2(C_185,A_186,B_187)
      | ~ v1_funct_1(C_185)
      | ~ m1_subset_1(C_185,k1_zfmisc_1(k2_zfmisc_1(A_186,B_187))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_2297,plain,
    ( v2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_2288])).

tff(c_2304,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_62,c_2297])).

tff(c_12,plain,(
    ! [A_3] :
      ( k2_funct_1(k2_funct_1(A_3)) = A_3
      | ~ v2_funct_1(A_3)
      | ~ v1_funct_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_64,plain,(
    v1_funct_2('#skF_3','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_2419,plain,(
    ! [A_214,B_215] :
      ( k2_funct_2(A_214,B_215) = k2_funct_1(B_215)
      | ~ m1_subset_1(B_215,k1_zfmisc_1(k2_zfmisc_1(A_214,A_214)))
      | ~ v3_funct_2(B_215,A_214,A_214)
      | ~ v1_funct_2(B_215,A_214,A_214)
      | ~ v1_funct_1(B_215) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_2429,plain,
    ( k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_2419])).

tff(c_2436,plain,(
    k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_2429])).

tff(c_2479,plain,(
    ! [A_225,B_226] :
      ( m1_subset_1(k2_funct_2(A_225,B_226),k1_zfmisc_1(k2_zfmisc_1(A_225,A_225)))
      | ~ m1_subset_1(B_226,k1_zfmisc_1(k2_zfmisc_1(A_225,A_225)))
      | ~ v3_funct_2(B_226,A_225,A_225)
      | ~ v1_funct_2(B_226,A_225,A_225)
      | ~ v1_funct_1(B_226) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_2509,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2436,c_2479])).

tff(c_2521,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_60,c_2509])).

tff(c_14,plain,(
    ! [C_6,A_4,B_5] :
      ( v1_relat_1(C_6)
      | ~ m1_subset_1(C_6,k1_zfmisc_1(k2_zfmisc_1(A_4,B_5))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_2572,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2521,c_14])).

tff(c_2374,plain,(
    ! [A_205,B_206] :
      ( v1_funct_1(k2_funct_2(A_205,B_206))
      | ~ m1_subset_1(B_206,k1_zfmisc_1(k2_zfmisc_1(A_205,A_205)))
      | ~ v3_funct_2(B_206,A_205,A_205)
      | ~ v1_funct_2(B_206,A_205,A_205)
      | ~ v1_funct_1(B_206) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_2384,plain,
    ( v1_funct_1(k2_funct_2('#skF_2','#skF_3'))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_2374])).

tff(c_2391,plain,(
    v1_funct_1(k2_funct_2('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_2384])).

tff(c_2437,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2436,c_2391])).

tff(c_2463,plain,(
    ! [A_222,B_223] :
      ( v3_funct_2(k2_funct_2(A_222,B_223),A_222,A_222)
      | ~ m1_subset_1(B_223,k1_zfmisc_1(k2_zfmisc_1(A_222,A_222)))
      | ~ v3_funct_2(B_223,A_222,A_222)
      | ~ v1_funct_2(B_223,A_222,A_222)
      | ~ v1_funct_1(B_223) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_2470,plain,
    ( v3_funct_2(k2_funct_2('#skF_2','#skF_3'),'#skF_2','#skF_2')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_2463])).

tff(c_2477,plain,(
    v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_2436,c_2470])).

tff(c_22,plain,(
    ! [C_16,A_14,B_15] :
      ( v2_funct_1(C_16)
      | ~ v3_funct_2(C_16,A_14,B_15)
      | ~ v1_funct_1(C_16)
      | ~ m1_subset_1(C_16,k1_zfmisc_1(k2_zfmisc_1(A_14,B_15))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_2542,plain,
    ( v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2521,c_22])).

tff(c_2570,plain,(
    v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2437,c_2477,c_2542])).

tff(c_2448,plain,(
    ! [A_220,B_221] :
      ( v1_funct_2(k2_funct_2(A_220,B_221),A_220,A_220)
      | ~ m1_subset_1(B_221,k1_zfmisc_1(k2_zfmisc_1(A_220,A_220)))
      | ~ v3_funct_2(B_221,A_220,A_220)
      | ~ v1_funct_2(B_221,A_220,A_220)
      | ~ v1_funct_1(B_221) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_2455,plain,
    ( v1_funct_2(k2_funct_2('#skF_2','#skF_3'),'#skF_2','#skF_2')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_2448])).

tff(c_2462,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_2436,c_2455])).

tff(c_56,plain,(
    ! [A_32,B_33] :
      ( k1_relset_1(A_32,A_32,B_33) = A_32
      | ~ m1_subset_1(B_33,k1_zfmisc_1(k2_zfmisc_1(A_32,A_32)))
      | ~ v1_funct_2(B_33,A_32,A_32)
      | ~ v1_funct_1(B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_2536,plain,
    ( k1_relset_1('#skF_2','#skF_2',k2_funct_1('#skF_3')) = '#skF_2'
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2521,c_56])).

tff(c_2564,plain,(
    k1_relset_1('#skF_2','#skF_2',k2_funct_1('#skF_3')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2437,c_2462,c_2536])).

tff(c_16,plain,(
    ! [A_7,B_8,C_9] :
      ( k1_relset_1(A_7,B_8,C_9) = k1_relat_1(C_9)
      | ~ m1_subset_1(C_9,k1_zfmisc_1(k2_zfmisc_1(A_7,B_8))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2571,plain,(
    k1_relset_1('#skF_2','#skF_2',k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2521,c_16])).

tff(c_2653,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2564,c_2571])).

tff(c_52,plain,(
    ! [A_29,B_30] :
      ( k2_funct_2(A_29,B_30) = k2_funct_1(B_30)
      | ~ m1_subset_1(B_30,k1_zfmisc_1(k2_zfmisc_1(A_29,A_29)))
      | ~ v3_funct_2(B_30,A_29,A_29)
      | ~ v1_funct_2(B_30,A_29,A_29)
      | ~ v1_funct_1(B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_2528,plain,
    ( k2_funct_2('#skF_2',k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3'))
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2521,c_52])).

tff(c_2557,plain,(
    k2_funct_2('#skF_2',k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2437,c_2462,c_2477,c_2528])).

tff(c_26,plain,(
    ! [A_17,B_18] :
      ( m1_subset_1(k2_funct_2(A_17,B_18),k1_zfmisc_1(k2_zfmisc_1(A_17,A_17)))
      | ~ m1_subset_1(B_18,k1_zfmisc_1(k2_zfmisc_1(A_17,A_17)))
      | ~ v3_funct_2(B_18,A_17,A_17)
      | ~ v1_funct_2(B_18,A_17,A_17)
      | ~ v1_funct_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_2631,plain,
    ( m1_subset_1(k2_funct_1(k2_funct_1('#skF_3')),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2557,c_26])).

tff(c_2635,plain,(
    m1_subset_1(k2_funct_1(k2_funct_1('#skF_3')),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2437,c_2462,c_2477,c_2521,c_2631])).

tff(c_2723,plain,(
    v1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_2635,c_14])).

tff(c_32,plain,(
    ! [A_17,B_18] :
      ( v1_funct_1(k2_funct_2(A_17,B_18))
      | ~ m1_subset_1(B_18,k1_zfmisc_1(k2_zfmisc_1(A_17,A_17)))
      | ~ v3_funct_2(B_18,A_17,A_17)
      | ~ v1_funct_2(B_18,A_17,A_17)
      | ~ v1_funct_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_2533,plain,
    ( v1_funct_1(k2_funct_2('#skF_2',k2_funct_1('#skF_3')))
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2521,c_32])).

tff(c_2561,plain,(
    v1_funct_1(k2_funct_2('#skF_2',k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2437,c_2462,c_2477,c_2533])).

tff(c_2627,plain,(
    v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2557,c_2561])).

tff(c_28,plain,(
    ! [A_17,B_18] :
      ( v3_funct_2(k2_funct_2(A_17,B_18),A_17,A_17)
      | ~ m1_subset_1(B_18,k1_zfmisc_1(k2_zfmisc_1(A_17,A_17)))
      | ~ v3_funct_2(B_18,A_17,A_17)
      | ~ v1_funct_2(B_18,A_17,A_17)
      | ~ v1_funct_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_2523,plain,
    ( v3_funct_2(k2_funct_2('#skF_2',k2_funct_1('#skF_3')),'#skF_2','#skF_2')
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2521,c_28])).

tff(c_2551,plain,(
    v3_funct_2(k2_funct_2('#skF_2',k2_funct_1('#skF_3')),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2437,c_2462,c_2477,c_2523])).

tff(c_2626,plain,(
    v3_funct_2(k2_funct_1(k2_funct_1('#skF_3')),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2557,c_2551])).

tff(c_2684,plain,
    ( v2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v3_funct_2(k2_funct_1(k2_funct_1('#skF_3')),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_2635,c_22])).

tff(c_2721,plain,(
    v2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2627,c_2626,c_2684])).

tff(c_30,plain,(
    ! [A_17,B_18] :
      ( v1_funct_2(k2_funct_2(A_17,B_18),A_17,A_17)
      | ~ m1_subset_1(B_18,k1_zfmisc_1(k2_zfmisc_1(A_17,A_17)))
      | ~ v3_funct_2(B_18,A_17,A_17)
      | ~ v1_funct_2(B_18,A_17,A_17)
      | ~ v1_funct_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_2525,plain,
    ( v1_funct_2(k2_funct_2('#skF_2',k2_funct_1('#skF_3')),'#skF_2','#skF_2')
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2521,c_30])).

tff(c_2554,plain,(
    v1_funct_2(k2_funct_2('#skF_2',k2_funct_1('#skF_3')),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2437,c_2462,c_2477,c_2525])).

tff(c_2647,plain,(
    v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2557,c_2554])).

tff(c_2670,plain,
    ( k2_funct_2('#skF_2',k2_funct_1(k2_funct_1('#skF_3'))) = k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v3_funct_2(k2_funct_1(k2_funct_1('#skF_3')),'#skF_2','#skF_2')
    | ~ v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_2635,c_52])).

tff(c_2708,plain,(
    k2_funct_2('#skF_2',k2_funct_1(k2_funct_1('#skF_3'))) = k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2627,c_2647,c_2626,c_2670])).

tff(c_2780,plain,
    ( k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) = k2_funct_2('#skF_2','#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_2708])).

tff(c_2786,plain,(
    k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_66,c_2304,c_2436,c_2780])).

tff(c_54,plain,(
    ! [A_31] : k6_relat_1(A_31) = k6_partfun1(A_31) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_8,plain,(
    ! [A_2] :
      ( k5_relat_1(k2_funct_1(A_2),A_2) = k6_relat_1(k2_relat_1(A_2))
      | ~ v2_funct_1(A_2)
      | ~ v1_funct_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_68,plain,(
    ! [A_2] :
      ( k5_relat_1(k2_funct_1(A_2),A_2) = k6_partfun1(k2_relat_1(A_2))
      | ~ v2_funct_1(A_2)
      | ~ v1_funct_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_8])).

tff(c_2803,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),k2_funct_1(k2_funct_1('#skF_3'))) = k6_partfun1(k2_relat_1(k2_funct_1(k2_funct_1('#skF_3'))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2786,c_68])).

tff(c_2831,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),k2_funct_1(k2_funct_1('#skF_3'))) = k6_partfun1(k2_relat_1(k2_funct_1(k2_funct_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2723,c_2627,c_2721,c_2803])).

tff(c_10,plain,(
    ! [A_2] :
      ( k5_relat_1(A_2,k2_funct_1(A_2)) = k6_relat_1(k1_relat_1(A_2))
      | ~ v2_funct_1(A_2)
      | ~ v1_funct_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_67,plain,(
    ! [A_2] :
      ( k5_relat_1(A_2,k2_funct_1(A_2)) = k6_partfun1(k1_relat_1(A_2))
      | ~ v2_funct_1(A_2)
      | ~ v1_funct_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_10])).

tff(c_3057,plain,
    ( k6_partfun1(k2_relat_1(k2_funct_1(k2_funct_1('#skF_3')))) = k6_partfun1(k1_relat_1(k2_funct_1('#skF_3')))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2831,c_67])).

tff(c_3067,plain,(
    k6_partfun1(k2_relat_1(k2_funct_1(k2_funct_1('#skF_3')))) = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2572,c_2437,c_2570,c_2653,c_3057])).

tff(c_3073,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),k2_funct_1(k2_funct_1('#skF_3'))) = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3067,c_2831])).

tff(c_3210,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_3073])).

tff(c_3218,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_66,c_2304,c_3210])).

tff(c_2573,plain,(
    ! [D_231,C_227,F_228,A_232,E_229,B_230] :
      ( k1_partfun1(A_232,B_230,C_227,D_231,E_229,F_228) = k5_relat_1(E_229,F_228)
      | ~ m1_subset_1(F_228,k1_zfmisc_1(k2_zfmisc_1(C_227,D_231)))
      | ~ v1_funct_1(F_228)
      | ~ m1_subset_1(E_229,k1_zfmisc_1(k2_zfmisc_1(A_232,B_230)))
      | ~ v1_funct_1(E_229) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_2583,plain,(
    ! [A_232,B_230,E_229] :
      ( k1_partfun1(A_232,B_230,'#skF_2','#skF_2',E_229,'#skF_3') = k5_relat_1(E_229,'#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(E_229,k1_zfmisc_1(k2_zfmisc_1(A_232,B_230)))
      | ~ v1_funct_1(E_229) ) ),
    inference(resolution,[status(thm)],[c_60,c_2573])).

tff(c_2599,plain,(
    ! [A_233,B_234,E_235] :
      ( k1_partfun1(A_233,B_234,'#skF_2','#skF_2',E_235,'#skF_3') = k5_relat_1(E_235,'#skF_3')
      | ~ m1_subset_1(E_235,k1_zfmisc_1(k2_zfmisc_1(A_233,B_234)))
      | ~ v1_funct_1(E_235) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_2583])).

tff(c_2902,plain,(
    ! [A_240,B_241] :
      ( k1_partfun1(A_240,A_240,'#skF_2','#skF_2',k2_funct_2(A_240,B_241),'#skF_3') = k5_relat_1(k2_funct_2(A_240,B_241),'#skF_3')
      | ~ v1_funct_1(k2_funct_2(A_240,B_241))
      | ~ m1_subset_1(B_241,k1_zfmisc_1(k2_zfmisc_1(A_240,A_240)))
      | ~ v3_funct_2(B_241,A_240,A_240)
      | ~ v1_funct_2(B_241,A_240,A_240)
      | ~ v1_funct_1(B_241) ) ),
    inference(resolution,[status(thm)],[c_26,c_2599])).

tff(c_2915,plain,
    ( k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_2('#skF_2','#skF_3'),'#skF_3') = k5_relat_1(k2_funct_2('#skF_2','#skF_3'),'#skF_3')
    | ~ v1_funct_1(k2_funct_2('#skF_2','#skF_3'))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_2902])).

tff(c_2929,plain,(
    k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_1('#skF_3'),'#skF_3') = k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_2437,c_2436,c_2436,c_2436,c_2915])).

tff(c_227,plain,(
    ! [A_76,B_77,C_78,D_79] :
      ( r2_relset_1(A_76,B_77,C_78,C_78)
      | ~ m1_subset_1(D_79,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77)))
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_237,plain,(
    ! [A_80,B_81,C_82] :
      ( r2_relset_1(A_80,B_81,C_82,C_82)
      | ~ m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1(A_80,B_81))) ) ),
    inference(resolution,[status(thm)],[c_48,c_227])).

tff(c_245,plain,(
    ! [A_19] : r2_relset_1(A_19,A_19,k6_partfun1(A_19),k6_partfun1(A_19)) ),
    inference(resolution,[status(thm)],[c_36,c_237])).

tff(c_190,plain,(
    ! [C_65,A_66,B_67] :
      ( v2_funct_1(C_65)
      | ~ v3_funct_2(C_65,A_66,B_67)
      | ~ v1_funct_1(C_65)
      | ~ m1_subset_1(C_65,k1_zfmisc_1(k2_zfmisc_1(A_66,B_67))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_199,plain,
    ( v2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_190])).

tff(c_206,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_62,c_199])).

tff(c_305,plain,(
    ! [A_92,B_93] :
      ( k2_funct_2(A_92,B_93) = k2_funct_1(B_93)
      | ~ m1_subset_1(B_93,k1_zfmisc_1(k2_zfmisc_1(A_92,A_92)))
      | ~ v3_funct_2(B_93,A_92,A_92)
      | ~ v1_funct_2(B_93,A_92,A_92)
      | ~ v1_funct_1(B_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_315,plain,
    ( k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_305])).

tff(c_322,plain,(
    k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_315])).

tff(c_274,plain,(
    ! [A_89,B_90] :
      ( v1_funct_1(k2_funct_2(A_89,B_90))
      | ~ m1_subset_1(B_90,k1_zfmisc_1(k2_zfmisc_1(A_89,A_89)))
      | ~ v3_funct_2(B_90,A_89,A_89)
      | ~ v1_funct_2(B_90,A_89,A_89)
      | ~ v1_funct_1(B_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_284,plain,
    ( v1_funct_1(k2_funct_2('#skF_2','#skF_3'))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_274])).

tff(c_291,plain,(
    v1_funct_1(k2_funct_2('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_284])).

tff(c_323,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_322,c_291])).

tff(c_348,plain,(
    ! [A_100,B_101] :
      ( v1_funct_2(k2_funct_2(A_100,B_101),A_100,A_100)
      | ~ m1_subset_1(B_101,k1_zfmisc_1(k2_zfmisc_1(A_100,A_100)))
      | ~ v3_funct_2(B_101,A_100,A_100)
      | ~ v1_funct_2(B_101,A_100,A_100)
      | ~ v1_funct_1(B_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_355,plain,
    ( v1_funct_2(k2_funct_2('#skF_2','#skF_3'),'#skF_2','#skF_2')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_348])).

tff(c_362,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_322,c_355])).

tff(c_331,plain,(
    ! [A_96,B_97] :
      ( v3_funct_2(k2_funct_2(A_96,B_97),A_96,A_96)
      | ~ m1_subset_1(B_97,k1_zfmisc_1(k2_zfmisc_1(A_96,A_96)))
      | ~ v3_funct_2(B_97,A_96,A_96)
      | ~ v1_funct_2(B_97,A_96,A_96)
      | ~ v1_funct_1(B_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_338,plain,
    ( v3_funct_2(k2_funct_2('#skF_2','#skF_3'),'#skF_2','#skF_2')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_331])).

tff(c_345,plain,(
    v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_322,c_338])).

tff(c_367,plain,(
    ! [A_106,B_107] :
      ( m1_subset_1(k2_funct_2(A_106,B_107),k1_zfmisc_1(k2_zfmisc_1(A_106,A_106)))
      | ~ m1_subset_1(B_107,k1_zfmisc_1(k2_zfmisc_1(A_106,A_106)))
      | ~ v3_funct_2(B_107,A_106,A_106)
      | ~ v1_funct_2(B_107,A_106,A_106)
      | ~ v1_funct_1(B_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_397,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_322,c_367])).

tff(c_409,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_60,c_397])).

tff(c_416,plain,
    ( k2_funct_2('#skF_2',k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3'))
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_409,c_52])).

tff(c_445,plain,(
    k2_funct_2('#skF_2',k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_323,c_362,c_345,c_416])).

tff(c_419,plain,
    ( v1_funct_1(k2_funct_2('#skF_2',k2_funct_1('#skF_3')))
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_409,c_32])).

tff(c_448,plain,(
    v1_funct_1(k2_funct_2('#skF_2',k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_323,c_362,c_345,c_419])).

tff(c_489,plain,(
    v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_445,c_448])).

tff(c_411,plain,
    ( v1_funct_2(k2_funct_2('#skF_2',k2_funct_1('#skF_3')),'#skF_2','#skF_2')
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_409,c_30])).

tff(c_439,plain,(
    v1_funct_2(k2_funct_2('#skF_2',k2_funct_1('#skF_3')),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_323,c_362,c_345,c_411])).

tff(c_487,plain,(
    v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_445,c_439])).

tff(c_493,plain,
    ( m1_subset_1(k2_funct_1(k2_funct_1('#skF_3')),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_445,c_26])).

tff(c_497,plain,(
    m1_subset_1(k2_funct_1(k2_funct_1('#skF_3')),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_323,c_362,c_345,c_409,c_493])).

tff(c_563,plain,
    ( k1_relset_1('#skF_2','#skF_2',k2_funct_1(k2_funct_1('#skF_3'))) = '#skF_2'
    | ~ v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_497,c_56])).

tff(c_601,plain,(
    k1_relset_1('#skF_2','#skF_2',k2_funct_1(k2_funct_1('#skF_3'))) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_489,c_487,c_563])).

tff(c_609,plain,(
    k1_relset_1('#skF_2','#skF_2',k2_funct_1(k2_funct_1('#skF_3'))) = k1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_497,c_16])).

tff(c_857,plain,(
    k1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_601,c_609])).

tff(c_610,plain,(
    v1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_497,c_14])).

tff(c_413,plain,
    ( v3_funct_2(k2_funct_2('#skF_2',k2_funct_1('#skF_3')),'#skF_2','#skF_2')
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_409,c_28])).

tff(c_442,plain,(
    v3_funct_2(k2_funct_2('#skF_2',k2_funct_1('#skF_3')),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_323,c_362,c_345,c_413])).

tff(c_488,plain,(
    v3_funct_2(k2_funct_1(k2_funct_1('#skF_3')),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_445,c_442])).

tff(c_571,plain,
    ( v2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v3_funct_2(k2_funct_1(k2_funct_1('#skF_3')),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_497,c_22])).

tff(c_608,plain,(
    v2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_489,c_488,c_571])).

tff(c_557,plain,
    ( k2_funct_2('#skF_2',k2_funct_1(k2_funct_1('#skF_3'))) = k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v3_funct_2(k2_funct_1(k2_funct_1('#skF_3')),'#skF_2','#skF_2')
    | ~ v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_497,c_52])).

tff(c_595,plain,(
    k2_funct_2('#skF_2',k2_funct_1(k2_funct_1('#skF_3'))) = k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_489,c_487,c_488,c_557])).

tff(c_727,plain,
    ( k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) = k2_funct_2('#skF_2','#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_595])).

tff(c_733,plain,(
    k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_66,c_206,c_322,c_727])).

tff(c_763,plain,
    ( k5_relat_1(k2_funct_1(k2_funct_1('#skF_3')),k2_funct_1('#skF_3')) = k6_partfun1(k1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_733,c_67])).

tff(c_791,plain,(
    k5_relat_1(k2_funct_1(k2_funct_1('#skF_3')),k2_funct_1('#skF_3')) = k6_partfun1(k1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_610,c_489,c_608,c_763])).

tff(c_1232,plain,(
    k5_relat_1(k2_funct_1(k2_funct_1('#skF_3')),k2_funct_1('#skF_3')) = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_857,c_791])).

tff(c_1249,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_1232])).

tff(c_1261,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_66,c_206,c_1249])).

tff(c_465,plain,(
    ! [B_111,A_113,C_108,D_112,F_109,E_110] :
      ( k1_partfun1(A_113,B_111,C_108,D_112,E_110,F_109) = k5_relat_1(E_110,F_109)
      | ~ m1_subset_1(F_109,k1_zfmisc_1(k2_zfmisc_1(C_108,D_112)))
      | ~ v1_funct_1(F_109)
      | ~ m1_subset_1(E_110,k1_zfmisc_1(k2_zfmisc_1(A_113,B_111)))
      | ~ v1_funct_1(E_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_467,plain,(
    ! [A_113,B_111,E_110] :
      ( k1_partfun1(A_113,B_111,'#skF_2','#skF_2',E_110,k2_funct_1('#skF_3')) = k5_relat_1(E_110,k2_funct_1('#skF_3'))
      | ~ v1_funct_1(k2_funct_1('#skF_3'))
      | ~ m1_subset_1(E_110,k1_zfmisc_1(k2_zfmisc_1(A_113,B_111)))
      | ~ v1_funct_1(E_110) ) ),
    inference(resolution,[status(thm)],[c_409,c_465])).

tff(c_2144,plain,(
    ! [A_173,B_174,E_175] :
      ( k1_partfun1(A_173,B_174,'#skF_2','#skF_2',E_175,k2_funct_1('#skF_3')) = k5_relat_1(E_175,k2_funct_1('#skF_3'))
      | ~ m1_subset_1(E_175,k1_zfmisc_1(k2_zfmisc_1(A_173,B_174)))
      | ~ v1_funct_1(E_175) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_323,c_467])).

tff(c_2177,plain,
    ( k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_1('#skF_3')) = k5_relat_1('#skF_3',k2_funct_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_2144])).

tff(c_2196,plain,(
    k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1261,c_2177])).

tff(c_58,plain,
    ( ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_2('#skF_2','#skF_3'),'#skF_3'),k6_partfun1('#skF_2'))
    | ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_2('#skF_2','#skF_3')),k6_partfun1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_104,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_2('#skF_2','#skF_3')),k6_partfun1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_324,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_1('#skF_3')),k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_322,c_104])).

tff(c_2197,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k6_partfun1('#skF_2'),k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2196,c_324])).

tff(c_2200,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_245,c_2197])).

tff(c_2201,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_2('#skF_2','#skF_3'),'#skF_3'),k6_partfun1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_2438,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_1('#skF_3'),'#skF_3'),k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2436,c_2201])).

tff(c_3189,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k5_relat_1(k2_funct_1('#skF_3'),'#skF_3'),k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2929,c_2438])).

tff(c_3262,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2412,c_3218,c_3189])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:55:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.65/2.08  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.81/2.12  
% 5.81/2.12  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.81/2.13  %$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 5.81/2.13  
% 5.81/2.13  %Foreground sorts:
% 5.81/2.13  
% 5.81/2.13  
% 5.81/2.13  %Background operators:
% 5.81/2.13  
% 5.81/2.13  
% 5.81/2.13  %Foreground operators:
% 5.81/2.13  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.81/2.13  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 5.81/2.13  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.81/2.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.81/2.13  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 5.81/2.13  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 5.81/2.13  tff(k2_funct_2, type, k2_funct_2: ($i * $i) > $i).
% 5.81/2.13  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.81/2.13  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.81/2.13  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.81/2.13  tff('#skF_2', type, '#skF_2': $i).
% 5.81/2.13  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 5.81/2.13  tff('#skF_3', type, '#skF_3': $i).
% 5.81/2.13  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 5.81/2.13  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.81/2.13  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.81/2.13  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.81/2.13  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 5.81/2.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.81/2.13  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.81/2.13  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.81/2.13  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 5.81/2.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.81/2.13  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.81/2.13  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 5.81/2.13  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.81/2.13  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.81/2.13  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.81/2.13  
% 5.81/2.17  tff(f_101, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 5.81/2.17  tff(f_114, axiom, (![A, B]: (?[C]: (((((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & v1_relat_1(C)) & v4_relat_1(C, A)) & v5_relat_1(C, B)) & v1_funct_1(C)) & v1_funct_2(C, A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc1_funct_2)).
% 5.81/2.17  tff(f_69, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 5.81/2.17  tff(f_157, negated_conjecture, ~(![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, k2_funct_2(A, B)), k6_partfun1(A)) & r2_relset_1(A, A, k1_partfun1(A, A, A, A, k2_funct_2(A, B), B), k6_partfun1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_funct_2)).
% 5.81/2.17  tff(f_59, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.81/2.17  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_funct_2)).
% 5.81/2.17  tff(f_55, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(k2_funct_1(A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_1)).
% 5.81/2.17  tff(f_134, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k2_funct_2(A, B) = k2_funct_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 5.81/2.17  tff(f_97, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (((v1_funct_1(k2_funct_2(A, B)) & v1_funct_2(k2_funct_2(A, B), A, A)) & v3_funct_2(k2_funct_2(A, B), A, A)) & m1_subset_1(k2_funct_2(A, B), k1_zfmisc_1(k2_zfmisc_1(A, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_2)).
% 5.81/2.17  tff(f_144, axiom, (![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k1_relset_1(A, A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_funct_2)).
% 5.81/2.17  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.81/2.17  tff(f_136, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 5.81/2.17  tff(f_47, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_1)).
% 5.81/2.17  tff(f_124, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 5.81/2.17  tff(c_36, plain, (![A_19]: (m1_subset_1(k6_partfun1(A_19), k1_zfmisc_1(k2_zfmisc_1(A_19, A_19))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 5.81/2.17  tff(c_48, plain, (![A_20, B_21]: (m1_subset_1('#skF_1'(A_20, B_21), k1_zfmisc_1(k2_zfmisc_1(A_20, B_21))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 5.81/2.17  tff(c_2364, plain, (![A_201, B_202, C_203, D_204]: (r2_relset_1(A_201, B_202, C_203, C_203) | ~m1_subset_1(D_204, k1_zfmisc_1(k2_zfmisc_1(A_201, B_202))) | ~m1_subset_1(C_203, k1_zfmisc_1(k2_zfmisc_1(A_201, B_202))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.81/2.17  tff(c_2404, plain, (![A_208, B_209, C_210]: (r2_relset_1(A_208, B_209, C_210, C_210) | ~m1_subset_1(C_210, k1_zfmisc_1(k2_zfmisc_1(A_208, B_209))))), inference(resolution, [status(thm)], [c_48, c_2364])).
% 5.81/2.17  tff(c_2412, plain, (![A_19]: (r2_relset_1(A_19, A_19, k6_partfun1(A_19), k6_partfun1(A_19)))), inference(resolution, [status(thm)], [c_36, c_2404])).
% 5.81/2.17  tff(c_60, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_157])).
% 5.81/2.17  tff(c_86, plain, (![C_49, A_50, B_51]: (v1_relat_1(C_49) | ~m1_subset_1(C_49, k1_zfmisc_1(k2_zfmisc_1(A_50, B_51))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.81/2.17  tff(c_99, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_60, c_86])).
% 5.81/2.17  tff(c_66, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_157])).
% 5.81/2.17  tff(c_62, plain, (v3_funct_2('#skF_3', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_157])).
% 5.81/2.17  tff(c_2288, plain, (![C_185, A_186, B_187]: (v2_funct_1(C_185) | ~v3_funct_2(C_185, A_186, B_187) | ~v1_funct_1(C_185) | ~m1_subset_1(C_185, k1_zfmisc_1(k2_zfmisc_1(A_186, B_187))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.81/2.17  tff(c_2297, plain, (v2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_60, c_2288])).
% 5.81/2.17  tff(c_2304, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_62, c_2297])).
% 5.81/2.17  tff(c_12, plain, (![A_3]: (k2_funct_1(k2_funct_1(A_3))=A_3 | ~v2_funct_1(A_3) | ~v1_funct_1(A_3) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.81/2.17  tff(c_64, plain, (v1_funct_2('#skF_3', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_157])).
% 5.81/2.17  tff(c_2419, plain, (![A_214, B_215]: (k2_funct_2(A_214, B_215)=k2_funct_1(B_215) | ~m1_subset_1(B_215, k1_zfmisc_1(k2_zfmisc_1(A_214, A_214))) | ~v3_funct_2(B_215, A_214, A_214) | ~v1_funct_2(B_215, A_214, A_214) | ~v1_funct_1(B_215))), inference(cnfTransformation, [status(thm)], [f_134])).
% 5.81/2.17  tff(c_2429, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_60, c_2419])).
% 5.81/2.17  tff(c_2436, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_2429])).
% 5.81/2.17  tff(c_2479, plain, (![A_225, B_226]: (m1_subset_1(k2_funct_2(A_225, B_226), k1_zfmisc_1(k2_zfmisc_1(A_225, A_225))) | ~m1_subset_1(B_226, k1_zfmisc_1(k2_zfmisc_1(A_225, A_225))) | ~v3_funct_2(B_226, A_225, A_225) | ~v1_funct_2(B_226, A_225, A_225) | ~v1_funct_1(B_226))), inference(cnfTransformation, [status(thm)], [f_97])).
% 5.81/2.17  tff(c_2509, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2436, c_2479])).
% 5.81/2.17  tff(c_2521, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_60, c_2509])).
% 5.81/2.17  tff(c_14, plain, (![C_6, A_4, B_5]: (v1_relat_1(C_6) | ~m1_subset_1(C_6, k1_zfmisc_1(k2_zfmisc_1(A_4, B_5))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.81/2.17  tff(c_2572, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_2521, c_14])).
% 5.81/2.17  tff(c_2374, plain, (![A_205, B_206]: (v1_funct_1(k2_funct_2(A_205, B_206)) | ~m1_subset_1(B_206, k1_zfmisc_1(k2_zfmisc_1(A_205, A_205))) | ~v3_funct_2(B_206, A_205, A_205) | ~v1_funct_2(B_206, A_205, A_205) | ~v1_funct_1(B_206))), inference(cnfTransformation, [status(thm)], [f_97])).
% 5.81/2.17  tff(c_2384, plain, (v1_funct_1(k2_funct_2('#skF_2', '#skF_3')) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_60, c_2374])).
% 5.81/2.17  tff(c_2391, plain, (v1_funct_1(k2_funct_2('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_2384])).
% 5.81/2.17  tff(c_2437, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2436, c_2391])).
% 5.81/2.17  tff(c_2463, plain, (![A_222, B_223]: (v3_funct_2(k2_funct_2(A_222, B_223), A_222, A_222) | ~m1_subset_1(B_223, k1_zfmisc_1(k2_zfmisc_1(A_222, A_222))) | ~v3_funct_2(B_223, A_222, A_222) | ~v1_funct_2(B_223, A_222, A_222) | ~v1_funct_1(B_223))), inference(cnfTransformation, [status(thm)], [f_97])).
% 5.81/2.17  tff(c_2470, plain, (v3_funct_2(k2_funct_2('#skF_2', '#skF_3'), '#skF_2', '#skF_2') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_60, c_2463])).
% 5.81/2.17  tff(c_2477, plain, (v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_2436, c_2470])).
% 5.81/2.17  tff(c_22, plain, (![C_16, A_14, B_15]: (v2_funct_1(C_16) | ~v3_funct_2(C_16, A_14, B_15) | ~v1_funct_1(C_16) | ~m1_subset_1(C_16, k1_zfmisc_1(k2_zfmisc_1(A_14, B_15))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.81/2.17  tff(c_2542, plain, (v2_funct_1(k2_funct_1('#skF_3')) | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_2521, c_22])).
% 5.81/2.17  tff(c_2570, plain, (v2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2437, c_2477, c_2542])).
% 5.81/2.17  tff(c_2448, plain, (![A_220, B_221]: (v1_funct_2(k2_funct_2(A_220, B_221), A_220, A_220) | ~m1_subset_1(B_221, k1_zfmisc_1(k2_zfmisc_1(A_220, A_220))) | ~v3_funct_2(B_221, A_220, A_220) | ~v1_funct_2(B_221, A_220, A_220) | ~v1_funct_1(B_221))), inference(cnfTransformation, [status(thm)], [f_97])).
% 5.81/2.17  tff(c_2455, plain, (v1_funct_2(k2_funct_2('#skF_2', '#skF_3'), '#skF_2', '#skF_2') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_60, c_2448])).
% 5.81/2.17  tff(c_2462, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_2436, c_2455])).
% 5.81/2.17  tff(c_56, plain, (![A_32, B_33]: (k1_relset_1(A_32, A_32, B_33)=A_32 | ~m1_subset_1(B_33, k1_zfmisc_1(k2_zfmisc_1(A_32, A_32))) | ~v1_funct_2(B_33, A_32, A_32) | ~v1_funct_1(B_33))), inference(cnfTransformation, [status(thm)], [f_144])).
% 5.81/2.17  tff(c_2536, plain, (k1_relset_1('#skF_2', '#skF_2', k2_funct_1('#skF_3'))='#skF_2' | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_2521, c_56])).
% 5.81/2.17  tff(c_2564, plain, (k1_relset_1('#skF_2', '#skF_2', k2_funct_1('#skF_3'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2437, c_2462, c_2536])).
% 5.81/2.17  tff(c_16, plain, (![A_7, B_8, C_9]: (k1_relset_1(A_7, B_8, C_9)=k1_relat_1(C_9) | ~m1_subset_1(C_9, k1_zfmisc_1(k2_zfmisc_1(A_7, B_8))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.81/2.17  tff(c_2571, plain, (k1_relset_1('#skF_2', '#skF_2', k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_2521, c_16])).
% 5.81/2.17  tff(c_2653, plain, (k1_relat_1(k2_funct_1('#skF_3'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2564, c_2571])).
% 5.81/2.17  tff(c_52, plain, (![A_29, B_30]: (k2_funct_2(A_29, B_30)=k2_funct_1(B_30) | ~m1_subset_1(B_30, k1_zfmisc_1(k2_zfmisc_1(A_29, A_29))) | ~v3_funct_2(B_30, A_29, A_29) | ~v1_funct_2(B_30, A_29, A_29) | ~v1_funct_1(B_30))), inference(cnfTransformation, [status(thm)], [f_134])).
% 5.81/2.17  tff(c_2528, plain, (k2_funct_2('#skF_2', k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3')) | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_2521, c_52])).
% 5.81/2.17  tff(c_2557, plain, (k2_funct_2('#skF_2', k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2437, c_2462, c_2477, c_2528])).
% 5.81/2.17  tff(c_26, plain, (![A_17, B_18]: (m1_subset_1(k2_funct_2(A_17, B_18), k1_zfmisc_1(k2_zfmisc_1(A_17, A_17))) | ~m1_subset_1(B_18, k1_zfmisc_1(k2_zfmisc_1(A_17, A_17))) | ~v3_funct_2(B_18, A_17, A_17) | ~v1_funct_2(B_18, A_17, A_17) | ~v1_funct_1(B_18))), inference(cnfTransformation, [status(thm)], [f_97])).
% 5.81/2.17  tff(c_2631, plain, (m1_subset_1(k2_funct_1(k2_funct_1('#skF_3')), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_2557, c_26])).
% 5.81/2.17  tff(c_2635, plain, (m1_subset_1(k2_funct_1(k2_funct_1('#skF_3')), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_2437, c_2462, c_2477, c_2521, c_2631])).
% 5.81/2.17  tff(c_2723, plain, (v1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(resolution, [status(thm)], [c_2635, c_14])).
% 5.81/2.17  tff(c_32, plain, (![A_17, B_18]: (v1_funct_1(k2_funct_2(A_17, B_18)) | ~m1_subset_1(B_18, k1_zfmisc_1(k2_zfmisc_1(A_17, A_17))) | ~v3_funct_2(B_18, A_17, A_17) | ~v1_funct_2(B_18, A_17, A_17) | ~v1_funct_1(B_18))), inference(cnfTransformation, [status(thm)], [f_97])).
% 5.81/2.17  tff(c_2533, plain, (v1_funct_1(k2_funct_2('#skF_2', k2_funct_1('#skF_3'))) | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_2521, c_32])).
% 5.81/2.17  tff(c_2561, plain, (v1_funct_1(k2_funct_2('#skF_2', k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_2437, c_2462, c_2477, c_2533])).
% 5.81/2.17  tff(c_2627, plain, (v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_2557, c_2561])).
% 5.81/2.17  tff(c_28, plain, (![A_17, B_18]: (v3_funct_2(k2_funct_2(A_17, B_18), A_17, A_17) | ~m1_subset_1(B_18, k1_zfmisc_1(k2_zfmisc_1(A_17, A_17))) | ~v3_funct_2(B_18, A_17, A_17) | ~v1_funct_2(B_18, A_17, A_17) | ~v1_funct_1(B_18))), inference(cnfTransformation, [status(thm)], [f_97])).
% 5.81/2.17  tff(c_2523, plain, (v3_funct_2(k2_funct_2('#skF_2', k2_funct_1('#skF_3')), '#skF_2', '#skF_2') | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_2521, c_28])).
% 5.81/2.17  tff(c_2551, plain, (v3_funct_2(k2_funct_2('#skF_2', k2_funct_1('#skF_3')), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2437, c_2462, c_2477, c_2523])).
% 5.81/2.17  tff(c_2626, plain, (v3_funct_2(k2_funct_1(k2_funct_1('#skF_3')), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2557, c_2551])).
% 5.81/2.17  tff(c_2684, plain, (v2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v3_funct_2(k2_funct_1(k2_funct_1('#skF_3')), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(resolution, [status(thm)], [c_2635, c_22])).
% 5.81/2.17  tff(c_2721, plain, (v2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_2627, c_2626, c_2684])).
% 5.81/2.17  tff(c_30, plain, (![A_17, B_18]: (v1_funct_2(k2_funct_2(A_17, B_18), A_17, A_17) | ~m1_subset_1(B_18, k1_zfmisc_1(k2_zfmisc_1(A_17, A_17))) | ~v3_funct_2(B_18, A_17, A_17) | ~v1_funct_2(B_18, A_17, A_17) | ~v1_funct_1(B_18))), inference(cnfTransformation, [status(thm)], [f_97])).
% 5.81/2.17  tff(c_2525, plain, (v1_funct_2(k2_funct_2('#skF_2', k2_funct_1('#skF_3')), '#skF_2', '#skF_2') | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_2521, c_30])).
% 5.81/2.17  tff(c_2554, plain, (v1_funct_2(k2_funct_2('#skF_2', k2_funct_1('#skF_3')), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2437, c_2462, c_2477, c_2525])).
% 5.81/2.17  tff(c_2647, plain, (v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2557, c_2554])).
% 5.81/2.17  tff(c_2670, plain, (k2_funct_2('#skF_2', k2_funct_1(k2_funct_1('#skF_3')))=k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v3_funct_2(k2_funct_1(k2_funct_1('#skF_3')), '#skF_2', '#skF_2') | ~v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(resolution, [status(thm)], [c_2635, c_52])).
% 5.81/2.17  tff(c_2708, plain, (k2_funct_2('#skF_2', k2_funct_1(k2_funct_1('#skF_3')))=k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_2627, c_2647, c_2626, c_2670])).
% 5.81/2.17  tff(c_2780, plain, (k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))=k2_funct_2('#skF_2', '#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_12, c_2708])).
% 5.81/2.17  tff(c_2786, plain, (k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_99, c_66, c_2304, c_2436, c_2780])).
% 5.81/2.17  tff(c_54, plain, (![A_31]: (k6_relat_1(A_31)=k6_partfun1(A_31))), inference(cnfTransformation, [status(thm)], [f_136])).
% 5.81/2.17  tff(c_8, plain, (![A_2]: (k5_relat_1(k2_funct_1(A_2), A_2)=k6_relat_1(k2_relat_1(A_2)) | ~v2_funct_1(A_2) | ~v1_funct_1(A_2) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.81/2.17  tff(c_68, plain, (![A_2]: (k5_relat_1(k2_funct_1(A_2), A_2)=k6_partfun1(k2_relat_1(A_2)) | ~v2_funct_1(A_2) | ~v1_funct_1(A_2) | ~v1_relat_1(A_2))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_8])).
% 5.81/2.17  tff(c_2803, plain, (k5_relat_1(k2_funct_1('#skF_3'), k2_funct_1(k2_funct_1('#skF_3')))=k6_partfun1(k2_relat_1(k2_funct_1(k2_funct_1('#skF_3')))) | ~v2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_2786, c_68])).
% 5.81/2.17  tff(c_2831, plain, (k5_relat_1(k2_funct_1('#skF_3'), k2_funct_1(k2_funct_1('#skF_3')))=k6_partfun1(k2_relat_1(k2_funct_1(k2_funct_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_2723, c_2627, c_2721, c_2803])).
% 5.81/2.17  tff(c_10, plain, (![A_2]: (k5_relat_1(A_2, k2_funct_1(A_2))=k6_relat_1(k1_relat_1(A_2)) | ~v2_funct_1(A_2) | ~v1_funct_1(A_2) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.81/2.17  tff(c_67, plain, (![A_2]: (k5_relat_1(A_2, k2_funct_1(A_2))=k6_partfun1(k1_relat_1(A_2)) | ~v2_funct_1(A_2) | ~v1_funct_1(A_2) | ~v1_relat_1(A_2))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_10])).
% 5.81/2.17  tff(c_3057, plain, (k6_partfun1(k2_relat_1(k2_funct_1(k2_funct_1('#skF_3'))))=k6_partfun1(k1_relat_1(k2_funct_1('#skF_3'))) | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_2831, c_67])).
% 5.81/2.17  tff(c_3067, plain, (k6_partfun1(k2_relat_1(k2_funct_1(k2_funct_1('#skF_3'))))=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2572, c_2437, c_2570, c_2653, c_3057])).
% 5.81/2.17  tff(c_3073, plain, (k5_relat_1(k2_funct_1('#skF_3'), k2_funct_1(k2_funct_1('#skF_3')))=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3067, c_2831])).
% 5.81/2.17  tff(c_3210, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_12, c_3073])).
% 5.81/2.17  tff(c_3218, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_99, c_66, c_2304, c_3210])).
% 5.81/2.17  tff(c_2573, plain, (![D_231, C_227, F_228, A_232, E_229, B_230]: (k1_partfun1(A_232, B_230, C_227, D_231, E_229, F_228)=k5_relat_1(E_229, F_228) | ~m1_subset_1(F_228, k1_zfmisc_1(k2_zfmisc_1(C_227, D_231))) | ~v1_funct_1(F_228) | ~m1_subset_1(E_229, k1_zfmisc_1(k2_zfmisc_1(A_232, B_230))) | ~v1_funct_1(E_229))), inference(cnfTransformation, [status(thm)], [f_124])).
% 5.81/2.17  tff(c_2583, plain, (![A_232, B_230, E_229]: (k1_partfun1(A_232, B_230, '#skF_2', '#skF_2', E_229, '#skF_3')=k5_relat_1(E_229, '#skF_3') | ~v1_funct_1('#skF_3') | ~m1_subset_1(E_229, k1_zfmisc_1(k2_zfmisc_1(A_232, B_230))) | ~v1_funct_1(E_229))), inference(resolution, [status(thm)], [c_60, c_2573])).
% 5.81/2.17  tff(c_2599, plain, (![A_233, B_234, E_235]: (k1_partfun1(A_233, B_234, '#skF_2', '#skF_2', E_235, '#skF_3')=k5_relat_1(E_235, '#skF_3') | ~m1_subset_1(E_235, k1_zfmisc_1(k2_zfmisc_1(A_233, B_234))) | ~v1_funct_1(E_235))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_2583])).
% 5.81/2.17  tff(c_2902, plain, (![A_240, B_241]: (k1_partfun1(A_240, A_240, '#skF_2', '#skF_2', k2_funct_2(A_240, B_241), '#skF_3')=k5_relat_1(k2_funct_2(A_240, B_241), '#skF_3') | ~v1_funct_1(k2_funct_2(A_240, B_241)) | ~m1_subset_1(B_241, k1_zfmisc_1(k2_zfmisc_1(A_240, A_240))) | ~v3_funct_2(B_241, A_240, A_240) | ~v1_funct_2(B_241, A_240, A_240) | ~v1_funct_1(B_241))), inference(resolution, [status(thm)], [c_26, c_2599])).
% 5.81/2.17  tff(c_2915, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_2('#skF_2', '#skF_3'), '#skF_3')=k5_relat_1(k2_funct_2('#skF_2', '#skF_3'), '#skF_3') | ~v1_funct_1(k2_funct_2('#skF_2', '#skF_3')) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_60, c_2902])).
% 5.81/2.17  tff(c_2929, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_1('#skF_3'), '#skF_3')=k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_2437, c_2436, c_2436, c_2436, c_2915])).
% 5.81/2.17  tff(c_227, plain, (![A_76, B_77, C_78, D_79]: (r2_relset_1(A_76, B_77, C_78, C_78) | ~m1_subset_1(D_79, k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))) | ~m1_subset_1(C_78, k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.81/2.17  tff(c_237, plain, (![A_80, B_81, C_82]: (r2_relset_1(A_80, B_81, C_82, C_82) | ~m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1(A_80, B_81))))), inference(resolution, [status(thm)], [c_48, c_227])).
% 5.81/2.17  tff(c_245, plain, (![A_19]: (r2_relset_1(A_19, A_19, k6_partfun1(A_19), k6_partfun1(A_19)))), inference(resolution, [status(thm)], [c_36, c_237])).
% 5.81/2.17  tff(c_190, plain, (![C_65, A_66, B_67]: (v2_funct_1(C_65) | ~v3_funct_2(C_65, A_66, B_67) | ~v1_funct_1(C_65) | ~m1_subset_1(C_65, k1_zfmisc_1(k2_zfmisc_1(A_66, B_67))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.81/2.17  tff(c_199, plain, (v2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_60, c_190])).
% 5.81/2.17  tff(c_206, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_62, c_199])).
% 5.81/2.17  tff(c_305, plain, (![A_92, B_93]: (k2_funct_2(A_92, B_93)=k2_funct_1(B_93) | ~m1_subset_1(B_93, k1_zfmisc_1(k2_zfmisc_1(A_92, A_92))) | ~v3_funct_2(B_93, A_92, A_92) | ~v1_funct_2(B_93, A_92, A_92) | ~v1_funct_1(B_93))), inference(cnfTransformation, [status(thm)], [f_134])).
% 5.81/2.17  tff(c_315, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_60, c_305])).
% 5.81/2.17  tff(c_322, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_315])).
% 5.81/2.17  tff(c_274, plain, (![A_89, B_90]: (v1_funct_1(k2_funct_2(A_89, B_90)) | ~m1_subset_1(B_90, k1_zfmisc_1(k2_zfmisc_1(A_89, A_89))) | ~v3_funct_2(B_90, A_89, A_89) | ~v1_funct_2(B_90, A_89, A_89) | ~v1_funct_1(B_90))), inference(cnfTransformation, [status(thm)], [f_97])).
% 5.81/2.17  tff(c_284, plain, (v1_funct_1(k2_funct_2('#skF_2', '#skF_3')) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_60, c_274])).
% 5.81/2.17  tff(c_291, plain, (v1_funct_1(k2_funct_2('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_284])).
% 5.81/2.17  tff(c_323, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_322, c_291])).
% 5.81/2.17  tff(c_348, plain, (![A_100, B_101]: (v1_funct_2(k2_funct_2(A_100, B_101), A_100, A_100) | ~m1_subset_1(B_101, k1_zfmisc_1(k2_zfmisc_1(A_100, A_100))) | ~v3_funct_2(B_101, A_100, A_100) | ~v1_funct_2(B_101, A_100, A_100) | ~v1_funct_1(B_101))), inference(cnfTransformation, [status(thm)], [f_97])).
% 5.81/2.17  tff(c_355, plain, (v1_funct_2(k2_funct_2('#skF_2', '#skF_3'), '#skF_2', '#skF_2') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_60, c_348])).
% 5.81/2.17  tff(c_362, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_322, c_355])).
% 5.81/2.17  tff(c_331, plain, (![A_96, B_97]: (v3_funct_2(k2_funct_2(A_96, B_97), A_96, A_96) | ~m1_subset_1(B_97, k1_zfmisc_1(k2_zfmisc_1(A_96, A_96))) | ~v3_funct_2(B_97, A_96, A_96) | ~v1_funct_2(B_97, A_96, A_96) | ~v1_funct_1(B_97))), inference(cnfTransformation, [status(thm)], [f_97])).
% 5.81/2.17  tff(c_338, plain, (v3_funct_2(k2_funct_2('#skF_2', '#skF_3'), '#skF_2', '#skF_2') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_60, c_331])).
% 5.81/2.17  tff(c_345, plain, (v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_322, c_338])).
% 5.81/2.17  tff(c_367, plain, (![A_106, B_107]: (m1_subset_1(k2_funct_2(A_106, B_107), k1_zfmisc_1(k2_zfmisc_1(A_106, A_106))) | ~m1_subset_1(B_107, k1_zfmisc_1(k2_zfmisc_1(A_106, A_106))) | ~v3_funct_2(B_107, A_106, A_106) | ~v1_funct_2(B_107, A_106, A_106) | ~v1_funct_1(B_107))), inference(cnfTransformation, [status(thm)], [f_97])).
% 5.81/2.17  tff(c_397, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_322, c_367])).
% 5.81/2.17  tff(c_409, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_60, c_397])).
% 5.81/2.17  tff(c_416, plain, (k2_funct_2('#skF_2', k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3')) | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_409, c_52])).
% 5.81/2.17  tff(c_445, plain, (k2_funct_2('#skF_2', k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_323, c_362, c_345, c_416])).
% 5.81/2.17  tff(c_419, plain, (v1_funct_1(k2_funct_2('#skF_2', k2_funct_1('#skF_3'))) | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_409, c_32])).
% 5.81/2.17  tff(c_448, plain, (v1_funct_1(k2_funct_2('#skF_2', k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_323, c_362, c_345, c_419])).
% 5.81/2.17  tff(c_489, plain, (v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_445, c_448])).
% 5.81/2.17  tff(c_411, plain, (v1_funct_2(k2_funct_2('#skF_2', k2_funct_1('#skF_3')), '#skF_2', '#skF_2') | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_409, c_30])).
% 5.81/2.17  tff(c_439, plain, (v1_funct_2(k2_funct_2('#skF_2', k2_funct_1('#skF_3')), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_323, c_362, c_345, c_411])).
% 5.81/2.17  tff(c_487, plain, (v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_445, c_439])).
% 5.81/2.17  tff(c_493, plain, (m1_subset_1(k2_funct_1(k2_funct_1('#skF_3')), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_445, c_26])).
% 5.81/2.17  tff(c_497, plain, (m1_subset_1(k2_funct_1(k2_funct_1('#skF_3')), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_323, c_362, c_345, c_409, c_493])).
% 5.81/2.17  tff(c_563, plain, (k1_relset_1('#skF_2', '#skF_2', k2_funct_1(k2_funct_1('#skF_3')))='#skF_2' | ~v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(resolution, [status(thm)], [c_497, c_56])).
% 5.81/2.17  tff(c_601, plain, (k1_relset_1('#skF_2', '#skF_2', k2_funct_1(k2_funct_1('#skF_3')))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_489, c_487, c_563])).
% 5.81/2.17  tff(c_609, plain, (k1_relset_1('#skF_2', '#skF_2', k2_funct_1(k2_funct_1('#skF_3')))=k1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(resolution, [status(thm)], [c_497, c_16])).
% 5.81/2.17  tff(c_857, plain, (k1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_601, c_609])).
% 5.81/2.17  tff(c_610, plain, (v1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(resolution, [status(thm)], [c_497, c_14])).
% 5.81/2.17  tff(c_413, plain, (v3_funct_2(k2_funct_2('#skF_2', k2_funct_1('#skF_3')), '#skF_2', '#skF_2') | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_409, c_28])).
% 5.81/2.17  tff(c_442, plain, (v3_funct_2(k2_funct_2('#skF_2', k2_funct_1('#skF_3')), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_323, c_362, c_345, c_413])).
% 5.81/2.17  tff(c_488, plain, (v3_funct_2(k2_funct_1(k2_funct_1('#skF_3')), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_445, c_442])).
% 5.81/2.17  tff(c_571, plain, (v2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v3_funct_2(k2_funct_1(k2_funct_1('#skF_3')), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(resolution, [status(thm)], [c_497, c_22])).
% 5.81/2.17  tff(c_608, plain, (v2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_489, c_488, c_571])).
% 5.81/2.17  tff(c_557, plain, (k2_funct_2('#skF_2', k2_funct_1(k2_funct_1('#skF_3')))=k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v3_funct_2(k2_funct_1(k2_funct_1('#skF_3')), '#skF_2', '#skF_2') | ~v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(resolution, [status(thm)], [c_497, c_52])).
% 5.81/2.17  tff(c_595, plain, (k2_funct_2('#skF_2', k2_funct_1(k2_funct_1('#skF_3')))=k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_489, c_487, c_488, c_557])).
% 5.81/2.17  tff(c_727, plain, (k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))=k2_funct_2('#skF_2', '#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_12, c_595])).
% 5.81/2.17  tff(c_733, plain, (k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_99, c_66, c_206, c_322, c_727])).
% 5.81/2.17  tff(c_763, plain, (k5_relat_1(k2_funct_1(k2_funct_1('#skF_3')), k2_funct_1('#skF_3'))=k6_partfun1(k1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))) | ~v2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_733, c_67])).
% 5.81/2.17  tff(c_791, plain, (k5_relat_1(k2_funct_1(k2_funct_1('#skF_3')), k2_funct_1('#skF_3'))=k6_partfun1(k1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_610, c_489, c_608, c_763])).
% 5.81/2.17  tff(c_1232, plain, (k5_relat_1(k2_funct_1(k2_funct_1('#skF_3')), k2_funct_1('#skF_3'))=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_857, c_791])).
% 5.81/2.17  tff(c_1249, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_12, c_1232])).
% 5.81/2.17  tff(c_1261, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_99, c_66, c_206, c_1249])).
% 5.81/2.17  tff(c_465, plain, (![B_111, A_113, C_108, D_112, F_109, E_110]: (k1_partfun1(A_113, B_111, C_108, D_112, E_110, F_109)=k5_relat_1(E_110, F_109) | ~m1_subset_1(F_109, k1_zfmisc_1(k2_zfmisc_1(C_108, D_112))) | ~v1_funct_1(F_109) | ~m1_subset_1(E_110, k1_zfmisc_1(k2_zfmisc_1(A_113, B_111))) | ~v1_funct_1(E_110))), inference(cnfTransformation, [status(thm)], [f_124])).
% 5.81/2.17  tff(c_467, plain, (![A_113, B_111, E_110]: (k1_partfun1(A_113, B_111, '#skF_2', '#skF_2', E_110, k2_funct_1('#skF_3'))=k5_relat_1(E_110, k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~m1_subset_1(E_110, k1_zfmisc_1(k2_zfmisc_1(A_113, B_111))) | ~v1_funct_1(E_110))), inference(resolution, [status(thm)], [c_409, c_465])).
% 5.81/2.17  tff(c_2144, plain, (![A_173, B_174, E_175]: (k1_partfun1(A_173, B_174, '#skF_2', '#skF_2', E_175, k2_funct_1('#skF_3'))=k5_relat_1(E_175, k2_funct_1('#skF_3')) | ~m1_subset_1(E_175, k1_zfmisc_1(k2_zfmisc_1(A_173, B_174))) | ~v1_funct_1(E_175))), inference(demodulation, [status(thm), theory('equality')], [c_323, c_467])).
% 5.81/2.17  tff(c_2177, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_1('#skF_3'))=k5_relat_1('#skF_3', k2_funct_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_60, c_2144])).
% 5.81/2.17  tff(c_2196, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_1261, c_2177])).
% 5.81/2.17  tff(c_58, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_2('#skF_2', '#skF_3'), '#skF_3'), k6_partfun1('#skF_2')) | ~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_2('#skF_2', '#skF_3')), k6_partfun1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_157])).
% 5.81/2.17  tff(c_104, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_2('#skF_2', '#skF_3')), k6_partfun1('#skF_2'))), inference(splitLeft, [status(thm)], [c_58])).
% 5.81/2.17  tff(c_324, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_1('#skF_3')), k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_322, c_104])).
% 5.81/2.17  tff(c_2197, plain, (~r2_relset_1('#skF_2', '#skF_2', k6_partfun1('#skF_2'), k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2196, c_324])).
% 5.81/2.17  tff(c_2200, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_245, c_2197])).
% 5.81/2.17  tff(c_2201, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_2('#skF_2', '#skF_3'), '#skF_3'), k6_partfun1('#skF_2'))), inference(splitRight, [status(thm)], [c_58])).
% 5.81/2.17  tff(c_2438, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_1('#skF_3'), '#skF_3'), k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2436, c_2201])).
% 5.81/2.17  tff(c_3189, plain, (~r2_relset_1('#skF_2', '#skF_2', k5_relat_1(k2_funct_1('#skF_3'), '#skF_3'), k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2929, c_2438])).
% 5.81/2.17  tff(c_3262, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2412, c_3218, c_3189])).
% 5.81/2.17  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.81/2.17  
% 5.81/2.17  Inference rules
% 5.81/2.17  ----------------------
% 5.81/2.17  #Ref     : 0
% 5.81/2.17  #Sup     : 759
% 5.81/2.17  #Fact    : 0
% 5.81/2.17  #Define  : 0
% 5.81/2.17  #Split   : 2
% 5.81/2.17  #Chain   : 0
% 5.81/2.17  #Close   : 0
% 5.81/2.17  
% 5.81/2.17  Ordering : KBO
% 5.81/2.17  
% 5.81/2.17  Simplification rules
% 5.81/2.17  ----------------------
% 5.81/2.17  #Subsume      : 89
% 5.81/2.17  #Demod        : 1432
% 5.81/2.17  #Tautology    : 332
% 5.81/2.17  #SimpNegUnit  : 0
% 5.81/2.17  #BackRed      : 31
% 5.81/2.17  
% 5.81/2.17  #Partial instantiations: 0
% 5.81/2.17  #Strategies tried      : 1
% 5.81/2.17  
% 5.81/2.17  Timing (in seconds)
% 5.81/2.17  ----------------------
% 5.81/2.18  Preprocessing        : 0.36
% 5.81/2.18  Parsing              : 0.20
% 5.81/2.18  CNF conversion       : 0.02
% 5.81/2.18  Main loop            : 0.94
% 5.81/2.18  Inferencing          : 0.31
% 5.81/2.18  Reduction            : 0.36
% 5.81/2.18  Demodulation         : 0.28
% 5.81/2.18  BG Simplification    : 0.04
% 5.81/2.18  Subsumption          : 0.16
% 5.81/2.18  Abstraction          : 0.04
% 5.81/2.18  MUC search           : 0.00
% 5.81/2.18  Cooper               : 0.00
% 5.81/2.18  Total                : 1.40
% 5.81/2.18  Index Insertion      : 0.00
% 5.81/2.18  Index Deletion       : 0.00
% 5.81/2.18  Index Matching       : 0.00
% 5.81/2.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
