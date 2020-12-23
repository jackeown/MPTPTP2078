%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:08 EST 2020

% Result     : Theorem 5.25s
% Output     : CNFRefutation 5.56s
% Verified   : 
% Statistics : Number of formulae       :  202 (11767 expanded)
%              Number of leaves         :   42 (4754 expanded)
%              Depth                    :   23
%              Number of atoms          :  486 (43178 expanded)
%              Number of equality atoms :   73 (2176 expanded)
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

tff(f_101,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_112,axiom,(
    ! [A,B] :
    ? [C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
      & v1_relat_1(C)
      & v4_relat_1(C,A)
      & v5_relat_1(C,B)
      & v1_funct_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_partfun1)).

tff(f_69,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(f_155,negated_conjecture,(
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

tff(f_132,axiom,(
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

tff(f_142,axiom,(
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

tff(f_134,axiom,(
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

tff(f_122,axiom,(
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

tff(c_46,plain,(
    ! [A_20,B_21] : m1_subset_1('#skF_1'(A_20,B_21),k1_zfmisc_1(k2_zfmisc_1(A_20,B_21))) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_2273,plain,(
    ! [A_195,B_196,C_197,D_198] :
      ( r2_relset_1(A_195,B_196,C_197,C_197)
      | ~ m1_subset_1(D_198,k1_zfmisc_1(k2_zfmisc_1(A_195,B_196)))
      | ~ m1_subset_1(C_197,k1_zfmisc_1(k2_zfmisc_1(A_195,B_196))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_2283,plain,(
    ! [A_199,B_200,C_201] :
      ( r2_relset_1(A_199,B_200,C_201,C_201)
      | ~ m1_subset_1(C_201,k1_zfmisc_1(k2_zfmisc_1(A_199,B_200))) ) ),
    inference(resolution,[status(thm)],[c_46,c_2273])).

tff(c_2291,plain,(
    ! [A_19] : r2_relset_1(A_19,A_19,k6_partfun1(A_19),k6_partfun1(A_19)) ),
    inference(resolution,[status(thm)],[c_36,c_2283])).

tff(c_58,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_82,plain,(
    ! [C_45,A_46,B_47] :
      ( v1_relat_1(C_45)
      | ~ m1_subset_1(C_45,k1_zfmisc_1(k2_zfmisc_1(A_46,B_47))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_90,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_82])).

tff(c_64,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_60,plain,(
    v3_funct_2('#skF_3','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_2206,plain,(
    ! [C_180,A_181,B_182] :
      ( v2_funct_1(C_180)
      | ~ v3_funct_2(C_180,A_181,B_182)
      | ~ v1_funct_1(C_180)
      | ~ m1_subset_1(C_180,k1_zfmisc_1(k2_zfmisc_1(A_181,B_182))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_2215,plain,
    ( v2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_2206])).

tff(c_2222,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60,c_2215])).

tff(c_12,plain,(
    ! [A_3] :
      ( k2_funct_1(k2_funct_1(A_3)) = A_3
      | ~ v2_funct_1(A_3)
      | ~ v1_funct_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_62,plain,(
    v1_funct_2('#skF_3','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_2314,plain,(
    ! [A_208,B_209] :
      ( k2_funct_2(A_208,B_209) = k2_funct_1(B_209)
      | ~ m1_subset_1(B_209,k1_zfmisc_1(k2_zfmisc_1(A_208,A_208)))
      | ~ v3_funct_2(B_209,A_208,A_208)
      | ~ v1_funct_2(B_209,A_208,A_208)
      | ~ v1_funct_1(B_209) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_2324,plain,
    ( k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_2314])).

tff(c_2331,plain,(
    k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_2324])).

tff(c_2376,plain,(
    ! [A_221,B_222] :
      ( m1_subset_1(k2_funct_2(A_221,B_222),k1_zfmisc_1(k2_zfmisc_1(A_221,A_221)))
      | ~ m1_subset_1(B_222,k1_zfmisc_1(k2_zfmisc_1(A_221,A_221)))
      | ~ v3_funct_2(B_222,A_221,A_221)
      | ~ v1_funct_2(B_222,A_221,A_221)
      | ~ v1_funct_1(B_222) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_2406,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2331,c_2376])).

tff(c_2418,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_58,c_2406])).

tff(c_14,plain,(
    ! [C_6,A_4,B_5] :
      ( v1_relat_1(C_6)
      | ~ m1_subset_1(C_6,k1_zfmisc_1(k2_zfmisc_1(A_4,B_5))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_2469,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2418,c_14])).

tff(c_2295,plain,(
    ! [A_205,B_206] :
      ( v1_funct_1(k2_funct_2(A_205,B_206))
      | ~ m1_subset_1(B_206,k1_zfmisc_1(k2_zfmisc_1(A_205,A_205)))
      | ~ v3_funct_2(B_206,A_205,A_205)
      | ~ v1_funct_2(B_206,A_205,A_205)
      | ~ v1_funct_1(B_206) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_2305,plain,
    ( v1_funct_1(k2_funct_2('#skF_2','#skF_3'))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_2295])).

tff(c_2312,plain,(
    v1_funct_1(k2_funct_2('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_2305])).

tff(c_2332,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2331,c_2312])).

tff(c_2340,plain,(
    ! [A_211,B_212] :
      ( v3_funct_2(k2_funct_2(A_211,B_212),A_211,A_211)
      | ~ m1_subset_1(B_212,k1_zfmisc_1(k2_zfmisc_1(A_211,A_211)))
      | ~ v3_funct_2(B_212,A_211,A_211)
      | ~ v1_funct_2(B_212,A_211,A_211)
      | ~ v1_funct_1(B_212) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_2347,plain,
    ( v3_funct_2(k2_funct_2('#skF_2','#skF_3'),'#skF_2','#skF_2')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_2340])).

tff(c_2354,plain,(
    v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_2331,c_2347])).

tff(c_22,plain,(
    ! [C_16,A_14,B_15] :
      ( v2_funct_1(C_16)
      | ~ v3_funct_2(C_16,A_14,B_15)
      | ~ v1_funct_1(C_16)
      | ~ m1_subset_1(C_16,k1_zfmisc_1(k2_zfmisc_1(A_14,B_15))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_2439,plain,
    ( v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2418,c_22])).

tff(c_2467,plain,(
    v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2332,c_2354,c_2439])).

tff(c_2357,plain,(
    ! [A_215,B_216] :
      ( v1_funct_2(k2_funct_2(A_215,B_216),A_215,A_215)
      | ~ m1_subset_1(B_216,k1_zfmisc_1(k2_zfmisc_1(A_215,A_215)))
      | ~ v3_funct_2(B_216,A_215,A_215)
      | ~ v1_funct_2(B_216,A_215,A_215)
      | ~ v1_funct_1(B_216) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_2364,plain,
    ( v1_funct_2(k2_funct_2('#skF_2','#skF_3'),'#skF_2','#skF_2')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_2357])).

tff(c_2371,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_2331,c_2364])).

tff(c_54,plain,(
    ! [A_32,B_33] :
      ( k1_relset_1(A_32,A_32,B_33) = A_32
      | ~ m1_subset_1(B_33,k1_zfmisc_1(k2_zfmisc_1(A_32,A_32)))
      | ~ v1_funct_2(B_33,A_32,A_32)
      | ~ v1_funct_1(B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_2433,plain,
    ( k1_relset_1('#skF_2','#skF_2',k2_funct_1('#skF_3')) = '#skF_2'
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2418,c_54])).

tff(c_2461,plain,(
    k1_relset_1('#skF_2','#skF_2',k2_funct_1('#skF_3')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2332,c_2371,c_2433])).

tff(c_16,plain,(
    ! [A_7,B_8,C_9] :
      ( k1_relset_1(A_7,B_8,C_9) = k1_relat_1(C_9)
      | ~ m1_subset_1(C_9,k1_zfmisc_1(k2_zfmisc_1(A_7,B_8))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2468,plain,(
    k1_relset_1('#skF_2','#skF_2',k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2418,c_16])).

tff(c_2523,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2461,c_2468])).

tff(c_50,plain,(
    ! [A_29,B_30] :
      ( k2_funct_2(A_29,B_30) = k2_funct_1(B_30)
      | ~ m1_subset_1(B_30,k1_zfmisc_1(k2_zfmisc_1(A_29,A_29)))
      | ~ v3_funct_2(B_30,A_29,A_29)
      | ~ v1_funct_2(B_30,A_29,A_29)
      | ~ v1_funct_1(B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_2425,plain,
    ( k2_funct_2('#skF_2',k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3'))
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2418,c_50])).

tff(c_2454,plain,(
    k2_funct_2('#skF_2',k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2332,c_2371,c_2354,c_2425])).

tff(c_26,plain,(
    ! [A_17,B_18] :
      ( m1_subset_1(k2_funct_2(A_17,B_18),k1_zfmisc_1(k2_zfmisc_1(A_17,A_17)))
      | ~ m1_subset_1(B_18,k1_zfmisc_1(k2_zfmisc_1(A_17,A_17)))
      | ~ v3_funct_2(B_18,A_17,A_17)
      | ~ v1_funct_2(B_18,A_17,A_17)
      | ~ v1_funct_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_2478,plain,
    ( m1_subset_1(k2_funct_1(k2_funct_1('#skF_3')),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2454,c_26])).

tff(c_2482,plain,(
    m1_subset_1(k2_funct_1(k2_funct_1('#skF_3')),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2332,c_2371,c_2354,c_2418,c_2478])).

tff(c_2619,plain,(
    v1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_2482,c_14])).

tff(c_32,plain,(
    ! [A_17,B_18] :
      ( v1_funct_1(k2_funct_2(A_17,B_18))
      | ~ m1_subset_1(B_18,k1_zfmisc_1(k2_zfmisc_1(A_17,A_17)))
      | ~ v3_funct_2(B_18,A_17,A_17)
      | ~ v1_funct_2(B_18,A_17,A_17)
      | ~ v1_funct_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_2428,plain,
    ( v1_funct_1(k2_funct_2('#skF_2',k2_funct_1('#skF_3')))
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2418,c_32])).

tff(c_2457,plain,(
    v1_funct_1(k2_funct_2('#skF_2',k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2332,c_2371,c_2354,c_2428])).

tff(c_2474,plain,(
    v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2454,c_2457])).

tff(c_28,plain,(
    ! [A_17,B_18] :
      ( v3_funct_2(k2_funct_2(A_17,B_18),A_17,A_17)
      | ~ m1_subset_1(B_18,k1_zfmisc_1(k2_zfmisc_1(A_17,A_17)))
      | ~ v3_funct_2(B_18,A_17,A_17)
      | ~ v1_funct_2(B_18,A_17,A_17)
      | ~ v1_funct_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_2422,plain,
    ( v3_funct_2(k2_funct_2('#skF_2',k2_funct_1('#skF_3')),'#skF_2','#skF_2')
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2418,c_28])).

tff(c_2451,plain,(
    v3_funct_2(k2_funct_2('#skF_2',k2_funct_1('#skF_3')),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2332,c_2371,c_2354,c_2422])).

tff(c_2511,plain,(
    v3_funct_2(k2_funct_1(k2_funct_1('#skF_3')),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2454,c_2451])).

tff(c_2580,plain,
    ( v2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v3_funct_2(k2_funct_1(k2_funct_1('#skF_3')),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_2482,c_22])).

tff(c_2617,plain,(
    v2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2474,c_2511,c_2580])).

tff(c_30,plain,(
    ! [A_17,B_18] :
      ( v1_funct_2(k2_funct_2(A_17,B_18),A_17,A_17)
      | ~ m1_subset_1(B_18,k1_zfmisc_1(k2_zfmisc_1(A_17,A_17)))
      | ~ v3_funct_2(B_18,A_17,A_17)
      | ~ v1_funct_2(B_18,A_17,A_17)
      | ~ v1_funct_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_2420,plain,
    ( v1_funct_2(k2_funct_2('#skF_2',k2_funct_1('#skF_3')),'#skF_2','#skF_2')
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2418,c_30])).

tff(c_2448,plain,(
    v1_funct_2(k2_funct_2('#skF_2',k2_funct_1('#skF_3')),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2332,c_2371,c_2354,c_2420])).

tff(c_2517,plain,(
    v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2454,c_2448])).

tff(c_2566,plain,
    ( k2_funct_2('#skF_2',k2_funct_1(k2_funct_1('#skF_3'))) = k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v3_funct_2(k2_funct_1(k2_funct_1('#skF_3')),'#skF_2','#skF_2')
    | ~ v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_2482,c_50])).

tff(c_2604,plain,(
    k2_funct_2('#skF_2',k2_funct_1(k2_funct_1('#skF_3'))) = k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2474,c_2517,c_2511,c_2566])).

tff(c_2735,plain,
    ( k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) = k2_funct_2('#skF_2','#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_2604])).

tff(c_2741,plain,(
    k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_64,c_2222,c_2331,c_2735])).

tff(c_52,plain,(
    ! [A_31] : k6_relat_1(A_31) = k6_partfun1(A_31) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_8,plain,(
    ! [A_2] :
      ( k5_relat_1(k2_funct_1(A_2),A_2) = k6_relat_1(k2_relat_1(A_2))
      | ~ v2_funct_1(A_2)
      | ~ v1_funct_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_66,plain,(
    ! [A_2] :
      ( k5_relat_1(k2_funct_1(A_2),A_2) = k6_partfun1(k2_relat_1(A_2))
      | ~ v2_funct_1(A_2)
      | ~ v1_funct_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_8])).

tff(c_2774,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),k2_funct_1(k2_funct_1('#skF_3'))) = k6_partfun1(k2_relat_1(k2_funct_1(k2_funct_1('#skF_3'))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2741,c_66])).

tff(c_2801,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),k2_funct_1(k2_funct_1('#skF_3'))) = k6_partfun1(k2_relat_1(k2_funct_1(k2_funct_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2619,c_2474,c_2617,c_2774])).

tff(c_10,plain,(
    ! [A_2] :
      ( k5_relat_1(A_2,k2_funct_1(A_2)) = k6_relat_1(k1_relat_1(A_2))
      | ~ v2_funct_1(A_2)
      | ~ v1_funct_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_65,plain,(
    ! [A_2] :
      ( k5_relat_1(A_2,k2_funct_1(A_2)) = k6_partfun1(k1_relat_1(A_2))
      | ~ v2_funct_1(A_2)
      | ~ v1_funct_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_10])).

tff(c_2978,plain,
    ( k6_partfun1(k2_relat_1(k2_funct_1(k2_funct_1('#skF_3')))) = k6_partfun1(k1_relat_1(k2_funct_1('#skF_3')))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2801,c_65])).

tff(c_2988,plain,(
    k6_partfun1(k2_relat_1(k2_funct_1(k2_funct_1('#skF_3')))) = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2469,c_2332,c_2467,c_2523,c_2978])).

tff(c_2994,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),k2_funct_1(k2_funct_1('#skF_3'))) = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2988,c_2801])).

tff(c_3240,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_2994])).

tff(c_3252,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_64,c_2222,c_3240])).

tff(c_2489,plain,(
    ! [D_227,A_228,B_226,F_224,C_223,E_225] :
      ( k1_partfun1(A_228,B_226,C_223,D_227,E_225,F_224) = k5_relat_1(E_225,F_224)
      | ~ m1_subset_1(F_224,k1_zfmisc_1(k2_zfmisc_1(C_223,D_227)))
      | ~ v1_funct_1(F_224)
      | ~ m1_subset_1(E_225,k1_zfmisc_1(k2_zfmisc_1(A_228,B_226)))
      | ~ v1_funct_1(E_225) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_2499,plain,(
    ! [A_228,B_226,E_225] :
      ( k1_partfun1(A_228,B_226,'#skF_2','#skF_2',E_225,'#skF_3') = k5_relat_1(E_225,'#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(E_225,k1_zfmisc_1(k2_zfmisc_1(A_228,B_226)))
      | ~ v1_funct_1(E_225) ) ),
    inference(resolution,[status(thm)],[c_58,c_2489])).

tff(c_2528,plain,(
    ! [A_229,B_230,E_231] :
      ( k1_partfun1(A_229,B_230,'#skF_2','#skF_2',E_231,'#skF_3') = k5_relat_1(E_231,'#skF_3')
      | ~ m1_subset_1(E_231,k1_zfmisc_1(k2_zfmisc_1(A_229,B_230)))
      | ~ v1_funct_1(E_231) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_2499])).

tff(c_3196,plain,(
    ! [A_244,B_245] :
      ( k1_partfun1(A_244,A_244,'#skF_2','#skF_2',k2_funct_2(A_244,B_245),'#skF_3') = k5_relat_1(k2_funct_2(A_244,B_245),'#skF_3')
      | ~ v1_funct_1(k2_funct_2(A_244,B_245))
      | ~ m1_subset_1(B_245,k1_zfmisc_1(k2_zfmisc_1(A_244,A_244)))
      | ~ v3_funct_2(B_245,A_244,A_244)
      | ~ v1_funct_2(B_245,A_244,A_244)
      | ~ v1_funct_1(B_245) ) ),
    inference(resolution,[status(thm)],[c_26,c_2528])).

tff(c_3209,plain,
    ( k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_2('#skF_2','#skF_3'),'#skF_3') = k5_relat_1(k2_funct_2('#skF_2','#skF_3'),'#skF_3')
    | ~ v1_funct_1(k2_funct_2('#skF_2','#skF_3'))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_3196])).

tff(c_3223,plain,(
    k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_1('#skF_3'),'#skF_3') = k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_2332,c_2331,c_2331,c_2331,c_3209])).

tff(c_3342,plain,(
    k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3252,c_3223])).

tff(c_254,plain,(
    ! [A_78,B_79,C_80,D_81] :
      ( r2_relset_1(A_78,B_79,C_80,C_80)
      | ~ m1_subset_1(D_81,k1_zfmisc_1(k2_zfmisc_1(A_78,B_79)))
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1(A_78,B_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_264,plain,(
    ! [A_82,B_83,C_84] :
      ( r2_relset_1(A_82,B_83,C_84,C_84)
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1(A_82,B_83))) ) ),
    inference(resolution,[status(thm)],[c_46,c_254])).

tff(c_272,plain,(
    ! [A_19] : r2_relset_1(A_19,A_19,k6_partfun1(A_19),k6_partfun1(A_19)) ),
    inference(resolution,[status(thm)],[c_36,c_264])).

tff(c_187,plain,(
    ! [C_63,A_64,B_65] :
      ( v2_funct_1(C_63)
      | ~ v3_funct_2(C_63,A_64,B_65)
      | ~ v1_funct_1(C_63)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1(A_64,B_65))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_196,plain,
    ( v2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_187])).

tff(c_203,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60,c_196])).

tff(c_295,plain,(
    ! [A_91,B_92] :
      ( k2_funct_2(A_91,B_92) = k2_funct_1(B_92)
      | ~ m1_subset_1(B_92,k1_zfmisc_1(k2_zfmisc_1(A_91,A_91)))
      | ~ v3_funct_2(B_92,A_91,A_91)
      | ~ v1_funct_2(B_92,A_91,A_91)
      | ~ v1_funct_1(B_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

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
    ! [A_105,B_106] :
      ( m1_subset_1(k2_funct_2(A_105,B_106),k1_zfmisc_1(k2_zfmisc_1(A_105,A_105)))
      | ~ m1_subset_1(B_106,k1_zfmisc_1(k2_zfmisc_1(A_105,A_105)))
      | ~ v3_funct_2(B_106,A_105,A_105)
      | ~ v1_funct_2(B_106,A_105,A_105)
      | ~ v1_funct_1(B_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

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

tff(c_276,plain,(
    ! [A_88,B_89] :
      ( v1_funct_1(k2_funct_2(A_88,B_89))
      | ~ m1_subset_1(B_89,k1_zfmisc_1(k2_zfmisc_1(A_88,A_88)))
      | ~ v3_funct_2(B_89,A_88,A_88)
      | ~ v1_funct_2(B_89,A_88,A_88)
      | ~ v1_funct_1(B_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_286,plain,
    ( v1_funct_1(k2_funct_2('#skF_2','#skF_3'))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_276])).

tff(c_293,plain,(
    v1_funct_1(k2_funct_2('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_286])).

tff(c_313,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_312,c_293])).

tff(c_338,plain,(
    ! [A_99,B_100] :
      ( v3_funct_2(k2_funct_2(A_99,B_100),A_99,A_99)
      | ~ m1_subset_1(B_100,k1_zfmisc_1(k2_zfmisc_1(A_99,A_99)))
      | ~ v3_funct_2(B_100,A_99,A_99)
      | ~ v1_funct_2(B_100,A_99,A_99)
      | ~ v1_funct_1(B_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_345,plain,
    ( v3_funct_2(k2_funct_2('#skF_2','#skF_3'),'#skF_2','#skF_2')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_338])).

tff(c_352,plain,(
    v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_312,c_345])).

tff(c_420,plain,
    ( v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_399,c_22])).

tff(c_448,plain,(
    v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_313,c_352,c_420])).

tff(c_175,plain,(
    ! [A_62] :
      ( k5_relat_1(k2_funct_1(A_62),A_62) = k6_partfun1(k2_relat_1(A_62))
      | ~ v2_funct_1(A_62)
      | ~ v1_funct_1(A_62)
      | ~ v1_relat_1(A_62) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_8])).

tff(c_184,plain,(
    ! [A_3] :
      ( k6_partfun1(k2_relat_1(k2_funct_1(A_3))) = k5_relat_1(A_3,k2_funct_1(A_3))
      | ~ v2_funct_1(k2_funct_1(A_3))
      | ~ v1_funct_1(k2_funct_1(A_3))
      | ~ v1_relat_1(k2_funct_1(A_3))
      | ~ v2_funct_1(A_3)
      | ~ v1_funct_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_175])).

tff(c_321,plain,(
    ! [A_95,B_96] :
      ( v1_funct_2(k2_funct_2(A_95,B_96),A_95,A_95)
      | ~ m1_subset_1(B_96,k1_zfmisc_1(k2_zfmisc_1(A_95,A_95)))
      | ~ v3_funct_2(B_96,A_95,A_95)
      | ~ v1_funct_2(B_96,A_95,A_95)
      | ~ v1_funct_1(B_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_328,plain,
    ( v1_funct_2(k2_funct_2('#skF_2','#skF_3'),'#skF_2','#skF_2')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_321])).

tff(c_335,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_312,c_328])).

tff(c_406,plain,
    ( k2_funct_2('#skF_2',k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3'))
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_399,c_50])).

tff(c_435,plain,(
    k2_funct_2('#skF_2',k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_313,c_335,c_352,c_406])).

tff(c_483,plain,
    ( m1_subset_1(k2_funct_1(k2_funct_1('#skF_3')),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_435,c_26])).

tff(c_487,plain,(
    m1_subset_1(k2_funct_1(k2_funct_1('#skF_3')),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_313,c_335,c_352,c_399,c_483])).

tff(c_600,plain,(
    v1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_487,c_14])).

tff(c_409,plain,
    ( v1_funct_1(k2_funct_2('#skF_2',k2_funct_1('#skF_3')))
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_399,c_32])).

tff(c_438,plain,(
    v1_funct_1(k2_funct_2('#skF_2',k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_313,c_335,c_352,c_409])).

tff(c_479,plain,(
    v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_435,c_438])).

tff(c_401,plain,
    ( v3_funct_2(k2_funct_2('#skF_2',k2_funct_1('#skF_3')),'#skF_2','#skF_2')
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_399,c_28])).

tff(c_429,plain,(
    v3_funct_2(k2_funct_2('#skF_2',k2_funct_1('#skF_3')),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_313,c_335,c_352,c_401])).

tff(c_478,plain,(
    v3_funct_2(k2_funct_1(k2_funct_1('#skF_3')),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_435,c_429])).

tff(c_561,plain,
    ( v2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v3_funct_2(k2_funct_1(k2_funct_1('#skF_3')),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_487,c_22])).

tff(c_598,plain,(
    v2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_479,c_478,c_561])).

tff(c_403,plain,
    ( v1_funct_2(k2_funct_2('#skF_2',k2_funct_1('#skF_3')),'#skF_2','#skF_2')
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_399,c_30])).

tff(c_432,plain,(
    v1_funct_2(k2_funct_2('#skF_2',k2_funct_1('#skF_3')),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_313,c_335,c_352,c_403])).

tff(c_477,plain,(
    v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_435,c_432])).

tff(c_555,plain,
    ( k1_relset_1('#skF_2','#skF_2',k2_funct_1(k2_funct_1('#skF_3'))) = '#skF_2'
    | ~ v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_487,c_54])).

tff(c_592,plain,(
    k1_relset_1('#skF_2','#skF_2',k2_funct_1(k2_funct_1('#skF_3'))) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_479,c_477,c_555])).

tff(c_599,plain,(
    k1_relset_1('#skF_2','#skF_2',k2_funct_1(k2_funct_1('#skF_3'))) = k1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_487,c_16])).

tff(c_1079,plain,(
    k1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_592,c_599])).

tff(c_547,plain,
    ( k2_funct_2('#skF_2',k2_funct_1(k2_funct_1('#skF_3'))) = k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v3_funct_2(k2_funct_1(k2_funct_1('#skF_3')),'#skF_2','#skF_2')
    | ~ v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_487,c_50])).

tff(c_585,plain,(
    k2_funct_2('#skF_2',k2_funct_1(k2_funct_1('#skF_3'))) = k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_479,c_477,c_478,c_547])).

tff(c_696,plain,
    ( k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) = k2_funct_2('#skF_2','#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_585])).

tff(c_702,plain,(
    k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_64,c_203,c_312,c_696])).

tff(c_1164,plain,(
    ! [A_131] :
      ( k6_partfun1(k2_relat_1(k2_funct_1(A_131))) = k5_relat_1(A_131,k2_funct_1(A_131))
      | ~ v2_funct_1(k2_funct_1(A_131))
      | ~ v1_funct_1(k2_funct_1(A_131))
      | ~ v1_relat_1(k2_funct_1(A_131))
      | ~ v2_funct_1(A_131)
      | ~ v1_funct_1(A_131)
      | ~ v1_relat_1(A_131) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_175])).

tff(c_1229,plain,
    ( k6_partfun1(k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))))) = k5_relat_1(k2_funct_1(k2_funct_1('#skF_3')),k2_funct_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_702,c_1164])).

tff(c_1245,plain,(
    k5_relat_1(k2_funct_1(k2_funct_1('#skF_3')),k2_funct_1('#skF_3')) = k6_partfun1(k2_relat_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_600,c_479,c_598,c_450,c_702,c_313,c_702,c_448,c_702,c_702,c_1229])).

tff(c_163,plain,(
    ! [A_61] :
      ( k5_relat_1(A_61,k2_funct_1(A_61)) = k6_partfun1(k1_relat_1(A_61))
      | ~ v2_funct_1(A_61)
      | ~ v1_funct_1(A_61)
      | ~ v1_relat_1(A_61) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_10])).

tff(c_172,plain,(
    ! [A_3] :
      ( k6_partfun1(k1_relat_1(k2_funct_1(A_3))) = k5_relat_1(k2_funct_1(A_3),A_3)
      | ~ v2_funct_1(k2_funct_1(A_3))
      | ~ v1_funct_1(k2_funct_1(A_3))
      | ~ v1_relat_1(k2_funct_1(A_3))
      | ~ v2_funct_1(A_3)
      | ~ v1_funct_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_163])).

tff(c_1249,plain,
    ( k6_partfun1(k1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))) = k6_partfun1(k2_relat_1(k2_funct_1('#skF_3')))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1245,c_172])).

tff(c_1265,plain,(
    k6_partfun1(k2_relat_1(k2_funct_1('#skF_3'))) = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_450,c_313,c_448,c_600,c_479,c_598,c_1079,c_1249])).

tff(c_1326,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_2')
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_184,c_1265])).

tff(c_1345,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_64,c_203,c_450,c_313,c_448,c_1326])).

tff(c_455,plain,(
    ! [A_112,F_108,B_110,D_111,E_109,C_107] :
      ( k1_partfun1(A_112,B_110,C_107,D_111,E_109,F_108) = k5_relat_1(E_109,F_108)
      | ~ m1_subset_1(F_108,k1_zfmisc_1(k2_zfmisc_1(C_107,D_111)))
      | ~ v1_funct_1(F_108)
      | ~ m1_subset_1(E_109,k1_zfmisc_1(k2_zfmisc_1(A_112,B_110)))
      | ~ v1_funct_1(E_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_457,plain,(
    ! [A_112,B_110,E_109] :
      ( k1_partfun1(A_112,B_110,'#skF_2','#skF_2',E_109,k2_funct_1('#skF_3')) = k5_relat_1(E_109,k2_funct_1('#skF_3'))
      | ~ v1_funct_1(k2_funct_1('#skF_3'))
      | ~ m1_subset_1(E_109,k1_zfmisc_1(k2_zfmisc_1(A_112,B_110)))
      | ~ v1_funct_1(E_109) ) ),
    inference(resolution,[status(thm)],[c_399,c_455])).

tff(c_2088,plain,(
    ! [A_169,B_170,E_171] :
      ( k1_partfun1(A_169,B_170,'#skF_2','#skF_2',E_171,k2_funct_1('#skF_3')) = k5_relat_1(E_171,k2_funct_1('#skF_3'))
      | ~ m1_subset_1(E_171,k1_zfmisc_1(k2_zfmisc_1(A_169,B_170)))
      | ~ v1_funct_1(E_171) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_313,c_457])).

tff(c_2121,plain,
    ( k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_1('#skF_3')) = k5_relat_1('#skF_3',k2_funct_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_2088])).

tff(c_2140,plain,(
    k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_1345,c_2121])).

tff(c_56,plain,
    ( ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_2('#skF_2','#skF_3'),'#skF_3'),k6_partfun1('#skF_2'))
    | ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_2('#skF_2','#skF_3')),k6_partfun1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_127,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_2('#skF_2','#skF_3')),k6_partfun1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_314,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_1('#skF_3')),k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_312,c_127])).

tff(c_2141,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k6_partfun1('#skF_2'),k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2140,c_314])).

tff(c_2144,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_272,c_2141])).

tff(c_2145,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_2('#skF_2','#skF_3'),'#skF_3'),k6_partfun1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_2333,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_1('#skF_3'),'#skF_3'),k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2331,c_2145])).

tff(c_3343,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k6_partfun1('#skF_2'),k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3342,c_2333])).

tff(c_3346,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2291,c_3343])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:11:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.25/1.98  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.56/2.01  
% 5.56/2.01  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.56/2.01  %$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 5.56/2.01  
% 5.56/2.01  %Foreground sorts:
% 5.56/2.01  
% 5.56/2.01  
% 5.56/2.01  %Background operators:
% 5.56/2.01  
% 5.56/2.01  
% 5.56/2.01  %Foreground operators:
% 5.56/2.01  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.56/2.01  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 5.56/2.01  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.56/2.01  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.56/2.01  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 5.56/2.01  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 5.56/2.01  tff(k2_funct_2, type, k2_funct_2: ($i * $i) > $i).
% 5.56/2.01  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.56/2.01  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.56/2.01  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.56/2.01  tff('#skF_2', type, '#skF_2': $i).
% 5.56/2.01  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 5.56/2.01  tff('#skF_3', type, '#skF_3': $i).
% 5.56/2.01  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 5.56/2.01  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.56/2.01  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.56/2.01  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.56/2.01  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 5.56/2.01  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.56/2.01  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.56/2.01  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.56/2.01  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 5.56/2.01  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.56/2.01  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.56/2.01  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 5.56/2.01  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.56/2.01  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.56/2.01  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.56/2.01  
% 5.56/2.04  tff(f_101, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 5.56/2.04  tff(f_112, axiom, (![A, B]: (?[C]: ((((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & v1_relat_1(C)) & v4_relat_1(C, A)) & v5_relat_1(C, B)) & v1_funct_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc1_partfun1)).
% 5.56/2.04  tff(f_69, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 5.56/2.04  tff(f_155, negated_conjecture, ~(![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, k2_funct_2(A, B)), k6_partfun1(A)) & r2_relset_1(A, A, k1_partfun1(A, A, A, A, k2_funct_2(A, B), B), k6_partfun1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_funct_2)).
% 5.56/2.04  tff(f_59, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.56/2.04  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_funct_2)).
% 5.56/2.04  tff(f_55, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(k2_funct_1(A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_1)).
% 5.56/2.04  tff(f_132, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k2_funct_2(A, B) = k2_funct_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 5.56/2.04  tff(f_97, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (((v1_funct_1(k2_funct_2(A, B)) & v1_funct_2(k2_funct_2(A, B), A, A)) & v3_funct_2(k2_funct_2(A, B), A, A)) & m1_subset_1(k2_funct_2(A, B), k1_zfmisc_1(k2_zfmisc_1(A, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_2)).
% 5.56/2.04  tff(f_142, axiom, (![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k1_relset_1(A, A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_funct_2)).
% 5.56/2.04  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.56/2.04  tff(f_134, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 5.56/2.04  tff(f_47, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_1)).
% 5.56/2.04  tff(f_122, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 5.56/2.04  tff(c_36, plain, (![A_19]: (m1_subset_1(k6_partfun1(A_19), k1_zfmisc_1(k2_zfmisc_1(A_19, A_19))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 5.56/2.04  tff(c_46, plain, (![A_20, B_21]: (m1_subset_1('#skF_1'(A_20, B_21), k1_zfmisc_1(k2_zfmisc_1(A_20, B_21))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 5.56/2.04  tff(c_2273, plain, (![A_195, B_196, C_197, D_198]: (r2_relset_1(A_195, B_196, C_197, C_197) | ~m1_subset_1(D_198, k1_zfmisc_1(k2_zfmisc_1(A_195, B_196))) | ~m1_subset_1(C_197, k1_zfmisc_1(k2_zfmisc_1(A_195, B_196))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.56/2.04  tff(c_2283, plain, (![A_199, B_200, C_201]: (r2_relset_1(A_199, B_200, C_201, C_201) | ~m1_subset_1(C_201, k1_zfmisc_1(k2_zfmisc_1(A_199, B_200))))), inference(resolution, [status(thm)], [c_46, c_2273])).
% 5.56/2.04  tff(c_2291, plain, (![A_19]: (r2_relset_1(A_19, A_19, k6_partfun1(A_19), k6_partfun1(A_19)))), inference(resolution, [status(thm)], [c_36, c_2283])).
% 5.56/2.04  tff(c_58, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_155])).
% 5.56/2.04  tff(c_82, plain, (![C_45, A_46, B_47]: (v1_relat_1(C_45) | ~m1_subset_1(C_45, k1_zfmisc_1(k2_zfmisc_1(A_46, B_47))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.56/2.04  tff(c_90, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_58, c_82])).
% 5.56/2.04  tff(c_64, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_155])).
% 5.56/2.04  tff(c_60, plain, (v3_funct_2('#skF_3', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_155])).
% 5.56/2.04  tff(c_2206, plain, (![C_180, A_181, B_182]: (v2_funct_1(C_180) | ~v3_funct_2(C_180, A_181, B_182) | ~v1_funct_1(C_180) | ~m1_subset_1(C_180, k1_zfmisc_1(k2_zfmisc_1(A_181, B_182))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.56/2.04  tff(c_2215, plain, (v2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_58, c_2206])).
% 5.56/2.04  tff(c_2222, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_60, c_2215])).
% 5.56/2.04  tff(c_12, plain, (![A_3]: (k2_funct_1(k2_funct_1(A_3))=A_3 | ~v2_funct_1(A_3) | ~v1_funct_1(A_3) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.56/2.04  tff(c_62, plain, (v1_funct_2('#skF_3', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_155])).
% 5.56/2.04  tff(c_2314, plain, (![A_208, B_209]: (k2_funct_2(A_208, B_209)=k2_funct_1(B_209) | ~m1_subset_1(B_209, k1_zfmisc_1(k2_zfmisc_1(A_208, A_208))) | ~v3_funct_2(B_209, A_208, A_208) | ~v1_funct_2(B_209, A_208, A_208) | ~v1_funct_1(B_209))), inference(cnfTransformation, [status(thm)], [f_132])).
% 5.56/2.04  tff(c_2324, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_58, c_2314])).
% 5.56/2.04  tff(c_2331, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_2324])).
% 5.56/2.04  tff(c_2376, plain, (![A_221, B_222]: (m1_subset_1(k2_funct_2(A_221, B_222), k1_zfmisc_1(k2_zfmisc_1(A_221, A_221))) | ~m1_subset_1(B_222, k1_zfmisc_1(k2_zfmisc_1(A_221, A_221))) | ~v3_funct_2(B_222, A_221, A_221) | ~v1_funct_2(B_222, A_221, A_221) | ~v1_funct_1(B_222))), inference(cnfTransformation, [status(thm)], [f_97])).
% 5.56/2.04  tff(c_2406, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2331, c_2376])).
% 5.56/2.04  tff(c_2418, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_58, c_2406])).
% 5.56/2.04  tff(c_14, plain, (![C_6, A_4, B_5]: (v1_relat_1(C_6) | ~m1_subset_1(C_6, k1_zfmisc_1(k2_zfmisc_1(A_4, B_5))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.56/2.04  tff(c_2469, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_2418, c_14])).
% 5.56/2.04  tff(c_2295, plain, (![A_205, B_206]: (v1_funct_1(k2_funct_2(A_205, B_206)) | ~m1_subset_1(B_206, k1_zfmisc_1(k2_zfmisc_1(A_205, A_205))) | ~v3_funct_2(B_206, A_205, A_205) | ~v1_funct_2(B_206, A_205, A_205) | ~v1_funct_1(B_206))), inference(cnfTransformation, [status(thm)], [f_97])).
% 5.56/2.04  tff(c_2305, plain, (v1_funct_1(k2_funct_2('#skF_2', '#skF_3')) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_58, c_2295])).
% 5.56/2.04  tff(c_2312, plain, (v1_funct_1(k2_funct_2('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_2305])).
% 5.56/2.04  tff(c_2332, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2331, c_2312])).
% 5.56/2.04  tff(c_2340, plain, (![A_211, B_212]: (v3_funct_2(k2_funct_2(A_211, B_212), A_211, A_211) | ~m1_subset_1(B_212, k1_zfmisc_1(k2_zfmisc_1(A_211, A_211))) | ~v3_funct_2(B_212, A_211, A_211) | ~v1_funct_2(B_212, A_211, A_211) | ~v1_funct_1(B_212))), inference(cnfTransformation, [status(thm)], [f_97])).
% 5.56/2.04  tff(c_2347, plain, (v3_funct_2(k2_funct_2('#skF_2', '#skF_3'), '#skF_2', '#skF_2') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_58, c_2340])).
% 5.56/2.04  tff(c_2354, plain, (v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_2331, c_2347])).
% 5.56/2.04  tff(c_22, plain, (![C_16, A_14, B_15]: (v2_funct_1(C_16) | ~v3_funct_2(C_16, A_14, B_15) | ~v1_funct_1(C_16) | ~m1_subset_1(C_16, k1_zfmisc_1(k2_zfmisc_1(A_14, B_15))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.56/2.04  tff(c_2439, plain, (v2_funct_1(k2_funct_1('#skF_3')) | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_2418, c_22])).
% 5.56/2.04  tff(c_2467, plain, (v2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2332, c_2354, c_2439])).
% 5.56/2.04  tff(c_2357, plain, (![A_215, B_216]: (v1_funct_2(k2_funct_2(A_215, B_216), A_215, A_215) | ~m1_subset_1(B_216, k1_zfmisc_1(k2_zfmisc_1(A_215, A_215))) | ~v3_funct_2(B_216, A_215, A_215) | ~v1_funct_2(B_216, A_215, A_215) | ~v1_funct_1(B_216))), inference(cnfTransformation, [status(thm)], [f_97])).
% 5.56/2.04  tff(c_2364, plain, (v1_funct_2(k2_funct_2('#skF_2', '#skF_3'), '#skF_2', '#skF_2') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_58, c_2357])).
% 5.56/2.04  tff(c_2371, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_2331, c_2364])).
% 5.56/2.04  tff(c_54, plain, (![A_32, B_33]: (k1_relset_1(A_32, A_32, B_33)=A_32 | ~m1_subset_1(B_33, k1_zfmisc_1(k2_zfmisc_1(A_32, A_32))) | ~v1_funct_2(B_33, A_32, A_32) | ~v1_funct_1(B_33))), inference(cnfTransformation, [status(thm)], [f_142])).
% 5.56/2.04  tff(c_2433, plain, (k1_relset_1('#skF_2', '#skF_2', k2_funct_1('#skF_3'))='#skF_2' | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_2418, c_54])).
% 5.56/2.04  tff(c_2461, plain, (k1_relset_1('#skF_2', '#skF_2', k2_funct_1('#skF_3'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2332, c_2371, c_2433])).
% 5.56/2.04  tff(c_16, plain, (![A_7, B_8, C_9]: (k1_relset_1(A_7, B_8, C_9)=k1_relat_1(C_9) | ~m1_subset_1(C_9, k1_zfmisc_1(k2_zfmisc_1(A_7, B_8))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.56/2.04  tff(c_2468, plain, (k1_relset_1('#skF_2', '#skF_2', k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_2418, c_16])).
% 5.56/2.04  tff(c_2523, plain, (k1_relat_1(k2_funct_1('#skF_3'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2461, c_2468])).
% 5.56/2.04  tff(c_50, plain, (![A_29, B_30]: (k2_funct_2(A_29, B_30)=k2_funct_1(B_30) | ~m1_subset_1(B_30, k1_zfmisc_1(k2_zfmisc_1(A_29, A_29))) | ~v3_funct_2(B_30, A_29, A_29) | ~v1_funct_2(B_30, A_29, A_29) | ~v1_funct_1(B_30))), inference(cnfTransformation, [status(thm)], [f_132])).
% 5.56/2.04  tff(c_2425, plain, (k2_funct_2('#skF_2', k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3')) | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_2418, c_50])).
% 5.56/2.04  tff(c_2454, plain, (k2_funct_2('#skF_2', k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2332, c_2371, c_2354, c_2425])).
% 5.56/2.04  tff(c_26, plain, (![A_17, B_18]: (m1_subset_1(k2_funct_2(A_17, B_18), k1_zfmisc_1(k2_zfmisc_1(A_17, A_17))) | ~m1_subset_1(B_18, k1_zfmisc_1(k2_zfmisc_1(A_17, A_17))) | ~v3_funct_2(B_18, A_17, A_17) | ~v1_funct_2(B_18, A_17, A_17) | ~v1_funct_1(B_18))), inference(cnfTransformation, [status(thm)], [f_97])).
% 5.56/2.04  tff(c_2478, plain, (m1_subset_1(k2_funct_1(k2_funct_1('#skF_3')), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_2454, c_26])).
% 5.56/2.04  tff(c_2482, plain, (m1_subset_1(k2_funct_1(k2_funct_1('#skF_3')), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_2332, c_2371, c_2354, c_2418, c_2478])).
% 5.56/2.04  tff(c_2619, plain, (v1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(resolution, [status(thm)], [c_2482, c_14])).
% 5.56/2.04  tff(c_32, plain, (![A_17, B_18]: (v1_funct_1(k2_funct_2(A_17, B_18)) | ~m1_subset_1(B_18, k1_zfmisc_1(k2_zfmisc_1(A_17, A_17))) | ~v3_funct_2(B_18, A_17, A_17) | ~v1_funct_2(B_18, A_17, A_17) | ~v1_funct_1(B_18))), inference(cnfTransformation, [status(thm)], [f_97])).
% 5.56/2.04  tff(c_2428, plain, (v1_funct_1(k2_funct_2('#skF_2', k2_funct_1('#skF_3'))) | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_2418, c_32])).
% 5.56/2.04  tff(c_2457, plain, (v1_funct_1(k2_funct_2('#skF_2', k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_2332, c_2371, c_2354, c_2428])).
% 5.56/2.04  tff(c_2474, plain, (v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_2454, c_2457])).
% 5.56/2.04  tff(c_28, plain, (![A_17, B_18]: (v3_funct_2(k2_funct_2(A_17, B_18), A_17, A_17) | ~m1_subset_1(B_18, k1_zfmisc_1(k2_zfmisc_1(A_17, A_17))) | ~v3_funct_2(B_18, A_17, A_17) | ~v1_funct_2(B_18, A_17, A_17) | ~v1_funct_1(B_18))), inference(cnfTransformation, [status(thm)], [f_97])).
% 5.56/2.04  tff(c_2422, plain, (v3_funct_2(k2_funct_2('#skF_2', k2_funct_1('#skF_3')), '#skF_2', '#skF_2') | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_2418, c_28])).
% 5.56/2.04  tff(c_2451, plain, (v3_funct_2(k2_funct_2('#skF_2', k2_funct_1('#skF_3')), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2332, c_2371, c_2354, c_2422])).
% 5.56/2.04  tff(c_2511, plain, (v3_funct_2(k2_funct_1(k2_funct_1('#skF_3')), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2454, c_2451])).
% 5.56/2.04  tff(c_2580, plain, (v2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v3_funct_2(k2_funct_1(k2_funct_1('#skF_3')), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(resolution, [status(thm)], [c_2482, c_22])).
% 5.56/2.04  tff(c_2617, plain, (v2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_2474, c_2511, c_2580])).
% 5.56/2.04  tff(c_30, plain, (![A_17, B_18]: (v1_funct_2(k2_funct_2(A_17, B_18), A_17, A_17) | ~m1_subset_1(B_18, k1_zfmisc_1(k2_zfmisc_1(A_17, A_17))) | ~v3_funct_2(B_18, A_17, A_17) | ~v1_funct_2(B_18, A_17, A_17) | ~v1_funct_1(B_18))), inference(cnfTransformation, [status(thm)], [f_97])).
% 5.56/2.04  tff(c_2420, plain, (v1_funct_2(k2_funct_2('#skF_2', k2_funct_1('#skF_3')), '#skF_2', '#skF_2') | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_2418, c_30])).
% 5.56/2.04  tff(c_2448, plain, (v1_funct_2(k2_funct_2('#skF_2', k2_funct_1('#skF_3')), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2332, c_2371, c_2354, c_2420])).
% 5.56/2.04  tff(c_2517, plain, (v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2454, c_2448])).
% 5.56/2.04  tff(c_2566, plain, (k2_funct_2('#skF_2', k2_funct_1(k2_funct_1('#skF_3')))=k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v3_funct_2(k2_funct_1(k2_funct_1('#skF_3')), '#skF_2', '#skF_2') | ~v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(resolution, [status(thm)], [c_2482, c_50])).
% 5.56/2.04  tff(c_2604, plain, (k2_funct_2('#skF_2', k2_funct_1(k2_funct_1('#skF_3')))=k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_2474, c_2517, c_2511, c_2566])).
% 5.56/2.04  tff(c_2735, plain, (k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))=k2_funct_2('#skF_2', '#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_12, c_2604])).
% 5.56/2.04  tff(c_2741, plain, (k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_64, c_2222, c_2331, c_2735])).
% 5.56/2.04  tff(c_52, plain, (![A_31]: (k6_relat_1(A_31)=k6_partfun1(A_31))), inference(cnfTransformation, [status(thm)], [f_134])).
% 5.56/2.04  tff(c_8, plain, (![A_2]: (k5_relat_1(k2_funct_1(A_2), A_2)=k6_relat_1(k2_relat_1(A_2)) | ~v2_funct_1(A_2) | ~v1_funct_1(A_2) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.56/2.04  tff(c_66, plain, (![A_2]: (k5_relat_1(k2_funct_1(A_2), A_2)=k6_partfun1(k2_relat_1(A_2)) | ~v2_funct_1(A_2) | ~v1_funct_1(A_2) | ~v1_relat_1(A_2))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_8])).
% 5.56/2.04  tff(c_2774, plain, (k5_relat_1(k2_funct_1('#skF_3'), k2_funct_1(k2_funct_1('#skF_3')))=k6_partfun1(k2_relat_1(k2_funct_1(k2_funct_1('#skF_3')))) | ~v2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_2741, c_66])).
% 5.56/2.04  tff(c_2801, plain, (k5_relat_1(k2_funct_1('#skF_3'), k2_funct_1(k2_funct_1('#skF_3')))=k6_partfun1(k2_relat_1(k2_funct_1(k2_funct_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_2619, c_2474, c_2617, c_2774])).
% 5.56/2.04  tff(c_10, plain, (![A_2]: (k5_relat_1(A_2, k2_funct_1(A_2))=k6_relat_1(k1_relat_1(A_2)) | ~v2_funct_1(A_2) | ~v1_funct_1(A_2) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.56/2.04  tff(c_65, plain, (![A_2]: (k5_relat_1(A_2, k2_funct_1(A_2))=k6_partfun1(k1_relat_1(A_2)) | ~v2_funct_1(A_2) | ~v1_funct_1(A_2) | ~v1_relat_1(A_2))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_10])).
% 5.56/2.04  tff(c_2978, plain, (k6_partfun1(k2_relat_1(k2_funct_1(k2_funct_1('#skF_3'))))=k6_partfun1(k1_relat_1(k2_funct_1('#skF_3'))) | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_2801, c_65])).
% 5.56/2.04  tff(c_2988, plain, (k6_partfun1(k2_relat_1(k2_funct_1(k2_funct_1('#skF_3'))))=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2469, c_2332, c_2467, c_2523, c_2978])).
% 5.56/2.04  tff(c_2994, plain, (k5_relat_1(k2_funct_1('#skF_3'), k2_funct_1(k2_funct_1('#skF_3')))=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2988, c_2801])).
% 5.56/2.04  tff(c_3240, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_12, c_2994])).
% 5.56/2.04  tff(c_3252, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_64, c_2222, c_3240])).
% 5.56/2.04  tff(c_2489, plain, (![D_227, A_228, B_226, F_224, C_223, E_225]: (k1_partfun1(A_228, B_226, C_223, D_227, E_225, F_224)=k5_relat_1(E_225, F_224) | ~m1_subset_1(F_224, k1_zfmisc_1(k2_zfmisc_1(C_223, D_227))) | ~v1_funct_1(F_224) | ~m1_subset_1(E_225, k1_zfmisc_1(k2_zfmisc_1(A_228, B_226))) | ~v1_funct_1(E_225))), inference(cnfTransformation, [status(thm)], [f_122])).
% 5.56/2.04  tff(c_2499, plain, (![A_228, B_226, E_225]: (k1_partfun1(A_228, B_226, '#skF_2', '#skF_2', E_225, '#skF_3')=k5_relat_1(E_225, '#skF_3') | ~v1_funct_1('#skF_3') | ~m1_subset_1(E_225, k1_zfmisc_1(k2_zfmisc_1(A_228, B_226))) | ~v1_funct_1(E_225))), inference(resolution, [status(thm)], [c_58, c_2489])).
% 5.56/2.04  tff(c_2528, plain, (![A_229, B_230, E_231]: (k1_partfun1(A_229, B_230, '#skF_2', '#skF_2', E_231, '#skF_3')=k5_relat_1(E_231, '#skF_3') | ~m1_subset_1(E_231, k1_zfmisc_1(k2_zfmisc_1(A_229, B_230))) | ~v1_funct_1(E_231))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_2499])).
% 5.56/2.04  tff(c_3196, plain, (![A_244, B_245]: (k1_partfun1(A_244, A_244, '#skF_2', '#skF_2', k2_funct_2(A_244, B_245), '#skF_3')=k5_relat_1(k2_funct_2(A_244, B_245), '#skF_3') | ~v1_funct_1(k2_funct_2(A_244, B_245)) | ~m1_subset_1(B_245, k1_zfmisc_1(k2_zfmisc_1(A_244, A_244))) | ~v3_funct_2(B_245, A_244, A_244) | ~v1_funct_2(B_245, A_244, A_244) | ~v1_funct_1(B_245))), inference(resolution, [status(thm)], [c_26, c_2528])).
% 5.56/2.04  tff(c_3209, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_2('#skF_2', '#skF_3'), '#skF_3')=k5_relat_1(k2_funct_2('#skF_2', '#skF_3'), '#skF_3') | ~v1_funct_1(k2_funct_2('#skF_2', '#skF_3')) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_58, c_3196])).
% 5.56/2.04  tff(c_3223, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_1('#skF_3'), '#skF_3')=k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_2332, c_2331, c_2331, c_2331, c_3209])).
% 5.56/2.04  tff(c_3342, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3252, c_3223])).
% 5.56/2.04  tff(c_254, plain, (![A_78, B_79, C_80, D_81]: (r2_relset_1(A_78, B_79, C_80, C_80) | ~m1_subset_1(D_81, k1_zfmisc_1(k2_zfmisc_1(A_78, B_79))) | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1(A_78, B_79))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.56/2.04  tff(c_264, plain, (![A_82, B_83, C_84]: (r2_relset_1(A_82, B_83, C_84, C_84) | ~m1_subset_1(C_84, k1_zfmisc_1(k2_zfmisc_1(A_82, B_83))))), inference(resolution, [status(thm)], [c_46, c_254])).
% 5.56/2.04  tff(c_272, plain, (![A_19]: (r2_relset_1(A_19, A_19, k6_partfun1(A_19), k6_partfun1(A_19)))), inference(resolution, [status(thm)], [c_36, c_264])).
% 5.56/2.04  tff(c_187, plain, (![C_63, A_64, B_65]: (v2_funct_1(C_63) | ~v3_funct_2(C_63, A_64, B_65) | ~v1_funct_1(C_63) | ~m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1(A_64, B_65))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.56/2.04  tff(c_196, plain, (v2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_58, c_187])).
% 5.56/2.04  tff(c_203, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_60, c_196])).
% 5.56/2.04  tff(c_295, plain, (![A_91, B_92]: (k2_funct_2(A_91, B_92)=k2_funct_1(B_92) | ~m1_subset_1(B_92, k1_zfmisc_1(k2_zfmisc_1(A_91, A_91))) | ~v3_funct_2(B_92, A_91, A_91) | ~v1_funct_2(B_92, A_91, A_91) | ~v1_funct_1(B_92))), inference(cnfTransformation, [status(thm)], [f_132])).
% 5.56/2.04  tff(c_305, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_58, c_295])).
% 5.56/2.04  tff(c_312, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_305])).
% 5.56/2.04  tff(c_357, plain, (![A_105, B_106]: (m1_subset_1(k2_funct_2(A_105, B_106), k1_zfmisc_1(k2_zfmisc_1(A_105, A_105))) | ~m1_subset_1(B_106, k1_zfmisc_1(k2_zfmisc_1(A_105, A_105))) | ~v3_funct_2(B_106, A_105, A_105) | ~v1_funct_2(B_106, A_105, A_105) | ~v1_funct_1(B_106))), inference(cnfTransformation, [status(thm)], [f_97])).
% 5.56/2.04  tff(c_387, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_312, c_357])).
% 5.56/2.04  tff(c_399, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_58, c_387])).
% 5.56/2.04  tff(c_450, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_399, c_14])).
% 5.56/2.04  tff(c_276, plain, (![A_88, B_89]: (v1_funct_1(k2_funct_2(A_88, B_89)) | ~m1_subset_1(B_89, k1_zfmisc_1(k2_zfmisc_1(A_88, A_88))) | ~v3_funct_2(B_89, A_88, A_88) | ~v1_funct_2(B_89, A_88, A_88) | ~v1_funct_1(B_89))), inference(cnfTransformation, [status(thm)], [f_97])).
% 5.56/2.04  tff(c_286, plain, (v1_funct_1(k2_funct_2('#skF_2', '#skF_3')) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_58, c_276])).
% 5.56/2.04  tff(c_293, plain, (v1_funct_1(k2_funct_2('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_286])).
% 5.56/2.04  tff(c_313, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_312, c_293])).
% 5.56/2.04  tff(c_338, plain, (![A_99, B_100]: (v3_funct_2(k2_funct_2(A_99, B_100), A_99, A_99) | ~m1_subset_1(B_100, k1_zfmisc_1(k2_zfmisc_1(A_99, A_99))) | ~v3_funct_2(B_100, A_99, A_99) | ~v1_funct_2(B_100, A_99, A_99) | ~v1_funct_1(B_100))), inference(cnfTransformation, [status(thm)], [f_97])).
% 5.56/2.04  tff(c_345, plain, (v3_funct_2(k2_funct_2('#skF_2', '#skF_3'), '#skF_2', '#skF_2') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_58, c_338])).
% 5.56/2.04  tff(c_352, plain, (v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_312, c_345])).
% 5.56/2.04  tff(c_420, plain, (v2_funct_1(k2_funct_1('#skF_3')) | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_399, c_22])).
% 5.56/2.04  tff(c_448, plain, (v2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_313, c_352, c_420])).
% 5.56/2.04  tff(c_175, plain, (![A_62]: (k5_relat_1(k2_funct_1(A_62), A_62)=k6_partfun1(k2_relat_1(A_62)) | ~v2_funct_1(A_62) | ~v1_funct_1(A_62) | ~v1_relat_1(A_62))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_8])).
% 5.56/2.04  tff(c_184, plain, (![A_3]: (k6_partfun1(k2_relat_1(k2_funct_1(A_3)))=k5_relat_1(A_3, k2_funct_1(A_3)) | ~v2_funct_1(k2_funct_1(A_3)) | ~v1_funct_1(k2_funct_1(A_3)) | ~v1_relat_1(k2_funct_1(A_3)) | ~v2_funct_1(A_3) | ~v1_funct_1(A_3) | ~v1_relat_1(A_3))), inference(superposition, [status(thm), theory('equality')], [c_12, c_175])).
% 5.56/2.04  tff(c_321, plain, (![A_95, B_96]: (v1_funct_2(k2_funct_2(A_95, B_96), A_95, A_95) | ~m1_subset_1(B_96, k1_zfmisc_1(k2_zfmisc_1(A_95, A_95))) | ~v3_funct_2(B_96, A_95, A_95) | ~v1_funct_2(B_96, A_95, A_95) | ~v1_funct_1(B_96))), inference(cnfTransformation, [status(thm)], [f_97])).
% 5.56/2.04  tff(c_328, plain, (v1_funct_2(k2_funct_2('#skF_2', '#skF_3'), '#skF_2', '#skF_2') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_58, c_321])).
% 5.56/2.04  tff(c_335, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_312, c_328])).
% 5.56/2.04  tff(c_406, plain, (k2_funct_2('#skF_2', k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3')) | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_399, c_50])).
% 5.56/2.04  tff(c_435, plain, (k2_funct_2('#skF_2', k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_313, c_335, c_352, c_406])).
% 5.56/2.04  tff(c_483, plain, (m1_subset_1(k2_funct_1(k2_funct_1('#skF_3')), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_435, c_26])).
% 5.56/2.04  tff(c_487, plain, (m1_subset_1(k2_funct_1(k2_funct_1('#skF_3')), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_313, c_335, c_352, c_399, c_483])).
% 5.56/2.04  tff(c_600, plain, (v1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(resolution, [status(thm)], [c_487, c_14])).
% 5.56/2.04  tff(c_409, plain, (v1_funct_1(k2_funct_2('#skF_2', k2_funct_1('#skF_3'))) | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_399, c_32])).
% 5.56/2.04  tff(c_438, plain, (v1_funct_1(k2_funct_2('#skF_2', k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_313, c_335, c_352, c_409])).
% 5.56/2.04  tff(c_479, plain, (v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_435, c_438])).
% 5.56/2.04  tff(c_401, plain, (v3_funct_2(k2_funct_2('#skF_2', k2_funct_1('#skF_3')), '#skF_2', '#skF_2') | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_399, c_28])).
% 5.56/2.04  tff(c_429, plain, (v3_funct_2(k2_funct_2('#skF_2', k2_funct_1('#skF_3')), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_313, c_335, c_352, c_401])).
% 5.56/2.04  tff(c_478, plain, (v3_funct_2(k2_funct_1(k2_funct_1('#skF_3')), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_435, c_429])).
% 5.56/2.04  tff(c_561, plain, (v2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v3_funct_2(k2_funct_1(k2_funct_1('#skF_3')), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(resolution, [status(thm)], [c_487, c_22])).
% 5.56/2.04  tff(c_598, plain, (v2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_479, c_478, c_561])).
% 5.56/2.04  tff(c_403, plain, (v1_funct_2(k2_funct_2('#skF_2', k2_funct_1('#skF_3')), '#skF_2', '#skF_2') | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_399, c_30])).
% 5.56/2.04  tff(c_432, plain, (v1_funct_2(k2_funct_2('#skF_2', k2_funct_1('#skF_3')), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_313, c_335, c_352, c_403])).
% 5.56/2.04  tff(c_477, plain, (v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_435, c_432])).
% 5.56/2.04  tff(c_555, plain, (k1_relset_1('#skF_2', '#skF_2', k2_funct_1(k2_funct_1('#skF_3')))='#skF_2' | ~v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(resolution, [status(thm)], [c_487, c_54])).
% 5.56/2.04  tff(c_592, plain, (k1_relset_1('#skF_2', '#skF_2', k2_funct_1(k2_funct_1('#skF_3')))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_479, c_477, c_555])).
% 5.56/2.04  tff(c_599, plain, (k1_relset_1('#skF_2', '#skF_2', k2_funct_1(k2_funct_1('#skF_3')))=k1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(resolution, [status(thm)], [c_487, c_16])).
% 5.56/2.04  tff(c_1079, plain, (k1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_592, c_599])).
% 5.56/2.04  tff(c_547, plain, (k2_funct_2('#skF_2', k2_funct_1(k2_funct_1('#skF_3')))=k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v3_funct_2(k2_funct_1(k2_funct_1('#skF_3')), '#skF_2', '#skF_2') | ~v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(resolution, [status(thm)], [c_487, c_50])).
% 5.56/2.04  tff(c_585, plain, (k2_funct_2('#skF_2', k2_funct_1(k2_funct_1('#skF_3')))=k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_479, c_477, c_478, c_547])).
% 5.56/2.04  tff(c_696, plain, (k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))=k2_funct_2('#skF_2', '#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_12, c_585])).
% 5.56/2.04  tff(c_702, plain, (k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_64, c_203, c_312, c_696])).
% 5.56/2.04  tff(c_1164, plain, (![A_131]: (k6_partfun1(k2_relat_1(k2_funct_1(A_131)))=k5_relat_1(A_131, k2_funct_1(A_131)) | ~v2_funct_1(k2_funct_1(A_131)) | ~v1_funct_1(k2_funct_1(A_131)) | ~v1_relat_1(k2_funct_1(A_131)) | ~v2_funct_1(A_131) | ~v1_funct_1(A_131) | ~v1_relat_1(A_131))), inference(superposition, [status(thm), theory('equality')], [c_12, c_175])).
% 5.56/2.04  tff(c_1229, plain, (k6_partfun1(k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))))=k5_relat_1(k2_funct_1(k2_funct_1('#skF_3')), k2_funct_1('#skF_3')) | ~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))) | ~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))) | ~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))) | ~v2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_702, c_1164])).
% 5.56/2.04  tff(c_1245, plain, (k5_relat_1(k2_funct_1(k2_funct_1('#skF_3')), k2_funct_1('#skF_3'))=k6_partfun1(k2_relat_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_600, c_479, c_598, c_450, c_702, c_313, c_702, c_448, c_702, c_702, c_1229])).
% 5.56/2.04  tff(c_163, plain, (![A_61]: (k5_relat_1(A_61, k2_funct_1(A_61))=k6_partfun1(k1_relat_1(A_61)) | ~v2_funct_1(A_61) | ~v1_funct_1(A_61) | ~v1_relat_1(A_61))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_10])).
% 5.56/2.04  tff(c_172, plain, (![A_3]: (k6_partfun1(k1_relat_1(k2_funct_1(A_3)))=k5_relat_1(k2_funct_1(A_3), A_3) | ~v2_funct_1(k2_funct_1(A_3)) | ~v1_funct_1(k2_funct_1(A_3)) | ~v1_relat_1(k2_funct_1(A_3)) | ~v2_funct_1(A_3) | ~v1_funct_1(A_3) | ~v1_relat_1(A_3))), inference(superposition, [status(thm), theory('equality')], [c_12, c_163])).
% 5.56/2.04  tff(c_1249, plain, (k6_partfun1(k1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))))=k6_partfun1(k2_relat_1(k2_funct_1('#skF_3'))) | ~v2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1245, c_172])).
% 5.56/2.04  tff(c_1265, plain, (k6_partfun1(k2_relat_1(k2_funct_1('#skF_3')))=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_450, c_313, c_448, c_600, c_479, c_598, c_1079, c_1249])).
% 5.56/2.04  tff(c_1326, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_2') | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_184, c_1265])).
% 5.56/2.04  tff(c_1345, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_64, c_203, c_450, c_313, c_448, c_1326])).
% 5.56/2.04  tff(c_455, plain, (![A_112, F_108, B_110, D_111, E_109, C_107]: (k1_partfun1(A_112, B_110, C_107, D_111, E_109, F_108)=k5_relat_1(E_109, F_108) | ~m1_subset_1(F_108, k1_zfmisc_1(k2_zfmisc_1(C_107, D_111))) | ~v1_funct_1(F_108) | ~m1_subset_1(E_109, k1_zfmisc_1(k2_zfmisc_1(A_112, B_110))) | ~v1_funct_1(E_109))), inference(cnfTransformation, [status(thm)], [f_122])).
% 5.56/2.04  tff(c_457, plain, (![A_112, B_110, E_109]: (k1_partfun1(A_112, B_110, '#skF_2', '#skF_2', E_109, k2_funct_1('#skF_3'))=k5_relat_1(E_109, k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~m1_subset_1(E_109, k1_zfmisc_1(k2_zfmisc_1(A_112, B_110))) | ~v1_funct_1(E_109))), inference(resolution, [status(thm)], [c_399, c_455])).
% 5.56/2.04  tff(c_2088, plain, (![A_169, B_170, E_171]: (k1_partfun1(A_169, B_170, '#skF_2', '#skF_2', E_171, k2_funct_1('#skF_3'))=k5_relat_1(E_171, k2_funct_1('#skF_3')) | ~m1_subset_1(E_171, k1_zfmisc_1(k2_zfmisc_1(A_169, B_170))) | ~v1_funct_1(E_171))), inference(demodulation, [status(thm), theory('equality')], [c_313, c_457])).
% 5.56/2.04  tff(c_2121, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_1('#skF_3'))=k5_relat_1('#skF_3', k2_funct_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_58, c_2088])).
% 5.56/2.04  tff(c_2140, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_1345, c_2121])).
% 5.56/2.04  tff(c_56, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_2('#skF_2', '#skF_3'), '#skF_3'), k6_partfun1('#skF_2')) | ~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_2('#skF_2', '#skF_3')), k6_partfun1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_155])).
% 5.56/2.04  tff(c_127, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_2('#skF_2', '#skF_3')), k6_partfun1('#skF_2'))), inference(splitLeft, [status(thm)], [c_56])).
% 5.56/2.04  tff(c_314, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_1('#skF_3')), k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_312, c_127])).
% 5.56/2.04  tff(c_2141, plain, (~r2_relset_1('#skF_2', '#skF_2', k6_partfun1('#skF_2'), k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2140, c_314])).
% 5.56/2.04  tff(c_2144, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_272, c_2141])).
% 5.56/2.04  tff(c_2145, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_2('#skF_2', '#skF_3'), '#skF_3'), k6_partfun1('#skF_2'))), inference(splitRight, [status(thm)], [c_56])).
% 5.56/2.04  tff(c_2333, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_1('#skF_3'), '#skF_3'), k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2331, c_2145])).
% 5.56/2.04  tff(c_3343, plain, (~r2_relset_1('#skF_2', '#skF_2', k6_partfun1('#skF_2'), k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_3342, c_2333])).
% 5.56/2.04  tff(c_3346, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2291, c_3343])).
% 5.56/2.04  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.56/2.04  
% 5.56/2.04  Inference rules
% 5.56/2.04  ----------------------
% 5.56/2.04  #Ref     : 0
% 5.56/2.04  #Sup     : 784
% 5.56/2.04  #Fact    : 0
% 5.56/2.04  #Define  : 0
% 5.56/2.04  #Split   : 2
% 5.56/2.04  #Chain   : 0
% 5.56/2.04  #Close   : 0
% 5.56/2.04  
% 5.56/2.04  Ordering : KBO
% 5.56/2.04  
% 5.56/2.04  Simplification rules
% 5.56/2.04  ----------------------
% 5.56/2.04  #Subsume      : 89
% 5.56/2.04  #Demod        : 1409
% 5.56/2.04  #Tautology    : 338
% 5.56/2.04  #SimpNegUnit  : 0
% 5.56/2.04  #BackRed      : 31
% 5.56/2.04  
% 5.56/2.04  #Partial instantiations: 0
% 5.56/2.04  #Strategies tried      : 1
% 5.56/2.04  
% 5.56/2.04  Timing (in seconds)
% 5.56/2.04  ----------------------
% 5.56/2.04  Preprocessing        : 0.34
% 5.56/2.04  Parsing              : 0.18
% 5.56/2.04  CNF conversion       : 0.02
% 5.56/2.04  Main loop            : 0.90
% 5.56/2.04  Inferencing          : 0.31
% 5.56/2.04  Reduction            : 0.35
% 5.56/2.04  Demodulation         : 0.27
% 5.56/2.04  BG Simplification    : 0.03
% 5.56/2.04  Subsumption          : 0.14
% 5.56/2.04  Abstraction          : 0.05
% 5.56/2.04  MUC search           : 0.00
% 5.56/2.04  Cooper               : 0.00
% 5.56/2.04  Total                : 1.31
% 5.56/2.04  Index Insertion      : 0.00
% 5.56/2.04  Index Deletion       : 0.00
% 5.56/2.04  Index Matching       : 0.00
% 5.56/2.04  BG Taut test         : 0.00
%------------------------------------------------------------------------------
