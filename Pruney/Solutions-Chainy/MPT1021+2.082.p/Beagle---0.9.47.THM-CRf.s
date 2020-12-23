%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:12 EST 2020

% Result     : Theorem 5.91s
% Output     : CNFRefutation 6.30s
% Verified   : 
% Statistics : Number of formulae       :  200 (6976 expanded)
%              Number of leaves         :   43 (2821 expanded)
%              Depth                    :   21
%              Number of atoms          :  464 (25489 expanded)
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

tff(f_102,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_113,axiom,(
    ! [A,B] :
    ? [C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
      & v1_relat_1(C)
      & v4_relat_1(C,A)
      & v5_relat_1(C,B)
      & v1_funct_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_partfun1)).

tff(f_70,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_156,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & v3_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ( r2_relset_1(A,A,k1_partfun1(A,A,A,A,B,k2_funct_2(A,B)),k6_partfun1(A))
          & r2_relset_1(A,A,k1_partfun1(A,A,A,A,k2_funct_2(A,B),B),k6_partfun1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_funct_2)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_60,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(k2_funct_1(A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).

tff(f_133,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k2_funct_2(A,B) = k2_funct_1(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

tff(f_98,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => ( v1_funct_1(k2_funct_2(A,B))
        & v1_funct_2(k2_funct_2(A,B),A,A)
        & v3_funct_2(k2_funct_2(A,B),A,A)
        & m1_subset_1(k2_funct_2(A,B),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_2)).

tff(f_143,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k1_relset_1(A,A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_2)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_135,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_44,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_123,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(c_34,plain,(
    ! [A_21] : m1_subset_1(k6_partfun1(A_21),k1_zfmisc_1(k2_zfmisc_1(A_21,A_21))) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_44,plain,(
    ! [A_22,B_23] : m1_subset_1('#skF_1'(A_22,B_23),k1_zfmisc_1(k2_zfmisc_1(A_22,B_23))) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_2274,plain,(
    ! [A_190,B_191,C_192,D_193] :
      ( r2_relset_1(A_190,B_191,C_192,C_192)
      | ~ m1_subset_1(D_193,k1_zfmisc_1(k2_zfmisc_1(A_190,B_191)))
      | ~ m1_subset_1(C_192,k1_zfmisc_1(k2_zfmisc_1(A_190,B_191))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2284,plain,(
    ! [A_194,B_195,C_196] :
      ( r2_relset_1(A_194,B_195,C_196,C_196)
      | ~ m1_subset_1(C_196,k1_zfmisc_1(k2_zfmisc_1(A_194,B_195))) ) ),
    inference(resolution,[status(thm)],[c_44,c_2274])).

tff(c_2292,plain,(
    ! [A_21] : r2_relset_1(A_21,A_21,k6_partfun1(A_21),k6_partfun1(A_21)) ),
    inference(resolution,[status(thm)],[c_34,c_2284])).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_56,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_81,plain,(
    ! [B_49,A_50] :
      ( v1_relat_1(B_49)
      | ~ m1_subset_1(B_49,k1_zfmisc_1(A_50))
      | ~ v1_relat_1(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_87,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_2')) ),
    inference(resolution,[status(thm)],[c_56,c_81])).

tff(c_93,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_87])).

tff(c_62,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_58,plain,(
    v3_funct_2('#skF_3','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_2237,plain,(
    ! [C_179,A_180,B_181] :
      ( v2_funct_1(C_179)
      | ~ v3_funct_2(C_179,A_180,B_181)
      | ~ v1_funct_1(C_179)
      | ~ m1_subset_1(C_179,k1_zfmisc_1(k2_zfmisc_1(A_180,B_181))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_2246,plain,
    ( v2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_2237])).

tff(c_2253,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_2246])).

tff(c_12,plain,(
    ! [A_8] :
      ( k2_funct_1(k2_funct_1(A_8)) = A_8
      | ~ v2_funct_1(A_8)
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_60,plain,(
    v1_funct_2('#skF_3','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_2346,plain,(
    ! [A_208,B_209] :
      ( k2_funct_2(A_208,B_209) = k2_funct_1(B_209)
      | ~ m1_subset_1(B_209,k1_zfmisc_1(k2_zfmisc_1(A_208,A_208)))
      | ~ v3_funct_2(B_209,A_208,A_208)
      | ~ v1_funct_2(B_209,A_208,A_208)
      | ~ v1_funct_1(B_209) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_2356,plain,
    ( k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_2346])).

tff(c_2363,plain,(
    k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_2356])).

tff(c_2406,plain,(
    ! [A_219,B_220] :
      ( m1_subset_1(k2_funct_2(A_219,B_220),k1_zfmisc_1(k2_zfmisc_1(A_219,A_219)))
      | ~ m1_subset_1(B_220,k1_zfmisc_1(k2_zfmisc_1(A_219,A_219)))
      | ~ v3_funct_2(B_220,A_219,A_219)
      | ~ v1_funct_2(B_220,A_219,A_219)
      | ~ v1_funct_1(B_220) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_2436,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2363,c_2406])).

tff(c_2450,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_56,c_2436])).

tff(c_2,plain,(
    ! [B_3,A_1] :
      ( v1_relat_1(B_3)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(A_1))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2477,plain,
    ( v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_2')) ),
    inference(resolution,[status(thm)],[c_2450,c_2])).

tff(c_2503,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_2477])).

tff(c_2325,plain,(
    ! [A_203,B_204] :
      ( v1_funct_1(k2_funct_2(A_203,B_204))
      | ~ m1_subset_1(B_204,k1_zfmisc_1(k2_zfmisc_1(A_203,A_203)))
      | ~ v3_funct_2(B_204,A_203,A_203)
      | ~ v1_funct_2(B_204,A_203,A_203)
      | ~ v1_funct_1(B_204) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_2335,plain,
    ( v1_funct_1(k2_funct_2('#skF_2','#skF_3'))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_2325])).

tff(c_2342,plain,(
    v1_funct_1(k2_funct_2('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_2335])).

tff(c_2364,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2363,c_2342])).

tff(c_2389,plain,(
    ! [A_215,B_216] :
      ( v3_funct_2(k2_funct_2(A_215,B_216),A_215,A_215)
      | ~ m1_subset_1(B_216,k1_zfmisc_1(k2_zfmisc_1(A_215,A_215)))
      | ~ v3_funct_2(B_216,A_215,A_215)
      | ~ v1_funct_2(B_216,A_215,A_215)
      | ~ v1_funct_1(B_216) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_2396,plain,
    ( v3_funct_2(k2_funct_2('#skF_2','#skF_3'),'#skF_2','#skF_2')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_2389])).

tff(c_2403,plain,(
    v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_2363,c_2396])).

tff(c_20,plain,(
    ! [C_18,A_16,B_17] :
      ( v2_funct_1(C_18)
      | ~ v3_funct_2(C_18,A_16,B_17)
      | ~ v1_funct_1(C_18)
      | ~ m1_subset_1(C_18,k1_zfmisc_1(k2_zfmisc_1(A_16,B_17))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_2471,plain,
    ( v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2450,c_20])).

tff(c_2499,plain,(
    v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2364,c_2403,c_2471])).

tff(c_2374,plain,(
    ! [A_213,B_214] :
      ( v1_funct_2(k2_funct_2(A_213,B_214),A_213,A_213)
      | ~ m1_subset_1(B_214,k1_zfmisc_1(k2_zfmisc_1(A_213,A_213)))
      | ~ v3_funct_2(B_214,A_213,A_213)
      | ~ v1_funct_2(B_214,A_213,A_213)
      | ~ v1_funct_1(B_214) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_2381,plain,
    ( v1_funct_2(k2_funct_2('#skF_2','#skF_3'),'#skF_2','#skF_2')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_2374])).

tff(c_2388,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_2363,c_2381])).

tff(c_52,plain,(
    ! [A_34,B_35] :
      ( k1_relset_1(A_34,A_34,B_35) = A_34
      | ~ m1_subset_1(B_35,k1_zfmisc_1(k2_zfmisc_1(A_34,A_34)))
      | ~ v1_funct_2(B_35,A_34,A_34)
      | ~ v1_funct_1(B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_2463,plain,
    ( k1_relset_1('#skF_2','#skF_2',k2_funct_1('#skF_3')) = '#skF_2'
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2450,c_52])).

tff(c_2492,plain,(
    k1_relset_1('#skF_2','#skF_2',k2_funct_1('#skF_3')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2364,c_2388,c_2463])).

tff(c_14,plain,(
    ! [A_9,B_10,C_11] :
      ( k1_relset_1(A_9,B_10,C_11) = k1_relat_1(C_11)
      | ~ m1_subset_1(C_11,k1_zfmisc_1(k2_zfmisc_1(A_9,B_10))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_2500,plain,(
    k1_relset_1('#skF_2','#skF_2',k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2450,c_14])).

tff(c_2584,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2492,c_2500])).

tff(c_48,plain,(
    ! [A_31,B_32] :
      ( k2_funct_2(A_31,B_32) = k2_funct_1(B_32)
      | ~ m1_subset_1(B_32,k1_zfmisc_1(k2_zfmisc_1(A_31,A_31)))
      | ~ v3_funct_2(B_32,A_31,A_31)
      | ~ v1_funct_2(B_32,A_31,A_31)
      | ~ v1_funct_1(B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_2457,plain,
    ( k2_funct_2('#skF_2',k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3'))
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2450,c_48])).

tff(c_2486,plain,(
    k2_funct_2('#skF_2',k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2364,c_2388,c_2403,c_2457])).

tff(c_2433,plain,(
    ! [A_219,B_220] :
      ( v1_relat_1(k2_funct_2(A_219,B_220))
      | ~ v1_relat_1(k2_zfmisc_1(A_219,A_219))
      | ~ m1_subset_1(B_220,k1_zfmisc_1(k2_zfmisc_1(A_219,A_219)))
      | ~ v3_funct_2(B_220,A_219,A_219)
      | ~ v1_funct_2(B_220,A_219,A_219)
      | ~ v1_funct_1(B_220) ) ),
    inference(resolution,[status(thm)],[c_2406,c_2])).

tff(c_2589,plain,(
    ! [A_230,B_231] :
      ( v1_relat_1(k2_funct_2(A_230,B_231))
      | ~ m1_subset_1(B_231,k1_zfmisc_1(k2_zfmisc_1(A_230,A_230)))
      | ~ v3_funct_2(B_231,A_230,A_230)
      | ~ v1_funct_2(B_231,A_230,A_230)
      | ~ v1_funct_1(B_231) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_2433])).

tff(c_2592,plain,
    ( v1_relat_1(k2_funct_2('#skF_2',k2_funct_1('#skF_3')))
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2450,c_2589])).

tff(c_2608,plain,(
    v1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2364,c_2388,c_2403,c_2486,c_2592])).

tff(c_30,plain,(
    ! [A_19,B_20] :
      ( v1_funct_1(k2_funct_2(A_19,B_20))
      | ~ m1_subset_1(B_20,k1_zfmisc_1(k2_zfmisc_1(A_19,A_19)))
      | ~ v3_funct_2(B_20,A_19,A_19)
      | ~ v1_funct_2(B_20,A_19,A_19)
      | ~ v1_funct_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_2460,plain,
    ( v1_funct_1(k2_funct_2('#skF_2',k2_funct_1('#skF_3')))
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2450,c_30])).

tff(c_2489,plain,(
    v1_funct_1(k2_funct_2('#skF_2',k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2364,c_2388,c_2403,c_2460])).

tff(c_2558,plain,(
    v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2486,c_2489])).

tff(c_26,plain,(
    ! [A_19,B_20] :
      ( v3_funct_2(k2_funct_2(A_19,B_20),A_19,A_19)
      | ~ m1_subset_1(B_20,k1_zfmisc_1(k2_zfmisc_1(A_19,A_19)))
      | ~ v3_funct_2(B_20,A_19,A_19)
      | ~ v1_funct_2(B_20,A_19,A_19)
      | ~ v1_funct_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_2452,plain,
    ( v3_funct_2(k2_funct_2('#skF_2',k2_funct_1('#skF_3')),'#skF_2','#skF_2')
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2450,c_26])).

tff(c_2480,plain,(
    v3_funct_2(k2_funct_2('#skF_2',k2_funct_1('#skF_3')),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2364,c_2388,c_2403,c_2452])).

tff(c_2557,plain,(
    v3_funct_2(k2_funct_1(k2_funct_1('#skF_3')),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2486,c_2480])).

tff(c_24,plain,(
    ! [A_19,B_20] :
      ( m1_subset_1(k2_funct_2(A_19,B_20),k1_zfmisc_1(k2_zfmisc_1(A_19,A_19)))
      | ~ m1_subset_1(B_20,k1_zfmisc_1(k2_zfmisc_1(A_19,A_19)))
      | ~ v3_funct_2(B_20,A_19,A_19)
      | ~ v1_funct_2(B_20,A_19,A_19)
      | ~ v1_funct_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_2562,plain,
    ( m1_subset_1(k2_funct_1(k2_funct_1('#skF_3')),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2486,c_24])).

tff(c_2566,plain,(
    m1_subset_1(k2_funct_1(k2_funct_1('#skF_3')),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2364,c_2388,c_2403,c_2450,c_2562])).

tff(c_2650,plain,
    ( v2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v3_funct_2(k2_funct_1(k2_funct_1('#skF_3')),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_2566,c_20])).

tff(c_2690,plain,(
    v2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2558,c_2557,c_2650])).

tff(c_28,plain,(
    ! [A_19,B_20] :
      ( v1_funct_2(k2_funct_2(A_19,B_20),A_19,A_19)
      | ~ m1_subset_1(B_20,k1_zfmisc_1(k2_zfmisc_1(A_19,A_19)))
      | ~ v3_funct_2(B_20,A_19,A_19)
      | ~ v1_funct_2(B_20,A_19,A_19)
      | ~ v1_funct_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_2454,plain,
    ( v1_funct_2(k2_funct_2('#skF_2',k2_funct_1('#skF_3')),'#skF_2','#skF_2')
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2450,c_28])).

tff(c_2483,plain,(
    v1_funct_2(k2_funct_2('#skF_2',k2_funct_1('#skF_3')),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2364,c_2388,c_2403,c_2454])).

tff(c_2578,plain,(
    v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2486,c_2483])).

tff(c_2636,plain,
    ( k2_funct_2('#skF_2',k2_funct_1(k2_funct_1('#skF_3'))) = k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v3_funct_2(k2_funct_1(k2_funct_1('#skF_3')),'#skF_2','#skF_2')
    | ~ v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_2566,c_48])).

tff(c_2677,plain,(
    k2_funct_2('#skF_2',k2_funct_1(k2_funct_1('#skF_3'))) = k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2558,c_2578,c_2557,c_2636])).

tff(c_2752,plain,
    ( k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) = k2_funct_2('#skF_2','#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_2677])).

tff(c_2758,plain,(
    k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_62,c_2253,c_2363,c_2752])).

tff(c_50,plain,(
    ! [A_33] : k6_relat_1(A_33) = k6_partfun1(A_33) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_6,plain,(
    ! [A_6] :
      ( k5_relat_1(k2_funct_1(A_6),A_6) = k6_relat_1(k2_relat_1(A_6))
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_64,plain,(
    ! [A_6] :
      ( k5_relat_1(k2_funct_1(A_6),A_6) = k6_partfun1(k2_relat_1(A_6))
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_6])).

tff(c_2791,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),k2_funct_1(k2_funct_1('#skF_3'))) = k6_partfun1(k2_relat_1(k2_funct_1(k2_funct_1('#skF_3'))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2758,c_64])).

tff(c_2812,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),k2_funct_1(k2_funct_1('#skF_3'))) = k6_partfun1(k2_relat_1(k2_funct_1(k2_funct_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2608,c_2558,c_2690,c_2791])).

tff(c_8,plain,(
    ! [A_6] :
      ( k5_relat_1(A_6,k2_funct_1(A_6)) = k6_relat_1(k1_relat_1(A_6))
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_63,plain,(
    ! [A_6] :
      ( k5_relat_1(A_6,k2_funct_1(A_6)) = k6_partfun1(k1_relat_1(A_6))
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_8])).

tff(c_2907,plain,
    ( k6_partfun1(k2_relat_1(k2_funct_1(k2_funct_1('#skF_3')))) = k6_partfun1(k1_relat_1(k2_funct_1('#skF_3')))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2812,c_63])).

tff(c_2917,plain,(
    k6_partfun1(k2_relat_1(k2_funct_1(k2_funct_1('#skF_3')))) = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2503,c_2364,c_2499,c_2584,c_2907])).

tff(c_2923,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),k2_funct_1(k2_funct_1('#skF_3'))) = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2917,c_2812])).

tff(c_3087,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_2923])).

tff(c_3095,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_62,c_2253,c_3087])).

tff(c_2504,plain,(
    ! [D_221,F_224,B_225,C_223,A_222,E_226] :
      ( k1_partfun1(A_222,B_225,C_223,D_221,E_226,F_224) = k5_relat_1(E_226,F_224)
      | ~ m1_subset_1(F_224,k1_zfmisc_1(k2_zfmisc_1(C_223,D_221)))
      | ~ v1_funct_1(F_224)
      | ~ m1_subset_1(E_226,k1_zfmisc_1(k2_zfmisc_1(A_222,B_225)))
      | ~ v1_funct_1(E_226) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_2514,plain,(
    ! [A_222,B_225,E_226] :
      ( k1_partfun1(A_222,B_225,'#skF_2','#skF_2',E_226,'#skF_3') = k5_relat_1(E_226,'#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(E_226,k1_zfmisc_1(k2_zfmisc_1(A_222,B_225)))
      | ~ v1_funct_1(E_226) ) ),
    inference(resolution,[status(thm)],[c_56,c_2504])).

tff(c_2530,plain,(
    ! [A_227,B_228,E_229] :
      ( k1_partfun1(A_227,B_228,'#skF_2','#skF_2',E_229,'#skF_3') = k5_relat_1(E_229,'#skF_3')
      | ~ m1_subset_1(E_229,k1_zfmisc_1(k2_zfmisc_1(A_227,B_228)))
      | ~ v1_funct_1(E_229) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_2514])).

tff(c_2865,plain,(
    ! [A_235,B_236] :
      ( k1_partfun1(A_235,A_235,'#skF_2','#skF_2',k2_funct_2(A_235,B_236),'#skF_3') = k5_relat_1(k2_funct_2(A_235,B_236),'#skF_3')
      | ~ v1_funct_1(k2_funct_2(A_235,B_236))
      | ~ m1_subset_1(B_236,k1_zfmisc_1(k2_zfmisc_1(A_235,A_235)))
      | ~ v3_funct_2(B_236,A_235,A_235)
      | ~ v1_funct_2(B_236,A_235,A_235)
      | ~ v1_funct_1(B_236) ) ),
    inference(resolution,[status(thm)],[c_24,c_2530])).

tff(c_2878,plain,
    ( k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_2('#skF_2','#skF_3'),'#skF_3') = k5_relat_1(k2_funct_2('#skF_2','#skF_3'),'#skF_3')
    | ~ v1_funct_1(k2_funct_2('#skF_2','#skF_3'))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_2865])).

tff(c_2892,plain,(
    k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_1('#skF_3'),'#skF_3') = k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_2364,c_2363,c_2363,c_2363,c_2878])).

tff(c_240,plain,(
    ! [A_78,B_79,C_80,D_81] :
      ( r2_relset_1(A_78,B_79,C_80,C_80)
      | ~ m1_subset_1(D_81,k1_zfmisc_1(k2_zfmisc_1(A_78,B_79)))
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1(A_78,B_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_271,plain,(
    ! [A_83,C_84] :
      ( r2_relset_1(A_83,A_83,C_84,C_84)
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1(A_83,A_83))) ) ),
    inference(resolution,[status(thm)],[c_34,c_240])).

tff(c_280,plain,(
    ! [A_21] : r2_relset_1(A_21,A_21,k6_partfun1(A_21),k6_partfun1(A_21)) ),
    inference(resolution,[status(thm)],[c_34,c_271])).

tff(c_183,plain,(
    ! [C_64,A_65,B_66] :
      ( v2_funct_1(C_64)
      | ~ v3_funct_2(C_64,A_65,B_66)
      | ~ v1_funct_1(C_64)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_192,plain,
    ( v2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_183])).

tff(c_199,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_192])).

tff(c_319,plain,(
    ! [A_94,B_95] :
      ( k2_funct_2(A_94,B_95) = k2_funct_1(B_95)
      | ~ m1_subset_1(B_95,k1_zfmisc_1(k2_zfmisc_1(A_94,A_94)))
      | ~ v3_funct_2(B_95,A_94,A_94)
      | ~ v1_funct_2(B_95,A_94,A_94)
      | ~ v1_funct_1(B_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_329,plain,
    ( k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_319])).

tff(c_336,plain,(
    k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_329])).

tff(c_287,plain,(
    ! [A_87,B_88] :
      ( v1_funct_1(k2_funct_2(A_87,B_88))
      | ~ m1_subset_1(B_88,k1_zfmisc_1(k2_zfmisc_1(A_87,A_87)))
      | ~ v3_funct_2(B_88,A_87,A_87)
      | ~ v1_funct_2(B_88,A_87,A_87)
      | ~ v1_funct_1(B_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_297,plain,
    ( v1_funct_1(k2_funct_2('#skF_2','#skF_3'))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_287])).

tff(c_304,plain,(
    v1_funct_1(k2_funct_2('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_297])).

tff(c_337,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_336,c_304])).

tff(c_362,plain,(
    ! [A_102,B_103] :
      ( v1_funct_2(k2_funct_2(A_102,B_103),A_102,A_102)
      | ~ m1_subset_1(B_103,k1_zfmisc_1(k2_zfmisc_1(A_102,A_102)))
      | ~ v3_funct_2(B_103,A_102,A_102)
      | ~ v1_funct_2(B_103,A_102,A_102)
      | ~ v1_funct_1(B_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_369,plain,
    ( v1_funct_2(k2_funct_2('#skF_2','#skF_3'),'#skF_2','#skF_2')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_362])).

tff(c_376,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_336,c_369])).

tff(c_345,plain,(
    ! [A_98,B_99] :
      ( v3_funct_2(k2_funct_2(A_98,B_99),A_98,A_98)
      | ~ m1_subset_1(B_99,k1_zfmisc_1(k2_zfmisc_1(A_98,A_98)))
      | ~ v3_funct_2(B_99,A_98,A_98)
      | ~ v1_funct_2(B_99,A_98,A_98)
      | ~ v1_funct_1(B_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_352,plain,
    ( v3_funct_2(k2_funct_2('#skF_2','#skF_3'),'#skF_2','#skF_2')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_345])).

tff(c_359,plain,(
    v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_336,c_352])).

tff(c_381,plain,(
    ! [A_108,B_109] :
      ( m1_subset_1(k2_funct_2(A_108,B_109),k1_zfmisc_1(k2_zfmisc_1(A_108,A_108)))
      | ~ m1_subset_1(B_109,k1_zfmisc_1(k2_zfmisc_1(A_108,A_108)))
      | ~ v3_funct_2(B_109,A_108,A_108)
      | ~ v1_funct_2(B_109,A_108,A_108)
      | ~ v1_funct_1(B_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_411,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_336,c_381])).

tff(c_425,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_56,c_411])).

tff(c_432,plain,
    ( k2_funct_2('#skF_2',k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3'))
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_425,c_48])).

tff(c_461,plain,(
    k2_funct_2('#skF_2',k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_337,c_376,c_359,c_432])).

tff(c_437,plain,
    ( v1_funct_1(k2_funct_2('#skF_2',k2_funct_1('#skF_3')))
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_425,c_30])).

tff(c_465,plain,(
    v1_funct_1(k2_funct_2('#skF_2',k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_337,c_376,c_359,c_437])).

tff(c_484,plain,(
    v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_461,c_465])).

tff(c_427,plain,
    ( v1_funct_2(k2_funct_2('#skF_2',k2_funct_1('#skF_3')),'#skF_2','#skF_2')
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_425,c_28])).

tff(c_455,plain,(
    v1_funct_2(k2_funct_2('#skF_2',k2_funct_1('#skF_3')),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_337,c_376,c_359,c_427])).

tff(c_526,plain,(
    v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_461,c_455])).

tff(c_488,plain,
    ( m1_subset_1(k2_funct_1(k2_funct_1('#skF_3')),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_461,c_24])).

tff(c_492,plain,(
    m1_subset_1(k2_funct_1(k2_funct_1('#skF_3')),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_337,c_376,c_359,c_425,c_488])).

tff(c_583,plain,
    ( k1_relset_1('#skF_2','#skF_2',k2_funct_1(k2_funct_1('#skF_3'))) = '#skF_2'
    | ~ v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_492,c_52])).

tff(c_620,plain,(
    k1_relset_1('#skF_2','#skF_2',k2_funct_1(k2_funct_1('#skF_3'))) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_484,c_526,c_583])).

tff(c_627,plain,(
    k1_relset_1('#skF_2','#skF_2',k2_funct_1(k2_funct_1('#skF_3'))) = k1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_492,c_14])).

tff(c_841,plain,(
    k1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_620,c_627])).

tff(c_595,plain,
    ( v1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_2')) ),
    inference(resolution,[status(thm)],[c_492,c_2])).

tff(c_630,plain,(
    v1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_595])).

tff(c_429,plain,
    ( v3_funct_2(k2_funct_2('#skF_2',k2_funct_1('#skF_3')),'#skF_2','#skF_2')
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_425,c_26])).

tff(c_458,plain,(
    v3_funct_2(k2_funct_2('#skF_2',k2_funct_1('#skF_3')),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_337,c_376,c_359,c_429])).

tff(c_483,plain,(
    v3_funct_2(k2_funct_1(k2_funct_1('#skF_3')),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_461,c_458])).

tff(c_589,plain,
    ( v2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v3_funct_2(k2_funct_1(k2_funct_1('#skF_3')),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_492,c_20])).

tff(c_626,plain,(
    v2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_484,c_483,c_589])).

tff(c_575,plain,
    ( k2_funct_2('#skF_2',k2_funct_1(k2_funct_1('#skF_3'))) = k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v3_funct_2(k2_funct_1(k2_funct_1('#skF_3')),'#skF_2','#skF_2')
    | ~ v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_492,c_48])).

tff(c_613,plain,(
    k2_funct_2('#skF_2',k2_funct_1(k2_funct_1('#skF_3'))) = k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_484,c_526,c_483,c_575])).

tff(c_747,plain,
    ( k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) = k2_funct_2('#skF_2','#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_613])).

tff(c_753,plain,(
    k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_62,c_199,c_336,c_747])).

tff(c_783,plain,
    ( k5_relat_1(k2_funct_1(k2_funct_1('#skF_3')),k2_funct_1('#skF_3')) = k6_partfun1(k1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_753,c_63])).

tff(c_805,plain,(
    k5_relat_1(k2_funct_1(k2_funct_1('#skF_3')),k2_funct_1('#skF_3')) = k6_partfun1(k1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_630,c_484,c_626,c_783])).

tff(c_851,plain,(
    k5_relat_1(k2_funct_1(k2_funct_1('#skF_3')),k2_funct_1('#skF_3')) = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_841,c_805])).

tff(c_862,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_851])).

tff(c_870,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_62,c_199,c_862])).

tff(c_494,plain,(
    ! [E_115,F_113,A_111,B_114,D_110,C_112] :
      ( k1_partfun1(A_111,B_114,C_112,D_110,E_115,F_113) = k5_relat_1(E_115,F_113)
      | ~ m1_subset_1(F_113,k1_zfmisc_1(k2_zfmisc_1(C_112,D_110)))
      | ~ v1_funct_1(F_113)
      | ~ m1_subset_1(E_115,k1_zfmisc_1(k2_zfmisc_1(A_111,B_114)))
      | ~ v1_funct_1(E_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_496,plain,(
    ! [A_111,B_114,E_115] :
      ( k1_partfun1(A_111,B_114,'#skF_2','#skF_2',E_115,k2_funct_1('#skF_3')) = k5_relat_1(E_115,k2_funct_1('#skF_3'))
      | ~ v1_funct_1(k2_funct_1('#skF_3'))
      | ~ m1_subset_1(E_115,k1_zfmisc_1(k2_zfmisc_1(A_111,B_114)))
      | ~ v1_funct_1(E_115) ) ),
    inference(resolution,[status(thm)],[c_425,c_494])).

tff(c_2132,plain,(
    ! [A_171,B_172,E_173] :
      ( k1_partfun1(A_171,B_172,'#skF_2','#skF_2',E_173,k2_funct_1('#skF_3')) = k5_relat_1(E_173,k2_funct_1('#skF_3'))
      | ~ m1_subset_1(E_173,k1_zfmisc_1(k2_zfmisc_1(A_171,B_172)))
      | ~ v1_funct_1(E_173) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_337,c_496])).

tff(c_2165,plain,
    ( k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_1('#skF_3')) = k5_relat_1('#skF_3',k2_funct_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_2132])).

tff(c_2184,plain,(
    k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_870,c_2165])).

tff(c_54,plain,
    ( ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_2('#skF_2','#skF_3'),'#skF_3'),k6_partfun1('#skF_2'))
    | ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_2('#skF_2','#skF_3')),k6_partfun1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_136,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_2('#skF_2','#skF_3')),k6_partfun1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_338,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_1('#skF_3')),k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_336,c_136])).

tff(c_2185,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k6_partfun1('#skF_2'),k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2184,c_338])).

tff(c_2188,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_280,c_2185])).

tff(c_2189,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_2('#skF_2','#skF_3'),'#skF_3'),k6_partfun1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_2366,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_1('#skF_3'),'#skF_3'),k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2363,c_2189])).

tff(c_3072,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k5_relat_1(k2_funct_1('#skF_3'),'#skF_3'),k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2892,c_2366])).

tff(c_3112,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2292,c_3095,c_3072])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:41:19 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.91/2.17  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.91/2.19  
% 5.91/2.19  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.91/2.21  %$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 5.91/2.21  
% 5.91/2.21  %Foreground sorts:
% 5.91/2.21  
% 5.91/2.21  
% 5.91/2.21  %Background operators:
% 5.91/2.21  
% 5.91/2.21  
% 5.91/2.21  %Foreground operators:
% 5.91/2.21  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.91/2.21  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 5.91/2.21  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.91/2.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.91/2.21  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 5.91/2.21  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 5.91/2.21  tff(k2_funct_2, type, k2_funct_2: ($i * $i) > $i).
% 5.91/2.21  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.91/2.21  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.91/2.21  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.91/2.21  tff('#skF_2', type, '#skF_2': $i).
% 5.91/2.21  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 5.91/2.21  tff('#skF_3', type, '#skF_3': $i).
% 5.91/2.21  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 5.91/2.21  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.91/2.21  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.91/2.21  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.91/2.21  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 5.91/2.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.91/2.21  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.91/2.21  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.91/2.21  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 5.91/2.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.91/2.21  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.91/2.21  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 5.91/2.21  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.91/2.21  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.91/2.21  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.91/2.21  
% 6.30/2.24  tff(f_102, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 6.30/2.24  tff(f_113, axiom, (![A, B]: (?[C]: ((((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & v1_relat_1(C)) & v4_relat_1(C, A)) & v5_relat_1(C, B)) & v1_funct_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc1_partfun1)).
% 6.30/2.24  tff(f_70, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 6.30/2.24  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 6.30/2.24  tff(f_156, negated_conjecture, ~(![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, k2_funct_2(A, B)), k6_partfun1(A)) & r2_relset_1(A, A, k1_partfun1(A, A, A, A, k2_funct_2(A, B), B), k6_partfun1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_funct_2)).
% 6.30/2.24  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 6.30/2.24  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_funct_2)).
% 6.30/2.24  tff(f_60, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(k2_funct_1(A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_1)).
% 6.30/2.24  tff(f_133, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k2_funct_2(A, B) = k2_funct_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 6.30/2.24  tff(f_98, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (((v1_funct_1(k2_funct_2(A, B)) & v1_funct_2(k2_funct_2(A, B), A, A)) & v3_funct_2(k2_funct_2(A, B), A, A)) & m1_subset_1(k2_funct_2(A, B), k1_zfmisc_1(k2_zfmisc_1(A, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_2)).
% 6.30/2.24  tff(f_143, axiom, (![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k1_relset_1(A, A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_funct_2)).
% 6.30/2.24  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 6.30/2.24  tff(f_135, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 6.30/2.24  tff(f_44, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 6.30/2.24  tff(f_123, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 6.30/2.24  tff(c_34, plain, (![A_21]: (m1_subset_1(k6_partfun1(A_21), k1_zfmisc_1(k2_zfmisc_1(A_21, A_21))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 6.30/2.24  tff(c_44, plain, (![A_22, B_23]: (m1_subset_1('#skF_1'(A_22, B_23), k1_zfmisc_1(k2_zfmisc_1(A_22, B_23))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 6.30/2.24  tff(c_2274, plain, (![A_190, B_191, C_192, D_193]: (r2_relset_1(A_190, B_191, C_192, C_192) | ~m1_subset_1(D_193, k1_zfmisc_1(k2_zfmisc_1(A_190, B_191))) | ~m1_subset_1(C_192, k1_zfmisc_1(k2_zfmisc_1(A_190, B_191))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.30/2.24  tff(c_2284, plain, (![A_194, B_195, C_196]: (r2_relset_1(A_194, B_195, C_196, C_196) | ~m1_subset_1(C_196, k1_zfmisc_1(k2_zfmisc_1(A_194, B_195))))), inference(resolution, [status(thm)], [c_44, c_2274])).
% 6.30/2.24  tff(c_2292, plain, (![A_21]: (r2_relset_1(A_21, A_21, k6_partfun1(A_21), k6_partfun1(A_21)))), inference(resolution, [status(thm)], [c_34, c_2284])).
% 6.30/2.24  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 6.30/2.24  tff(c_56, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_156])).
% 6.30/2.24  tff(c_81, plain, (![B_49, A_50]: (v1_relat_1(B_49) | ~m1_subset_1(B_49, k1_zfmisc_1(A_50)) | ~v1_relat_1(A_50))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.30/2.24  tff(c_87, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_2'))), inference(resolution, [status(thm)], [c_56, c_81])).
% 6.30/2.24  tff(c_93, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_87])).
% 6.30/2.24  tff(c_62, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_156])).
% 6.30/2.24  tff(c_58, plain, (v3_funct_2('#skF_3', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_156])).
% 6.30/2.24  tff(c_2237, plain, (![C_179, A_180, B_181]: (v2_funct_1(C_179) | ~v3_funct_2(C_179, A_180, B_181) | ~v1_funct_1(C_179) | ~m1_subset_1(C_179, k1_zfmisc_1(k2_zfmisc_1(A_180, B_181))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 6.30/2.24  tff(c_2246, plain, (v2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_56, c_2237])).
% 6.30/2.24  tff(c_2253, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_58, c_2246])).
% 6.30/2.24  tff(c_12, plain, (![A_8]: (k2_funct_1(k2_funct_1(A_8))=A_8 | ~v2_funct_1(A_8) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_60])).
% 6.30/2.24  tff(c_60, plain, (v1_funct_2('#skF_3', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_156])).
% 6.30/2.24  tff(c_2346, plain, (![A_208, B_209]: (k2_funct_2(A_208, B_209)=k2_funct_1(B_209) | ~m1_subset_1(B_209, k1_zfmisc_1(k2_zfmisc_1(A_208, A_208))) | ~v3_funct_2(B_209, A_208, A_208) | ~v1_funct_2(B_209, A_208, A_208) | ~v1_funct_1(B_209))), inference(cnfTransformation, [status(thm)], [f_133])).
% 6.30/2.24  tff(c_2356, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_56, c_2346])).
% 6.30/2.24  tff(c_2363, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_2356])).
% 6.30/2.24  tff(c_2406, plain, (![A_219, B_220]: (m1_subset_1(k2_funct_2(A_219, B_220), k1_zfmisc_1(k2_zfmisc_1(A_219, A_219))) | ~m1_subset_1(B_220, k1_zfmisc_1(k2_zfmisc_1(A_219, A_219))) | ~v3_funct_2(B_220, A_219, A_219) | ~v1_funct_2(B_220, A_219, A_219) | ~v1_funct_1(B_220))), inference(cnfTransformation, [status(thm)], [f_98])).
% 6.30/2.24  tff(c_2436, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2363, c_2406])).
% 6.30/2.24  tff(c_2450, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_56, c_2436])).
% 6.30/2.24  tff(c_2, plain, (![B_3, A_1]: (v1_relat_1(B_3) | ~m1_subset_1(B_3, k1_zfmisc_1(A_1)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.30/2.24  tff(c_2477, plain, (v1_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_2'))), inference(resolution, [status(thm)], [c_2450, c_2])).
% 6.30/2.24  tff(c_2503, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_2477])).
% 6.30/2.24  tff(c_2325, plain, (![A_203, B_204]: (v1_funct_1(k2_funct_2(A_203, B_204)) | ~m1_subset_1(B_204, k1_zfmisc_1(k2_zfmisc_1(A_203, A_203))) | ~v3_funct_2(B_204, A_203, A_203) | ~v1_funct_2(B_204, A_203, A_203) | ~v1_funct_1(B_204))), inference(cnfTransformation, [status(thm)], [f_98])).
% 6.30/2.24  tff(c_2335, plain, (v1_funct_1(k2_funct_2('#skF_2', '#skF_3')) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_56, c_2325])).
% 6.30/2.24  tff(c_2342, plain, (v1_funct_1(k2_funct_2('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_2335])).
% 6.30/2.24  tff(c_2364, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2363, c_2342])).
% 6.30/2.24  tff(c_2389, plain, (![A_215, B_216]: (v3_funct_2(k2_funct_2(A_215, B_216), A_215, A_215) | ~m1_subset_1(B_216, k1_zfmisc_1(k2_zfmisc_1(A_215, A_215))) | ~v3_funct_2(B_216, A_215, A_215) | ~v1_funct_2(B_216, A_215, A_215) | ~v1_funct_1(B_216))), inference(cnfTransformation, [status(thm)], [f_98])).
% 6.30/2.24  tff(c_2396, plain, (v3_funct_2(k2_funct_2('#skF_2', '#skF_3'), '#skF_2', '#skF_2') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_56, c_2389])).
% 6.30/2.24  tff(c_2403, plain, (v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_2363, c_2396])).
% 6.30/2.24  tff(c_20, plain, (![C_18, A_16, B_17]: (v2_funct_1(C_18) | ~v3_funct_2(C_18, A_16, B_17) | ~v1_funct_1(C_18) | ~m1_subset_1(C_18, k1_zfmisc_1(k2_zfmisc_1(A_16, B_17))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 6.30/2.24  tff(c_2471, plain, (v2_funct_1(k2_funct_1('#skF_3')) | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_2450, c_20])).
% 6.30/2.24  tff(c_2499, plain, (v2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2364, c_2403, c_2471])).
% 6.30/2.24  tff(c_2374, plain, (![A_213, B_214]: (v1_funct_2(k2_funct_2(A_213, B_214), A_213, A_213) | ~m1_subset_1(B_214, k1_zfmisc_1(k2_zfmisc_1(A_213, A_213))) | ~v3_funct_2(B_214, A_213, A_213) | ~v1_funct_2(B_214, A_213, A_213) | ~v1_funct_1(B_214))), inference(cnfTransformation, [status(thm)], [f_98])).
% 6.30/2.24  tff(c_2381, plain, (v1_funct_2(k2_funct_2('#skF_2', '#skF_3'), '#skF_2', '#skF_2') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_56, c_2374])).
% 6.30/2.24  tff(c_2388, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_2363, c_2381])).
% 6.30/2.24  tff(c_52, plain, (![A_34, B_35]: (k1_relset_1(A_34, A_34, B_35)=A_34 | ~m1_subset_1(B_35, k1_zfmisc_1(k2_zfmisc_1(A_34, A_34))) | ~v1_funct_2(B_35, A_34, A_34) | ~v1_funct_1(B_35))), inference(cnfTransformation, [status(thm)], [f_143])).
% 6.30/2.24  tff(c_2463, plain, (k1_relset_1('#skF_2', '#skF_2', k2_funct_1('#skF_3'))='#skF_2' | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_2450, c_52])).
% 6.30/2.24  tff(c_2492, plain, (k1_relset_1('#skF_2', '#skF_2', k2_funct_1('#skF_3'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2364, c_2388, c_2463])).
% 6.30/2.24  tff(c_14, plain, (![A_9, B_10, C_11]: (k1_relset_1(A_9, B_10, C_11)=k1_relat_1(C_11) | ~m1_subset_1(C_11, k1_zfmisc_1(k2_zfmisc_1(A_9, B_10))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 6.30/2.24  tff(c_2500, plain, (k1_relset_1('#skF_2', '#skF_2', k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_2450, c_14])).
% 6.30/2.24  tff(c_2584, plain, (k1_relat_1(k2_funct_1('#skF_3'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2492, c_2500])).
% 6.30/2.24  tff(c_48, plain, (![A_31, B_32]: (k2_funct_2(A_31, B_32)=k2_funct_1(B_32) | ~m1_subset_1(B_32, k1_zfmisc_1(k2_zfmisc_1(A_31, A_31))) | ~v3_funct_2(B_32, A_31, A_31) | ~v1_funct_2(B_32, A_31, A_31) | ~v1_funct_1(B_32))), inference(cnfTransformation, [status(thm)], [f_133])).
% 6.30/2.24  tff(c_2457, plain, (k2_funct_2('#skF_2', k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3')) | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_2450, c_48])).
% 6.30/2.24  tff(c_2486, plain, (k2_funct_2('#skF_2', k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2364, c_2388, c_2403, c_2457])).
% 6.30/2.24  tff(c_2433, plain, (![A_219, B_220]: (v1_relat_1(k2_funct_2(A_219, B_220)) | ~v1_relat_1(k2_zfmisc_1(A_219, A_219)) | ~m1_subset_1(B_220, k1_zfmisc_1(k2_zfmisc_1(A_219, A_219))) | ~v3_funct_2(B_220, A_219, A_219) | ~v1_funct_2(B_220, A_219, A_219) | ~v1_funct_1(B_220))), inference(resolution, [status(thm)], [c_2406, c_2])).
% 6.30/2.24  tff(c_2589, plain, (![A_230, B_231]: (v1_relat_1(k2_funct_2(A_230, B_231)) | ~m1_subset_1(B_231, k1_zfmisc_1(k2_zfmisc_1(A_230, A_230))) | ~v3_funct_2(B_231, A_230, A_230) | ~v1_funct_2(B_231, A_230, A_230) | ~v1_funct_1(B_231))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_2433])).
% 6.30/2.24  tff(c_2592, plain, (v1_relat_1(k2_funct_2('#skF_2', k2_funct_1('#skF_3'))) | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_2450, c_2589])).
% 6.30/2.24  tff(c_2608, plain, (v1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_2364, c_2388, c_2403, c_2486, c_2592])).
% 6.30/2.24  tff(c_30, plain, (![A_19, B_20]: (v1_funct_1(k2_funct_2(A_19, B_20)) | ~m1_subset_1(B_20, k1_zfmisc_1(k2_zfmisc_1(A_19, A_19))) | ~v3_funct_2(B_20, A_19, A_19) | ~v1_funct_2(B_20, A_19, A_19) | ~v1_funct_1(B_20))), inference(cnfTransformation, [status(thm)], [f_98])).
% 6.30/2.24  tff(c_2460, plain, (v1_funct_1(k2_funct_2('#skF_2', k2_funct_1('#skF_3'))) | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_2450, c_30])).
% 6.30/2.24  tff(c_2489, plain, (v1_funct_1(k2_funct_2('#skF_2', k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_2364, c_2388, c_2403, c_2460])).
% 6.30/2.24  tff(c_2558, plain, (v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_2486, c_2489])).
% 6.30/2.24  tff(c_26, plain, (![A_19, B_20]: (v3_funct_2(k2_funct_2(A_19, B_20), A_19, A_19) | ~m1_subset_1(B_20, k1_zfmisc_1(k2_zfmisc_1(A_19, A_19))) | ~v3_funct_2(B_20, A_19, A_19) | ~v1_funct_2(B_20, A_19, A_19) | ~v1_funct_1(B_20))), inference(cnfTransformation, [status(thm)], [f_98])).
% 6.30/2.24  tff(c_2452, plain, (v3_funct_2(k2_funct_2('#skF_2', k2_funct_1('#skF_3')), '#skF_2', '#skF_2') | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_2450, c_26])).
% 6.30/2.24  tff(c_2480, plain, (v3_funct_2(k2_funct_2('#skF_2', k2_funct_1('#skF_3')), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2364, c_2388, c_2403, c_2452])).
% 6.30/2.24  tff(c_2557, plain, (v3_funct_2(k2_funct_1(k2_funct_1('#skF_3')), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2486, c_2480])).
% 6.30/2.24  tff(c_24, plain, (![A_19, B_20]: (m1_subset_1(k2_funct_2(A_19, B_20), k1_zfmisc_1(k2_zfmisc_1(A_19, A_19))) | ~m1_subset_1(B_20, k1_zfmisc_1(k2_zfmisc_1(A_19, A_19))) | ~v3_funct_2(B_20, A_19, A_19) | ~v1_funct_2(B_20, A_19, A_19) | ~v1_funct_1(B_20))), inference(cnfTransformation, [status(thm)], [f_98])).
% 6.30/2.24  tff(c_2562, plain, (m1_subset_1(k2_funct_1(k2_funct_1('#skF_3')), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_2486, c_24])).
% 6.30/2.24  tff(c_2566, plain, (m1_subset_1(k2_funct_1(k2_funct_1('#skF_3')), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_2364, c_2388, c_2403, c_2450, c_2562])).
% 6.30/2.24  tff(c_2650, plain, (v2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v3_funct_2(k2_funct_1(k2_funct_1('#skF_3')), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(resolution, [status(thm)], [c_2566, c_20])).
% 6.30/2.24  tff(c_2690, plain, (v2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_2558, c_2557, c_2650])).
% 6.30/2.24  tff(c_28, plain, (![A_19, B_20]: (v1_funct_2(k2_funct_2(A_19, B_20), A_19, A_19) | ~m1_subset_1(B_20, k1_zfmisc_1(k2_zfmisc_1(A_19, A_19))) | ~v3_funct_2(B_20, A_19, A_19) | ~v1_funct_2(B_20, A_19, A_19) | ~v1_funct_1(B_20))), inference(cnfTransformation, [status(thm)], [f_98])).
% 6.30/2.24  tff(c_2454, plain, (v1_funct_2(k2_funct_2('#skF_2', k2_funct_1('#skF_3')), '#skF_2', '#skF_2') | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_2450, c_28])).
% 6.30/2.24  tff(c_2483, plain, (v1_funct_2(k2_funct_2('#skF_2', k2_funct_1('#skF_3')), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2364, c_2388, c_2403, c_2454])).
% 6.30/2.24  tff(c_2578, plain, (v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2486, c_2483])).
% 6.30/2.24  tff(c_2636, plain, (k2_funct_2('#skF_2', k2_funct_1(k2_funct_1('#skF_3')))=k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v3_funct_2(k2_funct_1(k2_funct_1('#skF_3')), '#skF_2', '#skF_2') | ~v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(resolution, [status(thm)], [c_2566, c_48])).
% 6.30/2.24  tff(c_2677, plain, (k2_funct_2('#skF_2', k2_funct_1(k2_funct_1('#skF_3')))=k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_2558, c_2578, c_2557, c_2636])).
% 6.30/2.24  tff(c_2752, plain, (k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))=k2_funct_2('#skF_2', '#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_12, c_2677])).
% 6.30/2.24  tff(c_2758, plain, (k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_93, c_62, c_2253, c_2363, c_2752])).
% 6.30/2.24  tff(c_50, plain, (![A_33]: (k6_relat_1(A_33)=k6_partfun1(A_33))), inference(cnfTransformation, [status(thm)], [f_135])).
% 6.30/2.24  tff(c_6, plain, (![A_6]: (k5_relat_1(k2_funct_1(A_6), A_6)=k6_relat_1(k2_relat_1(A_6)) | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_44])).
% 6.30/2.24  tff(c_64, plain, (![A_6]: (k5_relat_1(k2_funct_1(A_6), A_6)=k6_partfun1(k2_relat_1(A_6)) | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_6])).
% 6.30/2.24  tff(c_2791, plain, (k5_relat_1(k2_funct_1('#skF_3'), k2_funct_1(k2_funct_1('#skF_3')))=k6_partfun1(k2_relat_1(k2_funct_1(k2_funct_1('#skF_3')))) | ~v2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_2758, c_64])).
% 6.30/2.24  tff(c_2812, plain, (k5_relat_1(k2_funct_1('#skF_3'), k2_funct_1(k2_funct_1('#skF_3')))=k6_partfun1(k2_relat_1(k2_funct_1(k2_funct_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_2608, c_2558, c_2690, c_2791])).
% 6.30/2.24  tff(c_8, plain, (![A_6]: (k5_relat_1(A_6, k2_funct_1(A_6))=k6_relat_1(k1_relat_1(A_6)) | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_44])).
% 6.30/2.24  tff(c_63, plain, (![A_6]: (k5_relat_1(A_6, k2_funct_1(A_6))=k6_partfun1(k1_relat_1(A_6)) | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_8])).
% 6.30/2.24  tff(c_2907, plain, (k6_partfun1(k2_relat_1(k2_funct_1(k2_funct_1('#skF_3'))))=k6_partfun1(k1_relat_1(k2_funct_1('#skF_3'))) | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_2812, c_63])).
% 6.30/2.24  tff(c_2917, plain, (k6_partfun1(k2_relat_1(k2_funct_1(k2_funct_1('#skF_3'))))=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2503, c_2364, c_2499, c_2584, c_2907])).
% 6.30/2.24  tff(c_2923, plain, (k5_relat_1(k2_funct_1('#skF_3'), k2_funct_1(k2_funct_1('#skF_3')))=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2917, c_2812])).
% 6.30/2.24  tff(c_3087, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_12, c_2923])).
% 6.30/2.24  tff(c_3095, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_93, c_62, c_2253, c_3087])).
% 6.30/2.24  tff(c_2504, plain, (![D_221, F_224, B_225, C_223, A_222, E_226]: (k1_partfun1(A_222, B_225, C_223, D_221, E_226, F_224)=k5_relat_1(E_226, F_224) | ~m1_subset_1(F_224, k1_zfmisc_1(k2_zfmisc_1(C_223, D_221))) | ~v1_funct_1(F_224) | ~m1_subset_1(E_226, k1_zfmisc_1(k2_zfmisc_1(A_222, B_225))) | ~v1_funct_1(E_226))), inference(cnfTransformation, [status(thm)], [f_123])).
% 6.30/2.24  tff(c_2514, plain, (![A_222, B_225, E_226]: (k1_partfun1(A_222, B_225, '#skF_2', '#skF_2', E_226, '#skF_3')=k5_relat_1(E_226, '#skF_3') | ~v1_funct_1('#skF_3') | ~m1_subset_1(E_226, k1_zfmisc_1(k2_zfmisc_1(A_222, B_225))) | ~v1_funct_1(E_226))), inference(resolution, [status(thm)], [c_56, c_2504])).
% 6.30/2.24  tff(c_2530, plain, (![A_227, B_228, E_229]: (k1_partfun1(A_227, B_228, '#skF_2', '#skF_2', E_229, '#skF_3')=k5_relat_1(E_229, '#skF_3') | ~m1_subset_1(E_229, k1_zfmisc_1(k2_zfmisc_1(A_227, B_228))) | ~v1_funct_1(E_229))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_2514])).
% 6.30/2.24  tff(c_2865, plain, (![A_235, B_236]: (k1_partfun1(A_235, A_235, '#skF_2', '#skF_2', k2_funct_2(A_235, B_236), '#skF_3')=k5_relat_1(k2_funct_2(A_235, B_236), '#skF_3') | ~v1_funct_1(k2_funct_2(A_235, B_236)) | ~m1_subset_1(B_236, k1_zfmisc_1(k2_zfmisc_1(A_235, A_235))) | ~v3_funct_2(B_236, A_235, A_235) | ~v1_funct_2(B_236, A_235, A_235) | ~v1_funct_1(B_236))), inference(resolution, [status(thm)], [c_24, c_2530])).
% 6.30/2.24  tff(c_2878, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_2('#skF_2', '#skF_3'), '#skF_3')=k5_relat_1(k2_funct_2('#skF_2', '#skF_3'), '#skF_3') | ~v1_funct_1(k2_funct_2('#skF_2', '#skF_3')) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_56, c_2865])).
% 6.30/2.24  tff(c_2892, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_1('#skF_3'), '#skF_3')=k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_2364, c_2363, c_2363, c_2363, c_2878])).
% 6.30/2.24  tff(c_240, plain, (![A_78, B_79, C_80, D_81]: (r2_relset_1(A_78, B_79, C_80, C_80) | ~m1_subset_1(D_81, k1_zfmisc_1(k2_zfmisc_1(A_78, B_79))) | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1(A_78, B_79))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.30/2.24  tff(c_271, plain, (![A_83, C_84]: (r2_relset_1(A_83, A_83, C_84, C_84) | ~m1_subset_1(C_84, k1_zfmisc_1(k2_zfmisc_1(A_83, A_83))))), inference(resolution, [status(thm)], [c_34, c_240])).
% 6.30/2.24  tff(c_280, plain, (![A_21]: (r2_relset_1(A_21, A_21, k6_partfun1(A_21), k6_partfun1(A_21)))), inference(resolution, [status(thm)], [c_34, c_271])).
% 6.30/2.24  tff(c_183, plain, (![C_64, A_65, B_66]: (v2_funct_1(C_64) | ~v3_funct_2(C_64, A_65, B_66) | ~v1_funct_1(C_64) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 6.30/2.24  tff(c_192, plain, (v2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_56, c_183])).
% 6.30/2.24  tff(c_199, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_58, c_192])).
% 6.30/2.24  tff(c_319, plain, (![A_94, B_95]: (k2_funct_2(A_94, B_95)=k2_funct_1(B_95) | ~m1_subset_1(B_95, k1_zfmisc_1(k2_zfmisc_1(A_94, A_94))) | ~v3_funct_2(B_95, A_94, A_94) | ~v1_funct_2(B_95, A_94, A_94) | ~v1_funct_1(B_95))), inference(cnfTransformation, [status(thm)], [f_133])).
% 6.30/2.24  tff(c_329, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_56, c_319])).
% 6.30/2.24  tff(c_336, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_329])).
% 6.30/2.24  tff(c_287, plain, (![A_87, B_88]: (v1_funct_1(k2_funct_2(A_87, B_88)) | ~m1_subset_1(B_88, k1_zfmisc_1(k2_zfmisc_1(A_87, A_87))) | ~v3_funct_2(B_88, A_87, A_87) | ~v1_funct_2(B_88, A_87, A_87) | ~v1_funct_1(B_88))), inference(cnfTransformation, [status(thm)], [f_98])).
% 6.30/2.24  tff(c_297, plain, (v1_funct_1(k2_funct_2('#skF_2', '#skF_3')) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_56, c_287])).
% 6.30/2.24  tff(c_304, plain, (v1_funct_1(k2_funct_2('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_297])).
% 6.30/2.24  tff(c_337, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_336, c_304])).
% 6.30/2.24  tff(c_362, plain, (![A_102, B_103]: (v1_funct_2(k2_funct_2(A_102, B_103), A_102, A_102) | ~m1_subset_1(B_103, k1_zfmisc_1(k2_zfmisc_1(A_102, A_102))) | ~v3_funct_2(B_103, A_102, A_102) | ~v1_funct_2(B_103, A_102, A_102) | ~v1_funct_1(B_103))), inference(cnfTransformation, [status(thm)], [f_98])).
% 6.30/2.24  tff(c_369, plain, (v1_funct_2(k2_funct_2('#skF_2', '#skF_3'), '#skF_2', '#skF_2') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_56, c_362])).
% 6.30/2.24  tff(c_376, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_336, c_369])).
% 6.30/2.24  tff(c_345, plain, (![A_98, B_99]: (v3_funct_2(k2_funct_2(A_98, B_99), A_98, A_98) | ~m1_subset_1(B_99, k1_zfmisc_1(k2_zfmisc_1(A_98, A_98))) | ~v3_funct_2(B_99, A_98, A_98) | ~v1_funct_2(B_99, A_98, A_98) | ~v1_funct_1(B_99))), inference(cnfTransformation, [status(thm)], [f_98])).
% 6.30/2.24  tff(c_352, plain, (v3_funct_2(k2_funct_2('#skF_2', '#skF_3'), '#skF_2', '#skF_2') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_56, c_345])).
% 6.30/2.24  tff(c_359, plain, (v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_336, c_352])).
% 6.30/2.24  tff(c_381, plain, (![A_108, B_109]: (m1_subset_1(k2_funct_2(A_108, B_109), k1_zfmisc_1(k2_zfmisc_1(A_108, A_108))) | ~m1_subset_1(B_109, k1_zfmisc_1(k2_zfmisc_1(A_108, A_108))) | ~v3_funct_2(B_109, A_108, A_108) | ~v1_funct_2(B_109, A_108, A_108) | ~v1_funct_1(B_109))), inference(cnfTransformation, [status(thm)], [f_98])).
% 6.30/2.24  tff(c_411, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_336, c_381])).
% 6.30/2.24  tff(c_425, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_56, c_411])).
% 6.30/2.24  tff(c_432, plain, (k2_funct_2('#skF_2', k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3')) | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_425, c_48])).
% 6.30/2.24  tff(c_461, plain, (k2_funct_2('#skF_2', k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_337, c_376, c_359, c_432])).
% 6.30/2.24  tff(c_437, plain, (v1_funct_1(k2_funct_2('#skF_2', k2_funct_1('#skF_3'))) | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_425, c_30])).
% 6.30/2.24  tff(c_465, plain, (v1_funct_1(k2_funct_2('#skF_2', k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_337, c_376, c_359, c_437])).
% 6.30/2.24  tff(c_484, plain, (v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_461, c_465])).
% 6.30/2.24  tff(c_427, plain, (v1_funct_2(k2_funct_2('#skF_2', k2_funct_1('#skF_3')), '#skF_2', '#skF_2') | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_425, c_28])).
% 6.30/2.24  tff(c_455, plain, (v1_funct_2(k2_funct_2('#skF_2', k2_funct_1('#skF_3')), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_337, c_376, c_359, c_427])).
% 6.30/2.24  tff(c_526, plain, (v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_461, c_455])).
% 6.30/2.24  tff(c_488, plain, (m1_subset_1(k2_funct_1(k2_funct_1('#skF_3')), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_461, c_24])).
% 6.30/2.24  tff(c_492, plain, (m1_subset_1(k2_funct_1(k2_funct_1('#skF_3')), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_337, c_376, c_359, c_425, c_488])).
% 6.30/2.24  tff(c_583, plain, (k1_relset_1('#skF_2', '#skF_2', k2_funct_1(k2_funct_1('#skF_3')))='#skF_2' | ~v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(resolution, [status(thm)], [c_492, c_52])).
% 6.30/2.24  tff(c_620, plain, (k1_relset_1('#skF_2', '#skF_2', k2_funct_1(k2_funct_1('#skF_3')))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_484, c_526, c_583])).
% 6.30/2.24  tff(c_627, plain, (k1_relset_1('#skF_2', '#skF_2', k2_funct_1(k2_funct_1('#skF_3')))=k1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(resolution, [status(thm)], [c_492, c_14])).
% 6.30/2.24  tff(c_841, plain, (k1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_620, c_627])).
% 6.30/2.24  tff(c_595, plain, (v1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_2'))), inference(resolution, [status(thm)], [c_492, c_2])).
% 6.30/2.24  tff(c_630, plain, (v1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_595])).
% 6.30/2.24  tff(c_429, plain, (v3_funct_2(k2_funct_2('#skF_2', k2_funct_1('#skF_3')), '#skF_2', '#skF_2') | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_425, c_26])).
% 6.30/2.24  tff(c_458, plain, (v3_funct_2(k2_funct_2('#skF_2', k2_funct_1('#skF_3')), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_337, c_376, c_359, c_429])).
% 6.30/2.24  tff(c_483, plain, (v3_funct_2(k2_funct_1(k2_funct_1('#skF_3')), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_461, c_458])).
% 6.30/2.24  tff(c_589, plain, (v2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v3_funct_2(k2_funct_1(k2_funct_1('#skF_3')), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(resolution, [status(thm)], [c_492, c_20])).
% 6.30/2.24  tff(c_626, plain, (v2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_484, c_483, c_589])).
% 6.30/2.24  tff(c_575, plain, (k2_funct_2('#skF_2', k2_funct_1(k2_funct_1('#skF_3')))=k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v3_funct_2(k2_funct_1(k2_funct_1('#skF_3')), '#skF_2', '#skF_2') | ~v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(resolution, [status(thm)], [c_492, c_48])).
% 6.30/2.24  tff(c_613, plain, (k2_funct_2('#skF_2', k2_funct_1(k2_funct_1('#skF_3')))=k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_484, c_526, c_483, c_575])).
% 6.30/2.24  tff(c_747, plain, (k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))=k2_funct_2('#skF_2', '#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_12, c_613])).
% 6.30/2.24  tff(c_753, plain, (k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_93, c_62, c_199, c_336, c_747])).
% 6.30/2.24  tff(c_783, plain, (k5_relat_1(k2_funct_1(k2_funct_1('#skF_3')), k2_funct_1('#skF_3'))=k6_partfun1(k1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))) | ~v2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_753, c_63])).
% 6.30/2.24  tff(c_805, plain, (k5_relat_1(k2_funct_1(k2_funct_1('#skF_3')), k2_funct_1('#skF_3'))=k6_partfun1(k1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_630, c_484, c_626, c_783])).
% 6.30/2.24  tff(c_851, plain, (k5_relat_1(k2_funct_1(k2_funct_1('#skF_3')), k2_funct_1('#skF_3'))=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_841, c_805])).
% 6.30/2.24  tff(c_862, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_12, c_851])).
% 6.30/2.24  tff(c_870, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_93, c_62, c_199, c_862])).
% 6.30/2.24  tff(c_494, plain, (![E_115, F_113, A_111, B_114, D_110, C_112]: (k1_partfun1(A_111, B_114, C_112, D_110, E_115, F_113)=k5_relat_1(E_115, F_113) | ~m1_subset_1(F_113, k1_zfmisc_1(k2_zfmisc_1(C_112, D_110))) | ~v1_funct_1(F_113) | ~m1_subset_1(E_115, k1_zfmisc_1(k2_zfmisc_1(A_111, B_114))) | ~v1_funct_1(E_115))), inference(cnfTransformation, [status(thm)], [f_123])).
% 6.30/2.24  tff(c_496, plain, (![A_111, B_114, E_115]: (k1_partfun1(A_111, B_114, '#skF_2', '#skF_2', E_115, k2_funct_1('#skF_3'))=k5_relat_1(E_115, k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~m1_subset_1(E_115, k1_zfmisc_1(k2_zfmisc_1(A_111, B_114))) | ~v1_funct_1(E_115))), inference(resolution, [status(thm)], [c_425, c_494])).
% 6.30/2.24  tff(c_2132, plain, (![A_171, B_172, E_173]: (k1_partfun1(A_171, B_172, '#skF_2', '#skF_2', E_173, k2_funct_1('#skF_3'))=k5_relat_1(E_173, k2_funct_1('#skF_3')) | ~m1_subset_1(E_173, k1_zfmisc_1(k2_zfmisc_1(A_171, B_172))) | ~v1_funct_1(E_173))), inference(demodulation, [status(thm), theory('equality')], [c_337, c_496])).
% 6.30/2.24  tff(c_2165, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_1('#skF_3'))=k5_relat_1('#skF_3', k2_funct_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_56, c_2132])).
% 6.30/2.24  tff(c_2184, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_870, c_2165])).
% 6.30/2.24  tff(c_54, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_2('#skF_2', '#skF_3'), '#skF_3'), k6_partfun1('#skF_2')) | ~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_2('#skF_2', '#skF_3')), k6_partfun1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_156])).
% 6.30/2.24  tff(c_136, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_2('#skF_2', '#skF_3')), k6_partfun1('#skF_2'))), inference(splitLeft, [status(thm)], [c_54])).
% 6.30/2.24  tff(c_338, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_1('#skF_3')), k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_336, c_136])).
% 6.30/2.24  tff(c_2185, plain, (~r2_relset_1('#skF_2', '#skF_2', k6_partfun1('#skF_2'), k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2184, c_338])).
% 6.30/2.24  tff(c_2188, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_280, c_2185])).
% 6.30/2.24  tff(c_2189, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_2('#skF_2', '#skF_3'), '#skF_3'), k6_partfun1('#skF_2'))), inference(splitRight, [status(thm)], [c_54])).
% 6.30/2.24  tff(c_2366, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_1('#skF_3'), '#skF_3'), k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2363, c_2189])).
% 6.30/2.24  tff(c_3072, plain, (~r2_relset_1('#skF_2', '#skF_2', k5_relat_1(k2_funct_1('#skF_3'), '#skF_3'), k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2892, c_2366])).
% 6.30/2.24  tff(c_3112, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2292, c_3095, c_3072])).
% 6.30/2.24  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.30/2.24  
% 6.30/2.24  Inference rules
% 6.30/2.24  ----------------------
% 6.30/2.24  #Ref     : 0
% 6.30/2.24  #Sup     : 715
% 6.30/2.24  #Fact    : 0
% 6.30/2.24  #Define  : 0
% 6.30/2.24  #Split   : 2
% 6.30/2.24  #Chain   : 0
% 6.30/2.24  #Close   : 0
% 6.30/2.24  
% 6.30/2.24  Ordering : KBO
% 6.30/2.24  
% 6.30/2.24  Simplification rules
% 6.30/2.24  ----------------------
% 6.30/2.24  #Subsume      : 75
% 6.30/2.24  #Demod        : 1345
% 6.30/2.24  #Tautology    : 308
% 6.30/2.24  #SimpNegUnit  : 0
% 6.30/2.24  #BackRed      : 33
% 6.30/2.24  
% 6.30/2.24  #Partial instantiations: 0
% 6.30/2.24  #Strategies tried      : 1
% 6.30/2.24  
% 6.30/2.24  Timing (in seconds)
% 6.30/2.24  ----------------------
% 6.30/2.24  Preprocessing        : 0.38
% 6.30/2.24  Parsing              : 0.20
% 6.30/2.24  CNF conversion       : 0.03
% 6.30/2.24  Main loop            : 1.03
% 6.30/2.24  Inferencing          : 0.34
% 6.30/2.24  Reduction            : 0.41
% 6.30/2.24  Demodulation         : 0.32
% 6.30/2.24  BG Simplification    : 0.04
% 6.30/2.24  Subsumption          : 0.16
% 6.30/2.24  Abstraction          : 0.05
% 6.30/2.24  MUC search           : 0.00
% 6.30/2.24  Cooper               : 0.00
% 6.30/2.24  Total                : 1.48
% 6.30/2.24  Index Insertion      : 0.00
% 6.30/2.24  Index Deletion       : 0.00
% 6.30/2.24  Index Matching       : 0.00
% 6.30/2.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
