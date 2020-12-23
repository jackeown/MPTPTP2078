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
% DateTime   : Thu Dec  3 10:16:04 EST 2020

% Result     : Theorem 5.63s
% Output     : CNFRefutation 5.63s
% Verified   : 
% Statistics : Number of formulae       :  168 (3485 expanded)
%              Number of leaves         :   39 (1404 expanded)
%              Depth                    :   20
%              Number of atoms          :  407 (12599 expanded)
%              Number of equality atoms :   51 ( 643 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v2_funct_2,type,(
    v2_funct_2: ( $i * $i ) > $o )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_115,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_75,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(f_150,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & v3_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ( r2_relset_1(A,A,k1_partfun1(A,A,A,A,B,k2_funct_2(A,B)),k6_partfun1(A))
          & r2_relset_1(A,A,k1_partfun1(A,A,A,A,k2_funct_2(A,B),B),k6_partfun1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_funct_2)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_59,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(k2_funct_1(A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).

tff(f_135,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k2_funct_2(A,B) = k2_funct_1(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

tff(f_111,axiom,(
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

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_95,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_137,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_43,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_125,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(c_42,plain,(
    ! [A_22] : m1_subset_1(k6_partfun1(A_22),k1_zfmisc_1(k2_zfmisc_1(A_22,A_22))) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_2408,plain,(
    ! [A_187,B_188,C_189,D_190] :
      ( r2_relset_1(A_187,B_188,C_189,C_189)
      | ~ m1_subset_1(D_190,k1_zfmisc_1(k2_zfmisc_1(A_187,B_188)))
      | ~ m1_subset_1(C_189,k1_zfmisc_1(k2_zfmisc_1(A_187,B_188))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_2415,plain,(
    ! [A_191,C_192] :
      ( r2_relset_1(A_191,A_191,C_192,C_192)
      | ~ m1_subset_1(C_192,k1_zfmisc_1(k2_zfmisc_1(A_191,A_191))) ) ),
    inference(resolution,[status(thm)],[c_42,c_2408])).

tff(c_2420,plain,(
    ! [A_22] : r2_relset_1(A_22,A_22,k6_partfun1(A_22),k6_partfun1(A_22)) ),
    inference(resolution,[status(thm)],[c_42,c_2415])).

tff(c_52,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_2238,plain,(
    ! [C_151,A_152,B_153] :
      ( v1_relat_1(C_151)
      | ~ m1_subset_1(C_151,k1_zfmisc_1(k2_zfmisc_1(A_152,B_153))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2246,plain,(
    v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_2238])).

tff(c_58,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_54,plain,(
    v3_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_2385,plain,(
    ! [C_180,A_181,B_182] :
      ( v2_funct_1(C_180)
      | ~ v3_funct_2(C_180,A_181,B_182)
      | ~ v1_funct_1(C_180)
      | ~ m1_subset_1(C_180,k1_zfmisc_1(k2_zfmisc_1(A_181,B_182))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_2391,plain,
    ( v2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_2385])).

tff(c_2395,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_54,c_2391])).

tff(c_12,plain,(
    ! [A_4] :
      ( k2_funct_1(k2_funct_1(A_4)) = A_4
      | ~ v2_funct_1(A_4)
      | ~ v1_funct_1(A_4)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_56,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_2436,plain,(
    ! [A_198,B_199] :
      ( k2_funct_2(A_198,B_199) = k2_funct_1(B_199)
      | ~ m1_subset_1(B_199,k1_zfmisc_1(k2_zfmisc_1(A_198,A_198)))
      | ~ v3_funct_2(B_199,A_198,A_198)
      | ~ v1_funct_2(B_199,A_198,A_198)
      | ~ v1_funct_1(B_199) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_2442,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_2436])).

tff(c_2446,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_2442])).

tff(c_2424,plain,(
    ! [A_195,B_196] :
      ( v1_funct_1(k2_funct_2(A_195,B_196))
      | ~ m1_subset_1(B_196,k1_zfmisc_1(k2_zfmisc_1(A_195,A_195)))
      | ~ v3_funct_2(B_196,A_195,A_195)
      | ~ v1_funct_2(B_196,A_195,A_195)
      | ~ v1_funct_1(B_196) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_2430,plain,
    ( v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_2424])).

tff(c_2434,plain,(
    v1_funct_1(k2_funct_2('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_2430])).

tff(c_2456,plain,(
    v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2446,c_2434])).

tff(c_2466,plain,(
    ! [A_204,B_205] :
      ( v1_funct_2(k2_funct_2(A_204,B_205),A_204,A_204)
      | ~ m1_subset_1(B_205,k1_zfmisc_1(k2_zfmisc_1(A_204,A_204)))
      | ~ v3_funct_2(B_205,A_204,A_204)
      | ~ v1_funct_2(B_205,A_204,A_204)
      | ~ v1_funct_1(B_205) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_2470,plain,
    ( v1_funct_2(k2_funct_2('#skF_1','#skF_2'),'#skF_1','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_2466])).

tff(c_2474,plain,(
    v1_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_2446,c_2470])).

tff(c_2447,plain,(
    ! [A_200,B_201] :
      ( v3_funct_2(k2_funct_2(A_200,B_201),A_200,A_200)
      | ~ m1_subset_1(B_201,k1_zfmisc_1(k2_zfmisc_1(A_200,A_200)))
      | ~ v3_funct_2(B_201,A_200,A_200)
      | ~ v1_funct_2(B_201,A_200,A_200)
      | ~ v1_funct_1(B_201) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_2451,plain,
    ( v3_funct_2(k2_funct_2('#skF_1','#skF_2'),'#skF_1','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_2447])).

tff(c_2455,plain,(
    v3_funct_2(k2_funct_2('#skF_1','#skF_2'),'#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_2451])).

tff(c_2463,plain,(
    v3_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2446,c_2455])).

tff(c_2475,plain,(
    ! [A_206,B_207] :
      ( m1_subset_1(k2_funct_2(A_206,B_207),k1_zfmisc_1(k2_zfmisc_1(A_206,A_206)))
      | ~ m1_subset_1(B_207,k1_zfmisc_1(k2_zfmisc_1(A_206,A_206)))
      | ~ v3_funct_2(B_207,A_206,A_206)
      | ~ v1_funct_2(B_207,A_206,A_206)
      | ~ v1_funct_1(B_207) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_2507,plain,
    ( m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2446,c_2475])).

tff(c_2520,plain,(
    m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_52,c_2507])).

tff(c_46,plain,(
    ! [A_29,B_30] :
      ( k2_funct_2(A_29,B_30) = k2_funct_1(B_30)
      | ~ m1_subset_1(B_30,k1_zfmisc_1(k2_zfmisc_1(A_29,A_29)))
      | ~ v3_funct_2(B_30,A_29,A_29)
      | ~ v1_funct_2(B_30,A_29,A_29)
      | ~ v1_funct_1(B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_2527,plain,
    ( k2_funct_2('#skF_1',k2_funct_1('#skF_2')) = k2_funct_1(k2_funct_1('#skF_2'))
    | ~ v3_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1')
    | ~ v1_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_2520,c_46])).

tff(c_2558,plain,(
    k2_funct_2('#skF_1',k2_funct_1('#skF_2')) = k2_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2456,c_2474,c_2463,c_2527])).

tff(c_32,plain,(
    ! [A_20,B_21] :
      ( m1_subset_1(k2_funct_2(A_20,B_21),k1_zfmisc_1(k2_zfmisc_1(A_20,A_20)))
      | ~ m1_subset_1(B_21,k1_zfmisc_1(k2_zfmisc_1(A_20,A_20)))
      | ~ v3_funct_2(B_21,A_20,A_20)
      | ~ v1_funct_2(B_21,A_20,A_20)
      | ~ v1_funct_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_2583,plain,
    ( m1_subset_1(k2_funct_1(k2_funct_1('#skF_2')),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v3_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1')
    | ~ v1_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2558,c_32])).

tff(c_2587,plain,(
    m1_subset_1(k2_funct_1(k2_funct_1('#skF_2')),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2456,c_2474,c_2463,c_2520,c_2583])).

tff(c_14,plain,(
    ! [C_7,A_5,B_6] :
      ( v1_relat_1(C_7)
      | ~ m1_subset_1(C_7,k1_zfmisc_1(k2_zfmisc_1(A_5,B_6))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2720,plain,(
    v1_relat_1(k2_funct_1(k2_funct_1('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_2587,c_14])).

tff(c_38,plain,(
    ! [A_20,B_21] :
      ( v1_funct_1(k2_funct_2(A_20,B_21))
      | ~ m1_subset_1(B_21,k1_zfmisc_1(k2_zfmisc_1(A_20,A_20)))
      | ~ v3_funct_2(B_21,A_20,A_20)
      | ~ v1_funct_2(B_21,A_20,A_20)
      | ~ v1_funct_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_2530,plain,
    ( v1_funct_1(k2_funct_2('#skF_1',k2_funct_1('#skF_2')))
    | ~ v3_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1')
    | ~ v1_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_2520,c_38])).

tff(c_2561,plain,(
    v1_funct_1(k2_funct_2('#skF_1',k2_funct_1('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2456,c_2474,c_2463,c_2530])).

tff(c_2579,plain,(
    v1_funct_1(k2_funct_1(k2_funct_1('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2558,c_2561])).

tff(c_34,plain,(
    ! [A_20,B_21] :
      ( v3_funct_2(k2_funct_2(A_20,B_21),A_20,A_20)
      | ~ m1_subset_1(B_21,k1_zfmisc_1(k2_zfmisc_1(A_20,A_20)))
      | ~ v3_funct_2(B_21,A_20,A_20)
      | ~ v1_funct_2(B_21,A_20,A_20)
      | ~ v1_funct_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_2524,plain,
    ( v3_funct_2(k2_funct_2('#skF_1',k2_funct_1('#skF_2')),'#skF_1','#skF_1')
    | ~ v3_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1')
    | ~ v1_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_2520,c_34])).

tff(c_2555,plain,(
    v3_funct_2(k2_funct_2('#skF_1',k2_funct_1('#skF_2')),'#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2456,c_2474,c_2463,c_2524])).

tff(c_2617,plain,(
    v3_funct_2(k2_funct_1(k2_funct_1('#skF_2')),'#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2558,c_2555])).

tff(c_24,plain,(
    ! [C_17,A_15,B_16] :
      ( v2_funct_1(C_17)
      | ~ v3_funct_2(C_17,A_15,B_16)
      | ~ v1_funct_1(C_17)
      | ~ m1_subset_1(C_17,k1_zfmisc_1(k2_zfmisc_1(A_15,B_16))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_2679,plain,
    ( v2_funct_1(k2_funct_1(k2_funct_1('#skF_2')))
    | ~ v3_funct_2(k2_funct_1(k2_funct_1('#skF_2')),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_2587,c_24])).

tff(c_2717,plain,(
    v2_funct_1(k2_funct_1(k2_funct_1('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2579,c_2617,c_2679])).

tff(c_22,plain,(
    ! [C_17,B_16,A_15] :
      ( v2_funct_2(C_17,B_16)
      | ~ v3_funct_2(C_17,A_15,B_16)
      | ~ v1_funct_1(C_17)
      | ~ m1_subset_1(C_17,k1_zfmisc_1(k2_zfmisc_1(A_15,B_16))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_2676,plain,
    ( v2_funct_2(k2_funct_1(k2_funct_1('#skF_2')),'#skF_1')
    | ~ v3_funct_2(k2_funct_1(k2_funct_1('#skF_2')),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_2587,c_22])).

tff(c_2714,plain,(
    v2_funct_2(k2_funct_1(k2_funct_1('#skF_2')),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2579,c_2617,c_2676])).

tff(c_16,plain,(
    ! [C_10,B_9,A_8] :
      ( v5_relat_1(C_10,B_9)
      | ~ m1_subset_1(C_10,k1_zfmisc_1(k2_zfmisc_1(A_8,B_9))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_2719,plain,(
    v5_relat_1(k2_funct_1(k2_funct_1('#skF_2')),'#skF_1') ),
    inference(resolution,[status(thm)],[c_2587,c_16])).

tff(c_30,plain,(
    ! [B_19,A_18] :
      ( k2_relat_1(B_19) = A_18
      | ~ v2_funct_2(B_19,A_18)
      | ~ v5_relat_1(B_19,A_18)
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_2746,plain,
    ( k2_relat_1(k2_funct_1(k2_funct_1('#skF_2'))) = '#skF_1'
    | ~ v2_funct_2(k2_funct_1(k2_funct_1('#skF_2')),'#skF_1')
    | ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_2719,c_30])).

tff(c_2752,plain,(
    k2_relat_1(k2_funct_1(k2_funct_1('#skF_2'))) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2720,c_2714,c_2746])).

tff(c_36,plain,(
    ! [A_20,B_21] :
      ( v1_funct_2(k2_funct_2(A_20,B_21),A_20,A_20)
      | ~ m1_subset_1(B_21,k1_zfmisc_1(k2_zfmisc_1(A_20,A_20)))
      | ~ v3_funct_2(B_21,A_20,A_20)
      | ~ v1_funct_2(B_21,A_20,A_20)
      | ~ v1_funct_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_2522,plain,
    ( v1_funct_2(k2_funct_2('#skF_1',k2_funct_1('#skF_2')),'#skF_1','#skF_1')
    | ~ v3_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1')
    | ~ v1_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_2520,c_36])).

tff(c_2552,plain,(
    v1_funct_2(k2_funct_2('#skF_1',k2_funct_1('#skF_2')),'#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2456,c_2474,c_2463,c_2522])).

tff(c_2611,plain,(
    v1_funct_2(k2_funct_1(k2_funct_1('#skF_2')),'#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2558,c_2552])).

tff(c_2666,plain,
    ( k2_funct_2('#skF_1',k2_funct_1(k2_funct_1('#skF_2'))) = k2_funct_1(k2_funct_1(k2_funct_1('#skF_2')))
    | ~ v3_funct_2(k2_funct_1(k2_funct_1('#skF_2')),'#skF_1','#skF_1')
    | ~ v1_funct_2(k2_funct_1(k2_funct_1('#skF_2')),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_2587,c_46])).

tff(c_2706,plain,(
    k2_funct_2('#skF_1',k2_funct_1(k2_funct_1('#skF_2'))) = k2_funct_1(k2_funct_1(k2_funct_1('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2579,c_2611,c_2617,c_2666])).

tff(c_2851,plain,
    ( k2_funct_1(k2_funct_1(k2_funct_1('#skF_2'))) = k2_funct_2('#skF_1','#skF_2')
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_2706])).

tff(c_2857,plain,(
    k2_funct_1(k2_funct_1(k2_funct_1('#skF_2'))) = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2246,c_58,c_2395,c_2446,c_2851])).

tff(c_48,plain,(
    ! [A_31] : k6_relat_1(A_31) = k6_partfun1(A_31) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_6,plain,(
    ! [A_2] :
      ( k5_relat_1(k2_funct_1(A_2),A_2) = k6_relat_1(k2_relat_1(A_2))
      | ~ v2_funct_1(A_2)
      | ~ v1_funct_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_60,plain,(
    ! [A_2] :
      ( k5_relat_1(k2_funct_1(A_2),A_2) = k6_partfun1(k2_relat_1(A_2))
      | ~ v2_funct_1(A_2)
      | ~ v1_funct_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_6])).

tff(c_2890,plain,
    ( k5_relat_1(k2_funct_1('#skF_2'),k2_funct_1(k2_funct_1('#skF_2'))) = k6_partfun1(k2_relat_1(k2_funct_1(k2_funct_1('#skF_2'))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1('#skF_2')))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_2')))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2857,c_60])).

tff(c_2917,plain,(
    k5_relat_1(k2_funct_1('#skF_2'),k2_funct_1(k2_funct_1('#skF_2'))) = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2720,c_2579,c_2717,c_2752,c_2890])).

tff(c_2997,plain,
    ( k5_relat_1(k2_funct_1('#skF_2'),'#skF_2') = k6_partfun1('#skF_1')
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_2917])).

tff(c_3005,plain,(
    k5_relat_1(k2_funct_1('#skF_2'),'#skF_2') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2246,c_58,c_2395,c_2997])).

tff(c_2589,plain,(
    ! [B_211,A_213,D_212,E_210,F_209,C_208] :
      ( k1_partfun1(A_213,B_211,C_208,D_212,E_210,F_209) = k5_relat_1(E_210,F_209)
      | ~ m1_subset_1(F_209,k1_zfmisc_1(k2_zfmisc_1(C_208,D_212)))
      | ~ v1_funct_1(F_209)
      | ~ m1_subset_1(E_210,k1_zfmisc_1(k2_zfmisc_1(A_213,B_211)))
      | ~ v1_funct_1(E_210) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_2597,plain,(
    ! [A_213,B_211,E_210] :
      ( k1_partfun1(A_213,B_211,'#skF_1','#skF_1',E_210,'#skF_2') = k5_relat_1(E_210,'#skF_2')
      | ~ v1_funct_1('#skF_2')
      | ~ m1_subset_1(E_210,k1_zfmisc_1(k2_zfmisc_1(A_213,B_211)))
      | ~ v1_funct_1(E_210) ) ),
    inference(resolution,[status(thm)],[c_52,c_2589])).

tff(c_2623,plain,(
    ! [A_214,B_215,E_216] :
      ( k1_partfun1(A_214,B_215,'#skF_1','#skF_1',E_216,'#skF_2') = k5_relat_1(E_216,'#skF_2')
      | ~ m1_subset_1(E_216,k1_zfmisc_1(k2_zfmisc_1(A_214,B_215)))
      | ~ v1_funct_1(E_216) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_2597])).

tff(c_3006,plain,(
    ! [A_223,B_224] :
      ( k1_partfun1(A_223,A_223,'#skF_1','#skF_1',k2_funct_2(A_223,B_224),'#skF_2') = k5_relat_1(k2_funct_2(A_223,B_224),'#skF_2')
      | ~ v1_funct_1(k2_funct_2(A_223,B_224))
      | ~ m1_subset_1(B_224,k1_zfmisc_1(k2_zfmisc_1(A_223,A_223)))
      | ~ v3_funct_2(B_224,A_223,A_223)
      | ~ v1_funct_2(B_224,A_223,A_223)
      | ~ v1_funct_1(B_224) ) ),
    inference(resolution,[status(thm)],[c_32,c_2623])).

tff(c_3016,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_2'),'#skF_2') = k5_relat_1(k2_funct_2('#skF_1','#skF_2'),'#skF_2')
    | ~ v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_3006])).

tff(c_3027,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_1('#skF_2'),'#skF_2') = k5_relat_1(k2_funct_1('#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_2456,c_2446,c_2446,c_2446,c_3016])).

tff(c_3153,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_1('#skF_2'),'#skF_2') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3005,c_3027])).

tff(c_258,plain,(
    ! [A_75,B_76,C_77,D_78] :
      ( r2_relset_1(A_75,B_76,C_77,C_77)
      | ~ m1_subset_1(D_78,k1_zfmisc_1(k2_zfmisc_1(A_75,B_76)))
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_75,B_76))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_276,plain,(
    ! [A_81,C_82] :
      ( r2_relset_1(A_81,A_81,C_82,C_82)
      | ~ m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1(A_81,A_81))) ) ),
    inference(resolution,[status(thm)],[c_42,c_258])).

tff(c_281,plain,(
    ! [A_22] : r2_relset_1(A_22,A_22,k6_partfun1(A_22),k6_partfun1(A_22)) ),
    inference(resolution,[status(thm)],[c_42,c_276])).

tff(c_285,plain,(
    ! [A_85,B_86] :
      ( k2_funct_2(A_85,B_86) = k2_funct_1(B_86)
      | ~ m1_subset_1(B_86,k1_zfmisc_1(k2_zfmisc_1(A_85,A_85)))
      | ~ v3_funct_2(B_86,A_85,A_85)
      | ~ v1_funct_2(B_86,A_85,A_85)
      | ~ v1_funct_1(B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_291,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_285])).

tff(c_295,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_291])).

tff(c_265,plain,(
    ! [A_79,B_80] :
      ( v1_funct_1(k2_funct_2(A_79,B_80))
      | ~ m1_subset_1(B_80,k1_zfmisc_1(k2_zfmisc_1(A_79,A_79)))
      | ~ v3_funct_2(B_80,A_79,A_79)
      | ~ v1_funct_2(B_80,A_79,A_79)
      | ~ v1_funct_1(B_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_271,plain,
    ( v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_265])).

tff(c_275,plain,(
    v1_funct_1(k2_funct_2('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_271])).

tff(c_296,plain,(
    v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_295,c_275])).

tff(c_75,plain,(
    ! [C_37,A_38,B_39] :
      ( v1_relat_1(C_37)
      | ~ m1_subset_1(C_37,k1_zfmisc_1(k2_zfmisc_1(A_38,B_39))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_83,plain,(
    v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_75])).

tff(c_234,plain,(
    ! [C_67,A_68,B_69] :
      ( v2_funct_1(C_67)
      | ~ v3_funct_2(C_67,A_68,B_69)
      | ~ v1_funct_1(C_67)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_240,plain,
    ( v2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_234])).

tff(c_244,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_54,c_240])).

tff(c_401,plain,(
    ! [A_96,B_97] :
      ( m1_subset_1(k2_funct_2(A_96,B_97),k1_zfmisc_1(k2_zfmisc_1(A_96,A_96)))
      | ~ m1_subset_1(B_97,k1_zfmisc_1(k2_zfmisc_1(A_96,A_96)))
      | ~ v3_funct_2(B_97,A_96,A_96)
      | ~ v1_funct_2(B_97,A_96,A_96)
      | ~ v1_funct_1(B_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_433,plain,
    ( m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_295,c_401])).

tff(c_446,plain,(
    m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_52,c_433])).

tff(c_498,plain,(
    v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_446,c_14])).

tff(c_312,plain,(
    ! [A_90,B_91] :
      ( v3_funct_2(k2_funct_2(A_90,B_91),A_90,A_90)
      | ~ m1_subset_1(B_91,k1_zfmisc_1(k2_zfmisc_1(A_90,A_90)))
      | ~ v3_funct_2(B_91,A_90,A_90)
      | ~ v1_funct_2(B_91,A_90,A_90)
      | ~ v1_funct_1(B_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_316,plain,
    ( v3_funct_2(k2_funct_2('#skF_1','#skF_2'),'#skF_1','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_312])).

tff(c_320,plain,(
    v3_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_295,c_316])).

tff(c_466,plain,
    ( v2_funct_1(k2_funct_1('#skF_2'))
    | ~ v3_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_446,c_24])).

tff(c_495,plain,(
    v2_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_296,c_320,c_466])).

tff(c_463,plain,
    ( v2_funct_2(k2_funct_1('#skF_2'),'#skF_1')
    | ~ v3_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_446,c_22])).

tff(c_492,plain,(
    v2_funct_2(k2_funct_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_296,c_320,c_463])).

tff(c_496,plain,(
    v5_relat_1(k2_funct_1('#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_446,c_16])).

tff(c_501,plain,
    ( k2_relat_1(k2_funct_1('#skF_2')) = '#skF_1'
    | ~ v2_funct_2(k2_funct_1('#skF_2'),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_496,c_30])).

tff(c_504,plain,
    ( k2_relat_1(k2_funct_1('#skF_2')) = '#skF_1'
    | ~ v2_funct_2(k2_funct_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_498,c_501])).

tff(c_571,plain,(
    k2_relat_1(k2_funct_1('#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_492,c_504])).

tff(c_208,plain,(
    ! [A_64] :
      ( k5_relat_1(k2_funct_1(A_64),A_64) = k6_partfun1(k2_relat_1(A_64))
      | ~ v2_funct_1(A_64)
      | ~ v1_funct_1(A_64)
      | ~ v1_relat_1(A_64) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_6])).

tff(c_1160,plain,(
    ! [A_120] :
      ( k6_partfun1(k2_relat_1(k2_funct_1(A_120))) = k5_relat_1(A_120,k2_funct_1(A_120))
      | ~ v2_funct_1(k2_funct_1(A_120))
      | ~ v1_funct_1(k2_funct_1(A_120))
      | ~ v1_relat_1(k2_funct_1(A_120))
      | ~ v2_funct_1(A_120)
      | ~ v1_funct_1(A_120)
      | ~ v1_relat_1(A_120) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_208])).

tff(c_1231,plain,
    ( k5_relat_1('#skF_2',k2_funct_1('#skF_2')) = k6_partfun1('#skF_1')
    | ~ v2_funct_1(k2_funct_1('#skF_2'))
    | ~ v1_funct_1(k2_funct_1('#skF_2'))
    | ~ v1_relat_1(k2_funct_1('#skF_2'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_571,c_1160])).

tff(c_1249,plain,(
    k5_relat_1('#skF_2',k2_funct_1('#skF_2')) = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_58,c_244,c_498,c_296,c_495,c_1231])).

tff(c_515,plain,(
    ! [E_100,B_101,A_103,C_98,F_99,D_102] :
      ( k1_partfun1(A_103,B_101,C_98,D_102,E_100,F_99) = k5_relat_1(E_100,F_99)
      | ~ m1_subset_1(F_99,k1_zfmisc_1(k2_zfmisc_1(C_98,D_102)))
      | ~ v1_funct_1(F_99)
      | ~ m1_subset_1(E_100,k1_zfmisc_1(k2_zfmisc_1(A_103,B_101)))
      | ~ v1_funct_1(E_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_2121,plain,(
    ! [E_143,B_144,A_145,A_142,B_141] :
      ( k1_partfun1(A_142,B_141,A_145,A_145,E_143,k2_funct_2(A_145,B_144)) = k5_relat_1(E_143,k2_funct_2(A_145,B_144))
      | ~ v1_funct_1(k2_funct_2(A_145,B_144))
      | ~ m1_subset_1(E_143,k1_zfmisc_1(k2_zfmisc_1(A_142,B_141)))
      | ~ v1_funct_1(E_143)
      | ~ m1_subset_1(B_144,k1_zfmisc_1(k2_zfmisc_1(A_145,A_145)))
      | ~ v3_funct_2(B_144,A_145,A_145)
      | ~ v1_funct_2(B_144,A_145,A_145)
      | ~ v1_funct_1(B_144) ) ),
    inference(resolution,[status(thm)],[c_32,c_515])).

tff(c_2141,plain,(
    ! [A_145,B_144] :
      ( k1_partfun1('#skF_1','#skF_1',A_145,A_145,'#skF_2',k2_funct_2(A_145,B_144)) = k5_relat_1('#skF_2',k2_funct_2(A_145,B_144))
      | ~ v1_funct_1(k2_funct_2(A_145,B_144))
      | ~ v1_funct_1('#skF_2')
      | ~ m1_subset_1(B_144,k1_zfmisc_1(k2_zfmisc_1(A_145,A_145)))
      | ~ v3_funct_2(B_144,A_145,A_145)
      | ~ v1_funct_2(B_144,A_145,A_145)
      | ~ v1_funct_1(B_144) ) ),
    inference(resolution,[status(thm)],[c_52,c_2121])).

tff(c_2201,plain,(
    ! [A_149,B_150] :
      ( k1_partfun1('#skF_1','#skF_1',A_149,A_149,'#skF_2',k2_funct_2(A_149,B_150)) = k5_relat_1('#skF_2',k2_funct_2(A_149,B_150))
      | ~ v1_funct_1(k2_funct_2(A_149,B_150))
      | ~ m1_subset_1(B_150,k1_zfmisc_1(k2_zfmisc_1(A_149,A_149)))
      | ~ v3_funct_2(B_150,A_149,A_149)
      | ~ v1_funct_2(B_150,A_149,A_149)
      | ~ v1_funct_1(B_150) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_2141])).

tff(c_2217,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_2('#skF_1','#skF_2')) = k5_relat_1('#skF_2',k2_funct_2('#skF_1','#skF_2'))
    | ~ v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_2201])).

tff(c_2231,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_1('#skF_2')) = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_296,c_295,c_1249,c_295,c_295,c_2217])).

tff(c_50,plain,
    ( ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_2'),'#skF_2'),k6_partfun1('#skF_1'))
    | ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_2('#skF_1','#skF_2')),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_74,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_2('#skF_1','#skF_2')),k6_partfun1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_297,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_1('#skF_2')),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_295,c_74])).

tff(c_2232,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2231,c_297])).

tff(c_2235,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_281,c_2232])).

tff(c_2236,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_2'),'#skF_2'),k6_partfun1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_2458,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_1('#skF_2'),'#skF_2'),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2446,c_2236])).

tff(c_3154,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3153,c_2458])).

tff(c_3157,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2420,c_3154])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:21:19 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.63/2.13  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.63/2.14  
% 5.63/2.14  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.63/2.15  %$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1
% 5.63/2.15  
% 5.63/2.15  %Foreground sorts:
% 5.63/2.15  
% 5.63/2.15  
% 5.63/2.15  %Background operators:
% 5.63/2.15  
% 5.63/2.15  
% 5.63/2.15  %Foreground operators:
% 5.63/2.15  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.63/2.15  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 5.63/2.15  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.63/2.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.63/2.15  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 5.63/2.15  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 5.63/2.15  tff(k2_funct_2, type, k2_funct_2: ($i * $i) > $i).
% 5.63/2.15  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.63/2.15  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.63/2.15  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.63/2.15  tff('#skF_2', type, '#skF_2': $i).
% 5.63/2.15  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 5.63/2.15  tff('#skF_1', type, '#skF_1': $i).
% 5.63/2.15  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 5.63/2.15  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.63/2.15  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.63/2.15  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 5.63/2.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.63/2.15  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.63/2.15  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.63/2.15  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 5.63/2.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.63/2.15  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.63/2.15  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 5.63/2.15  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.63/2.15  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.63/2.15  
% 5.63/2.17  tff(f_115, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 5.63/2.17  tff(f_75, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 5.63/2.17  tff(f_150, negated_conjecture, ~(![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, k2_funct_2(A, B)), k6_partfun1(A)) & r2_relset_1(A, A, k1_partfun1(A, A, A, A, k2_funct_2(A, B), B), k6_partfun1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_funct_2)).
% 5.63/2.17  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.63/2.17  tff(f_87, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_funct_2)).
% 5.63/2.17  tff(f_59, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(k2_funct_1(A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_1)).
% 5.63/2.17  tff(f_135, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k2_funct_2(A, B) = k2_funct_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 5.63/2.17  tff(f_111, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (((v1_funct_1(k2_funct_2(A, B)) & v1_funct_2(k2_funct_2(A, B), A, A)) & v3_funct_2(k2_funct_2(A, B), A, A)) & m1_subset_1(k2_funct_2(A, B), k1_zfmisc_1(k2_zfmisc_1(A, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_2)).
% 5.63/2.17  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.63/2.17  tff(f_95, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 5.63/2.17  tff(f_137, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 5.63/2.17  tff(f_43, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 5.63/2.17  tff(f_125, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 5.63/2.17  tff(c_42, plain, (![A_22]: (m1_subset_1(k6_partfun1(A_22), k1_zfmisc_1(k2_zfmisc_1(A_22, A_22))))), inference(cnfTransformation, [status(thm)], [f_115])).
% 5.63/2.17  tff(c_2408, plain, (![A_187, B_188, C_189, D_190]: (r2_relset_1(A_187, B_188, C_189, C_189) | ~m1_subset_1(D_190, k1_zfmisc_1(k2_zfmisc_1(A_187, B_188))) | ~m1_subset_1(C_189, k1_zfmisc_1(k2_zfmisc_1(A_187, B_188))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.63/2.17  tff(c_2415, plain, (![A_191, C_192]: (r2_relset_1(A_191, A_191, C_192, C_192) | ~m1_subset_1(C_192, k1_zfmisc_1(k2_zfmisc_1(A_191, A_191))))), inference(resolution, [status(thm)], [c_42, c_2408])).
% 5.63/2.17  tff(c_2420, plain, (![A_22]: (r2_relset_1(A_22, A_22, k6_partfun1(A_22), k6_partfun1(A_22)))), inference(resolution, [status(thm)], [c_42, c_2415])).
% 5.63/2.17  tff(c_52, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_150])).
% 5.63/2.17  tff(c_2238, plain, (![C_151, A_152, B_153]: (v1_relat_1(C_151) | ~m1_subset_1(C_151, k1_zfmisc_1(k2_zfmisc_1(A_152, B_153))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.63/2.17  tff(c_2246, plain, (v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_52, c_2238])).
% 5.63/2.17  tff(c_58, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_150])).
% 5.63/2.17  tff(c_54, plain, (v3_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_150])).
% 5.63/2.17  tff(c_2385, plain, (![C_180, A_181, B_182]: (v2_funct_1(C_180) | ~v3_funct_2(C_180, A_181, B_182) | ~v1_funct_1(C_180) | ~m1_subset_1(C_180, k1_zfmisc_1(k2_zfmisc_1(A_181, B_182))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.63/2.17  tff(c_2391, plain, (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_52, c_2385])).
% 5.63/2.17  tff(c_2395, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_54, c_2391])).
% 5.63/2.17  tff(c_12, plain, (![A_4]: (k2_funct_1(k2_funct_1(A_4))=A_4 | ~v2_funct_1(A_4) | ~v1_funct_1(A_4) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.63/2.17  tff(c_56, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_150])).
% 5.63/2.17  tff(c_2436, plain, (![A_198, B_199]: (k2_funct_2(A_198, B_199)=k2_funct_1(B_199) | ~m1_subset_1(B_199, k1_zfmisc_1(k2_zfmisc_1(A_198, A_198))) | ~v3_funct_2(B_199, A_198, A_198) | ~v1_funct_2(B_199, A_198, A_198) | ~v1_funct_1(B_199))), inference(cnfTransformation, [status(thm)], [f_135])).
% 5.63/2.17  tff(c_2442, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_52, c_2436])).
% 5.63/2.17  tff(c_2446, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_2442])).
% 5.63/2.17  tff(c_2424, plain, (![A_195, B_196]: (v1_funct_1(k2_funct_2(A_195, B_196)) | ~m1_subset_1(B_196, k1_zfmisc_1(k2_zfmisc_1(A_195, A_195))) | ~v3_funct_2(B_196, A_195, A_195) | ~v1_funct_2(B_196, A_195, A_195) | ~v1_funct_1(B_196))), inference(cnfTransformation, [status(thm)], [f_111])).
% 5.63/2.17  tff(c_2430, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_52, c_2424])).
% 5.63/2.17  tff(c_2434, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_2430])).
% 5.63/2.17  tff(c_2456, plain, (v1_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2446, c_2434])).
% 5.63/2.17  tff(c_2466, plain, (![A_204, B_205]: (v1_funct_2(k2_funct_2(A_204, B_205), A_204, A_204) | ~m1_subset_1(B_205, k1_zfmisc_1(k2_zfmisc_1(A_204, A_204))) | ~v3_funct_2(B_205, A_204, A_204) | ~v1_funct_2(B_205, A_204, A_204) | ~v1_funct_1(B_205))), inference(cnfTransformation, [status(thm)], [f_111])).
% 5.63/2.17  tff(c_2470, plain, (v1_funct_2(k2_funct_2('#skF_1', '#skF_2'), '#skF_1', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_52, c_2466])).
% 5.63/2.17  tff(c_2474, plain, (v1_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_2446, c_2470])).
% 5.63/2.17  tff(c_2447, plain, (![A_200, B_201]: (v3_funct_2(k2_funct_2(A_200, B_201), A_200, A_200) | ~m1_subset_1(B_201, k1_zfmisc_1(k2_zfmisc_1(A_200, A_200))) | ~v3_funct_2(B_201, A_200, A_200) | ~v1_funct_2(B_201, A_200, A_200) | ~v1_funct_1(B_201))), inference(cnfTransformation, [status(thm)], [f_111])).
% 5.63/2.17  tff(c_2451, plain, (v3_funct_2(k2_funct_2('#skF_1', '#skF_2'), '#skF_1', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_52, c_2447])).
% 5.63/2.17  tff(c_2455, plain, (v3_funct_2(k2_funct_2('#skF_1', '#skF_2'), '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_2451])).
% 5.63/2.17  tff(c_2463, plain, (v3_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2446, c_2455])).
% 5.63/2.17  tff(c_2475, plain, (![A_206, B_207]: (m1_subset_1(k2_funct_2(A_206, B_207), k1_zfmisc_1(k2_zfmisc_1(A_206, A_206))) | ~m1_subset_1(B_207, k1_zfmisc_1(k2_zfmisc_1(A_206, A_206))) | ~v3_funct_2(B_207, A_206, A_206) | ~v1_funct_2(B_207, A_206, A_206) | ~v1_funct_1(B_207))), inference(cnfTransformation, [status(thm)], [f_111])).
% 5.63/2.17  tff(c_2507, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2446, c_2475])).
% 5.63/2.17  tff(c_2520, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_52, c_2507])).
% 5.63/2.17  tff(c_46, plain, (![A_29, B_30]: (k2_funct_2(A_29, B_30)=k2_funct_1(B_30) | ~m1_subset_1(B_30, k1_zfmisc_1(k2_zfmisc_1(A_29, A_29))) | ~v3_funct_2(B_30, A_29, A_29) | ~v1_funct_2(B_30, A_29, A_29) | ~v1_funct_1(B_30))), inference(cnfTransformation, [status(thm)], [f_135])).
% 5.63/2.17  tff(c_2527, plain, (k2_funct_2('#skF_1', k2_funct_1('#skF_2'))=k2_funct_1(k2_funct_1('#skF_2')) | ~v3_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1') | ~v1_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_2520, c_46])).
% 5.63/2.17  tff(c_2558, plain, (k2_funct_2('#skF_1', k2_funct_1('#skF_2'))=k2_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2456, c_2474, c_2463, c_2527])).
% 5.63/2.17  tff(c_32, plain, (![A_20, B_21]: (m1_subset_1(k2_funct_2(A_20, B_21), k1_zfmisc_1(k2_zfmisc_1(A_20, A_20))) | ~m1_subset_1(B_21, k1_zfmisc_1(k2_zfmisc_1(A_20, A_20))) | ~v3_funct_2(B_21, A_20, A_20) | ~v1_funct_2(B_21, A_20, A_20) | ~v1_funct_1(B_21))), inference(cnfTransformation, [status(thm)], [f_111])).
% 5.63/2.17  tff(c_2583, plain, (m1_subset_1(k2_funct_1(k2_funct_1('#skF_2')), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v3_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1') | ~v1_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_2558, c_32])).
% 5.63/2.17  tff(c_2587, plain, (m1_subset_1(k2_funct_1(k2_funct_1('#skF_2')), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_2456, c_2474, c_2463, c_2520, c_2583])).
% 5.63/2.17  tff(c_14, plain, (![C_7, A_5, B_6]: (v1_relat_1(C_7) | ~m1_subset_1(C_7, k1_zfmisc_1(k2_zfmisc_1(A_5, B_6))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.63/2.17  tff(c_2720, plain, (v1_relat_1(k2_funct_1(k2_funct_1('#skF_2')))), inference(resolution, [status(thm)], [c_2587, c_14])).
% 5.63/2.17  tff(c_38, plain, (![A_20, B_21]: (v1_funct_1(k2_funct_2(A_20, B_21)) | ~m1_subset_1(B_21, k1_zfmisc_1(k2_zfmisc_1(A_20, A_20))) | ~v3_funct_2(B_21, A_20, A_20) | ~v1_funct_2(B_21, A_20, A_20) | ~v1_funct_1(B_21))), inference(cnfTransformation, [status(thm)], [f_111])).
% 5.63/2.17  tff(c_2530, plain, (v1_funct_1(k2_funct_2('#skF_1', k2_funct_1('#skF_2'))) | ~v3_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1') | ~v1_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_2520, c_38])).
% 5.63/2.17  tff(c_2561, plain, (v1_funct_1(k2_funct_2('#skF_1', k2_funct_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_2456, c_2474, c_2463, c_2530])).
% 5.63/2.17  tff(c_2579, plain, (v1_funct_1(k2_funct_1(k2_funct_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_2558, c_2561])).
% 5.63/2.17  tff(c_34, plain, (![A_20, B_21]: (v3_funct_2(k2_funct_2(A_20, B_21), A_20, A_20) | ~m1_subset_1(B_21, k1_zfmisc_1(k2_zfmisc_1(A_20, A_20))) | ~v3_funct_2(B_21, A_20, A_20) | ~v1_funct_2(B_21, A_20, A_20) | ~v1_funct_1(B_21))), inference(cnfTransformation, [status(thm)], [f_111])).
% 5.63/2.17  tff(c_2524, plain, (v3_funct_2(k2_funct_2('#skF_1', k2_funct_1('#skF_2')), '#skF_1', '#skF_1') | ~v3_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1') | ~v1_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_2520, c_34])).
% 5.63/2.17  tff(c_2555, plain, (v3_funct_2(k2_funct_2('#skF_1', k2_funct_1('#skF_2')), '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2456, c_2474, c_2463, c_2524])).
% 5.63/2.17  tff(c_2617, plain, (v3_funct_2(k2_funct_1(k2_funct_1('#skF_2')), '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2558, c_2555])).
% 5.63/2.17  tff(c_24, plain, (![C_17, A_15, B_16]: (v2_funct_1(C_17) | ~v3_funct_2(C_17, A_15, B_16) | ~v1_funct_1(C_17) | ~m1_subset_1(C_17, k1_zfmisc_1(k2_zfmisc_1(A_15, B_16))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.63/2.17  tff(c_2679, plain, (v2_funct_1(k2_funct_1(k2_funct_1('#skF_2'))) | ~v3_funct_2(k2_funct_1(k2_funct_1('#skF_2')), '#skF_1', '#skF_1') | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_2')))), inference(resolution, [status(thm)], [c_2587, c_24])).
% 5.63/2.17  tff(c_2717, plain, (v2_funct_1(k2_funct_1(k2_funct_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_2579, c_2617, c_2679])).
% 5.63/2.17  tff(c_22, plain, (![C_17, B_16, A_15]: (v2_funct_2(C_17, B_16) | ~v3_funct_2(C_17, A_15, B_16) | ~v1_funct_1(C_17) | ~m1_subset_1(C_17, k1_zfmisc_1(k2_zfmisc_1(A_15, B_16))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.63/2.17  tff(c_2676, plain, (v2_funct_2(k2_funct_1(k2_funct_1('#skF_2')), '#skF_1') | ~v3_funct_2(k2_funct_1(k2_funct_1('#skF_2')), '#skF_1', '#skF_1') | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_2')))), inference(resolution, [status(thm)], [c_2587, c_22])).
% 5.63/2.17  tff(c_2714, plain, (v2_funct_2(k2_funct_1(k2_funct_1('#skF_2')), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2579, c_2617, c_2676])).
% 5.63/2.17  tff(c_16, plain, (![C_10, B_9, A_8]: (v5_relat_1(C_10, B_9) | ~m1_subset_1(C_10, k1_zfmisc_1(k2_zfmisc_1(A_8, B_9))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.63/2.17  tff(c_2719, plain, (v5_relat_1(k2_funct_1(k2_funct_1('#skF_2')), '#skF_1')), inference(resolution, [status(thm)], [c_2587, c_16])).
% 5.63/2.17  tff(c_30, plain, (![B_19, A_18]: (k2_relat_1(B_19)=A_18 | ~v2_funct_2(B_19, A_18) | ~v5_relat_1(B_19, A_18) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_95])).
% 5.63/2.17  tff(c_2746, plain, (k2_relat_1(k2_funct_1(k2_funct_1('#skF_2')))='#skF_1' | ~v2_funct_2(k2_funct_1(k2_funct_1('#skF_2')), '#skF_1') | ~v1_relat_1(k2_funct_1(k2_funct_1('#skF_2')))), inference(resolution, [status(thm)], [c_2719, c_30])).
% 5.63/2.17  tff(c_2752, plain, (k2_relat_1(k2_funct_1(k2_funct_1('#skF_2')))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2720, c_2714, c_2746])).
% 5.63/2.17  tff(c_36, plain, (![A_20, B_21]: (v1_funct_2(k2_funct_2(A_20, B_21), A_20, A_20) | ~m1_subset_1(B_21, k1_zfmisc_1(k2_zfmisc_1(A_20, A_20))) | ~v3_funct_2(B_21, A_20, A_20) | ~v1_funct_2(B_21, A_20, A_20) | ~v1_funct_1(B_21))), inference(cnfTransformation, [status(thm)], [f_111])).
% 5.63/2.17  tff(c_2522, plain, (v1_funct_2(k2_funct_2('#skF_1', k2_funct_1('#skF_2')), '#skF_1', '#skF_1') | ~v3_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1') | ~v1_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_2520, c_36])).
% 5.63/2.17  tff(c_2552, plain, (v1_funct_2(k2_funct_2('#skF_1', k2_funct_1('#skF_2')), '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2456, c_2474, c_2463, c_2522])).
% 5.63/2.17  tff(c_2611, plain, (v1_funct_2(k2_funct_1(k2_funct_1('#skF_2')), '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2558, c_2552])).
% 5.63/2.17  tff(c_2666, plain, (k2_funct_2('#skF_1', k2_funct_1(k2_funct_1('#skF_2')))=k2_funct_1(k2_funct_1(k2_funct_1('#skF_2'))) | ~v3_funct_2(k2_funct_1(k2_funct_1('#skF_2')), '#skF_1', '#skF_1') | ~v1_funct_2(k2_funct_1(k2_funct_1('#skF_2')), '#skF_1', '#skF_1') | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_2')))), inference(resolution, [status(thm)], [c_2587, c_46])).
% 5.63/2.17  tff(c_2706, plain, (k2_funct_2('#skF_1', k2_funct_1(k2_funct_1('#skF_2')))=k2_funct_1(k2_funct_1(k2_funct_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_2579, c_2611, c_2617, c_2666])).
% 5.63/2.17  tff(c_2851, plain, (k2_funct_1(k2_funct_1(k2_funct_1('#skF_2')))=k2_funct_2('#skF_1', '#skF_2') | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_12, c_2706])).
% 5.63/2.17  tff(c_2857, plain, (k2_funct_1(k2_funct_1(k2_funct_1('#skF_2')))=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2246, c_58, c_2395, c_2446, c_2851])).
% 5.63/2.17  tff(c_48, plain, (![A_31]: (k6_relat_1(A_31)=k6_partfun1(A_31))), inference(cnfTransformation, [status(thm)], [f_137])).
% 5.63/2.17  tff(c_6, plain, (![A_2]: (k5_relat_1(k2_funct_1(A_2), A_2)=k6_relat_1(k2_relat_1(A_2)) | ~v2_funct_1(A_2) | ~v1_funct_1(A_2) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.63/2.17  tff(c_60, plain, (![A_2]: (k5_relat_1(k2_funct_1(A_2), A_2)=k6_partfun1(k2_relat_1(A_2)) | ~v2_funct_1(A_2) | ~v1_funct_1(A_2) | ~v1_relat_1(A_2))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_6])).
% 5.63/2.17  tff(c_2890, plain, (k5_relat_1(k2_funct_1('#skF_2'), k2_funct_1(k2_funct_1('#skF_2')))=k6_partfun1(k2_relat_1(k2_funct_1(k2_funct_1('#skF_2')))) | ~v2_funct_1(k2_funct_1(k2_funct_1('#skF_2'))) | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_2'))) | ~v1_relat_1(k2_funct_1(k2_funct_1('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_2857, c_60])).
% 5.63/2.17  tff(c_2917, plain, (k5_relat_1(k2_funct_1('#skF_2'), k2_funct_1(k2_funct_1('#skF_2')))=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2720, c_2579, c_2717, c_2752, c_2890])).
% 5.63/2.17  tff(c_2997, plain, (k5_relat_1(k2_funct_1('#skF_2'), '#skF_2')=k6_partfun1('#skF_1') | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_12, c_2917])).
% 5.63/2.17  tff(c_3005, plain, (k5_relat_1(k2_funct_1('#skF_2'), '#skF_2')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2246, c_58, c_2395, c_2997])).
% 5.63/2.17  tff(c_2589, plain, (![B_211, A_213, D_212, E_210, F_209, C_208]: (k1_partfun1(A_213, B_211, C_208, D_212, E_210, F_209)=k5_relat_1(E_210, F_209) | ~m1_subset_1(F_209, k1_zfmisc_1(k2_zfmisc_1(C_208, D_212))) | ~v1_funct_1(F_209) | ~m1_subset_1(E_210, k1_zfmisc_1(k2_zfmisc_1(A_213, B_211))) | ~v1_funct_1(E_210))), inference(cnfTransformation, [status(thm)], [f_125])).
% 5.63/2.17  tff(c_2597, plain, (![A_213, B_211, E_210]: (k1_partfun1(A_213, B_211, '#skF_1', '#skF_1', E_210, '#skF_2')=k5_relat_1(E_210, '#skF_2') | ~v1_funct_1('#skF_2') | ~m1_subset_1(E_210, k1_zfmisc_1(k2_zfmisc_1(A_213, B_211))) | ~v1_funct_1(E_210))), inference(resolution, [status(thm)], [c_52, c_2589])).
% 5.63/2.17  tff(c_2623, plain, (![A_214, B_215, E_216]: (k1_partfun1(A_214, B_215, '#skF_1', '#skF_1', E_216, '#skF_2')=k5_relat_1(E_216, '#skF_2') | ~m1_subset_1(E_216, k1_zfmisc_1(k2_zfmisc_1(A_214, B_215))) | ~v1_funct_1(E_216))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_2597])).
% 5.63/2.17  tff(c_3006, plain, (![A_223, B_224]: (k1_partfun1(A_223, A_223, '#skF_1', '#skF_1', k2_funct_2(A_223, B_224), '#skF_2')=k5_relat_1(k2_funct_2(A_223, B_224), '#skF_2') | ~v1_funct_1(k2_funct_2(A_223, B_224)) | ~m1_subset_1(B_224, k1_zfmisc_1(k2_zfmisc_1(A_223, A_223))) | ~v3_funct_2(B_224, A_223, A_223) | ~v1_funct_2(B_224, A_223, A_223) | ~v1_funct_1(B_224))), inference(resolution, [status(thm)], [c_32, c_2623])).
% 5.63/2.17  tff(c_3016, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_2'), '#skF_2')=k5_relat_1(k2_funct_2('#skF_1', '#skF_2'), '#skF_2') | ~v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_52, c_3006])).
% 5.63/2.17  tff(c_3027, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_1('#skF_2'), '#skF_2')=k5_relat_1(k2_funct_1('#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_2456, c_2446, c_2446, c_2446, c_3016])).
% 5.63/2.17  tff(c_3153, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_1('#skF_2'), '#skF_2')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3005, c_3027])).
% 5.63/2.17  tff(c_258, plain, (![A_75, B_76, C_77, D_78]: (r2_relset_1(A_75, B_76, C_77, C_77) | ~m1_subset_1(D_78, k1_zfmisc_1(k2_zfmisc_1(A_75, B_76))) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_75, B_76))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.63/2.17  tff(c_276, plain, (![A_81, C_82]: (r2_relset_1(A_81, A_81, C_82, C_82) | ~m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1(A_81, A_81))))), inference(resolution, [status(thm)], [c_42, c_258])).
% 5.63/2.17  tff(c_281, plain, (![A_22]: (r2_relset_1(A_22, A_22, k6_partfun1(A_22), k6_partfun1(A_22)))), inference(resolution, [status(thm)], [c_42, c_276])).
% 5.63/2.17  tff(c_285, plain, (![A_85, B_86]: (k2_funct_2(A_85, B_86)=k2_funct_1(B_86) | ~m1_subset_1(B_86, k1_zfmisc_1(k2_zfmisc_1(A_85, A_85))) | ~v3_funct_2(B_86, A_85, A_85) | ~v1_funct_2(B_86, A_85, A_85) | ~v1_funct_1(B_86))), inference(cnfTransformation, [status(thm)], [f_135])).
% 5.63/2.17  tff(c_291, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_52, c_285])).
% 5.63/2.17  tff(c_295, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_291])).
% 5.63/2.17  tff(c_265, plain, (![A_79, B_80]: (v1_funct_1(k2_funct_2(A_79, B_80)) | ~m1_subset_1(B_80, k1_zfmisc_1(k2_zfmisc_1(A_79, A_79))) | ~v3_funct_2(B_80, A_79, A_79) | ~v1_funct_2(B_80, A_79, A_79) | ~v1_funct_1(B_80))), inference(cnfTransformation, [status(thm)], [f_111])).
% 5.63/2.17  tff(c_271, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_52, c_265])).
% 5.63/2.17  tff(c_275, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_271])).
% 5.63/2.17  tff(c_296, plain, (v1_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_295, c_275])).
% 5.63/2.17  tff(c_75, plain, (![C_37, A_38, B_39]: (v1_relat_1(C_37) | ~m1_subset_1(C_37, k1_zfmisc_1(k2_zfmisc_1(A_38, B_39))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.63/2.17  tff(c_83, plain, (v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_52, c_75])).
% 5.63/2.17  tff(c_234, plain, (![C_67, A_68, B_69]: (v2_funct_1(C_67) | ~v3_funct_2(C_67, A_68, B_69) | ~v1_funct_1(C_67) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.63/2.17  tff(c_240, plain, (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_52, c_234])).
% 5.63/2.17  tff(c_244, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_54, c_240])).
% 5.63/2.17  tff(c_401, plain, (![A_96, B_97]: (m1_subset_1(k2_funct_2(A_96, B_97), k1_zfmisc_1(k2_zfmisc_1(A_96, A_96))) | ~m1_subset_1(B_97, k1_zfmisc_1(k2_zfmisc_1(A_96, A_96))) | ~v3_funct_2(B_97, A_96, A_96) | ~v1_funct_2(B_97, A_96, A_96) | ~v1_funct_1(B_97))), inference(cnfTransformation, [status(thm)], [f_111])).
% 5.63/2.17  tff(c_433, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_295, c_401])).
% 5.63/2.17  tff(c_446, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_52, c_433])).
% 5.63/2.17  tff(c_498, plain, (v1_relat_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_446, c_14])).
% 5.63/2.17  tff(c_312, plain, (![A_90, B_91]: (v3_funct_2(k2_funct_2(A_90, B_91), A_90, A_90) | ~m1_subset_1(B_91, k1_zfmisc_1(k2_zfmisc_1(A_90, A_90))) | ~v3_funct_2(B_91, A_90, A_90) | ~v1_funct_2(B_91, A_90, A_90) | ~v1_funct_1(B_91))), inference(cnfTransformation, [status(thm)], [f_111])).
% 5.63/2.17  tff(c_316, plain, (v3_funct_2(k2_funct_2('#skF_1', '#skF_2'), '#skF_1', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_52, c_312])).
% 5.63/2.17  tff(c_320, plain, (v3_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_295, c_316])).
% 5.63/2.17  tff(c_466, plain, (v2_funct_1(k2_funct_1('#skF_2')) | ~v3_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_446, c_24])).
% 5.63/2.17  tff(c_495, plain, (v2_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_296, c_320, c_466])).
% 5.63/2.17  tff(c_463, plain, (v2_funct_2(k2_funct_1('#skF_2'), '#skF_1') | ~v3_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_446, c_22])).
% 5.63/2.17  tff(c_492, plain, (v2_funct_2(k2_funct_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_296, c_320, c_463])).
% 5.63/2.17  tff(c_496, plain, (v5_relat_1(k2_funct_1('#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_446, c_16])).
% 5.63/2.17  tff(c_501, plain, (k2_relat_1(k2_funct_1('#skF_2'))='#skF_1' | ~v2_funct_2(k2_funct_1('#skF_2'), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_496, c_30])).
% 5.63/2.17  tff(c_504, plain, (k2_relat_1(k2_funct_1('#skF_2'))='#skF_1' | ~v2_funct_2(k2_funct_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_498, c_501])).
% 5.63/2.17  tff(c_571, plain, (k2_relat_1(k2_funct_1('#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_492, c_504])).
% 5.63/2.17  tff(c_208, plain, (![A_64]: (k5_relat_1(k2_funct_1(A_64), A_64)=k6_partfun1(k2_relat_1(A_64)) | ~v2_funct_1(A_64) | ~v1_funct_1(A_64) | ~v1_relat_1(A_64))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_6])).
% 5.63/2.17  tff(c_1160, plain, (![A_120]: (k6_partfun1(k2_relat_1(k2_funct_1(A_120)))=k5_relat_1(A_120, k2_funct_1(A_120)) | ~v2_funct_1(k2_funct_1(A_120)) | ~v1_funct_1(k2_funct_1(A_120)) | ~v1_relat_1(k2_funct_1(A_120)) | ~v2_funct_1(A_120) | ~v1_funct_1(A_120) | ~v1_relat_1(A_120))), inference(superposition, [status(thm), theory('equality')], [c_12, c_208])).
% 5.63/2.17  tff(c_1231, plain, (k5_relat_1('#skF_2', k2_funct_1('#skF_2'))=k6_partfun1('#skF_1') | ~v2_funct_1(k2_funct_1('#skF_2')) | ~v1_funct_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_funct_1('#skF_2')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_571, c_1160])).
% 5.63/2.18  tff(c_1249, plain, (k5_relat_1('#skF_2', k2_funct_1('#skF_2'))=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_83, c_58, c_244, c_498, c_296, c_495, c_1231])).
% 5.63/2.18  tff(c_515, plain, (![E_100, B_101, A_103, C_98, F_99, D_102]: (k1_partfun1(A_103, B_101, C_98, D_102, E_100, F_99)=k5_relat_1(E_100, F_99) | ~m1_subset_1(F_99, k1_zfmisc_1(k2_zfmisc_1(C_98, D_102))) | ~v1_funct_1(F_99) | ~m1_subset_1(E_100, k1_zfmisc_1(k2_zfmisc_1(A_103, B_101))) | ~v1_funct_1(E_100))), inference(cnfTransformation, [status(thm)], [f_125])).
% 5.63/2.18  tff(c_2121, plain, (![E_143, B_144, A_145, A_142, B_141]: (k1_partfun1(A_142, B_141, A_145, A_145, E_143, k2_funct_2(A_145, B_144))=k5_relat_1(E_143, k2_funct_2(A_145, B_144)) | ~v1_funct_1(k2_funct_2(A_145, B_144)) | ~m1_subset_1(E_143, k1_zfmisc_1(k2_zfmisc_1(A_142, B_141))) | ~v1_funct_1(E_143) | ~m1_subset_1(B_144, k1_zfmisc_1(k2_zfmisc_1(A_145, A_145))) | ~v3_funct_2(B_144, A_145, A_145) | ~v1_funct_2(B_144, A_145, A_145) | ~v1_funct_1(B_144))), inference(resolution, [status(thm)], [c_32, c_515])).
% 5.63/2.18  tff(c_2141, plain, (![A_145, B_144]: (k1_partfun1('#skF_1', '#skF_1', A_145, A_145, '#skF_2', k2_funct_2(A_145, B_144))=k5_relat_1('#skF_2', k2_funct_2(A_145, B_144)) | ~v1_funct_1(k2_funct_2(A_145, B_144)) | ~v1_funct_1('#skF_2') | ~m1_subset_1(B_144, k1_zfmisc_1(k2_zfmisc_1(A_145, A_145))) | ~v3_funct_2(B_144, A_145, A_145) | ~v1_funct_2(B_144, A_145, A_145) | ~v1_funct_1(B_144))), inference(resolution, [status(thm)], [c_52, c_2121])).
% 5.63/2.18  tff(c_2201, plain, (![A_149, B_150]: (k1_partfun1('#skF_1', '#skF_1', A_149, A_149, '#skF_2', k2_funct_2(A_149, B_150))=k5_relat_1('#skF_2', k2_funct_2(A_149, B_150)) | ~v1_funct_1(k2_funct_2(A_149, B_150)) | ~m1_subset_1(B_150, k1_zfmisc_1(k2_zfmisc_1(A_149, A_149))) | ~v3_funct_2(B_150, A_149, A_149) | ~v1_funct_2(B_150, A_149, A_149) | ~v1_funct_1(B_150))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_2141])).
% 5.63/2.18  tff(c_2217, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_2('#skF_1', '#skF_2'))=k5_relat_1('#skF_2', k2_funct_2('#skF_1', '#skF_2')) | ~v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_52, c_2201])).
% 5.63/2.18  tff(c_2231, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_1('#skF_2'))=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_296, c_295, c_1249, c_295, c_295, c_2217])).
% 5.63/2.18  tff(c_50, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_2'), '#skF_2'), k6_partfun1('#skF_1')) | ~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_2('#skF_1', '#skF_2')), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_150])).
% 5.63/2.18  tff(c_74, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_2('#skF_1', '#skF_2')), k6_partfun1('#skF_1'))), inference(splitLeft, [status(thm)], [c_50])).
% 5.63/2.18  tff(c_297, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_1('#skF_2')), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_295, c_74])).
% 5.63/2.18  tff(c_2232, plain, (~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2231, c_297])).
% 5.63/2.18  tff(c_2235, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_281, c_2232])).
% 5.63/2.18  tff(c_2236, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_2'), '#skF_2'), k6_partfun1('#skF_1'))), inference(splitRight, [status(thm)], [c_50])).
% 5.63/2.18  tff(c_2458, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_1('#skF_2'), '#skF_2'), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2446, c_2236])).
% 5.63/2.18  tff(c_3154, plain, (~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_3153, c_2458])).
% 5.63/2.18  tff(c_3157, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2420, c_3154])).
% 5.63/2.18  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.63/2.18  
% 5.63/2.18  Inference rules
% 5.63/2.18  ----------------------
% 5.63/2.18  #Ref     : 0
% 5.63/2.18  #Sup     : 715
% 5.63/2.18  #Fact    : 0
% 5.63/2.18  #Define  : 0
% 5.63/2.18  #Split   : 7
% 5.63/2.18  #Chain   : 0
% 5.63/2.18  #Close   : 0
% 5.63/2.18  
% 5.63/2.18  Ordering : KBO
% 5.63/2.18  
% 5.63/2.18  Simplification rules
% 5.63/2.18  ----------------------
% 5.63/2.18  #Subsume      : 94
% 5.63/2.18  #Demod        : 1528
% 5.63/2.18  #Tautology    : 300
% 5.63/2.18  #SimpNegUnit  : 6
% 5.63/2.18  #BackRed      : 29
% 5.63/2.18  
% 5.63/2.18  #Partial instantiations: 0
% 5.63/2.18  #Strategies tried      : 1
% 5.63/2.18  
% 5.63/2.18  Timing (in seconds)
% 5.63/2.18  ----------------------
% 5.63/2.18  Preprocessing        : 0.35
% 5.63/2.18  Parsing              : 0.19
% 5.63/2.18  CNF conversion       : 0.02
% 5.63/2.18  Main loop            : 0.98
% 5.63/2.18  Inferencing          : 0.33
% 5.63/2.18  Reduction            : 0.38
% 5.63/2.18  Demodulation         : 0.29
% 5.63/2.18  BG Simplification    : 0.03
% 5.63/2.18  Subsumption          : 0.16
% 5.63/2.18  Abstraction          : 0.04
% 5.63/2.18  MUC search           : 0.00
% 5.63/2.18  Cooper               : 0.00
% 5.63/2.18  Total                : 1.38
% 5.63/2.18  Index Insertion      : 0.00
% 5.63/2.18  Index Deletion       : 0.00
% 5.63/2.18  Index Matching       : 0.00
% 5.63/2.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
