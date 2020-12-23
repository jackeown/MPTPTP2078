%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:06 EST 2020

% Result     : Theorem 6.13s
% Output     : CNFRefutation 6.51s
% Verified   : 
% Statistics : Number of formulae       :  134 ( 413 expanded)
%              Number of leaves         :   46 ( 177 expanded)
%              Depth                    :   10
%              Number of atoms          :  290 (1262 expanded)
%              Number of equality atoms :   55 ( 108 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v2_funct_2 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k3_relset_1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > k11_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k2_funct_2,type,(
    k2_funct_2: ( $i * $i ) > $i )).

tff(k3_relset_1,type,(
    k3_relset_1: ( $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v2_funct_2,type,(
    v2_funct_2: ( $i * $i ) > $o )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff(v3_funct_2,type,(
    v3_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_150,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & v3_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ( r2_relset_1(A,A,k1_partfun1(A,A,A,A,B,k2_funct_2(A,B)),k6_partfun1(A))
          & r2_relset_1(A,A,k1_partfun1(A,A,A,A,k2_funct_2(A,B),B),k6_partfun1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_funct_2)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_129,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_67,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A)))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,A)))
         => ( ! [D] :
                ( r2_hidden(D,A)
               => k11_relat_1(B,D) = k11_relat_1(C,D) )
           => r2_relset_1(A,A,B,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_relset_1)).

tff(f_127,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k2_funct_2(A,B) = k2_funct_1(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

tff(f_107,axiom,(
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

tff(f_33,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(A) = k4_relat_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k3_relset_1(A,B,C) = k4_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_relset_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k1_relset_1(B,A,k3_relset_1(A,B,C)) = k2_relset_1(A,B,C)
        & k2_relset_1(B,A,k3_relset_1(A,B,C)) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_relset_1)).

tff(f_137,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k1_relset_1(A,A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_2)).

tff(f_43,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_117,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(c_50,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_70,plain,(
    ! [C_44,A_45,B_46] :
      ( v1_relat_1(C_44)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(A_45,B_46))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_78,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_70])).

tff(c_56,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_52,plain,(
    v3_funct_2('#skF_3','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_2391,plain,(
    ! [C_178,A_179,B_180] :
      ( v2_funct_1(C_178)
      | ~ v3_funct_2(C_178,A_179,B_180)
      | ~ v1_funct_1(C_178)
      | ~ m1_subset_1(C_178,k1_zfmisc_1(k2_zfmisc_1(A_179,B_180))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_2397,plain,
    ( v2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_2391])).

tff(c_2401,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_2397])).

tff(c_44,plain,(
    ! [A_39] : k6_relat_1(A_39) = k6_partfun1(A_39) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_20,plain,(
    ! [A_18] : m1_subset_1(k6_relat_1(A_18),k1_zfmisc_1(k2_zfmisc_1(A_18,A_18))) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_57,plain,(
    ! [A_18] : m1_subset_1(k6_partfun1(A_18),k1_zfmisc_1(k2_zfmisc_1(A_18,A_18))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_20])).

tff(c_22,plain,(
    ! [C_24,A_19,B_20] :
      ( k11_relat_1(C_24,'#skF_1'(A_19,B_20,C_24)) != k11_relat_1(B_20,'#skF_1'(A_19,B_20,C_24))
      | r2_relset_1(A_19,A_19,B_20,C_24)
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1(A_19,A_19)))
      | ~ m1_subset_1(B_20,k1_zfmisc_1(k2_zfmisc_1(A_19,A_19))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_2862,plain,(
    ! [A_223,B_224] :
      ( r2_relset_1(A_223,A_223,B_224,B_224)
      | ~ m1_subset_1(B_224,k1_zfmisc_1(k2_zfmisc_1(A_223,A_223)))
      | ~ m1_subset_1(B_224,k1_zfmisc_1(k2_zfmisc_1(A_223,A_223))) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_22])).

tff(c_2870,plain,(
    ! [A_18] :
      ( r2_relset_1(A_18,A_18,k6_partfun1(A_18),k6_partfun1(A_18))
      | ~ m1_subset_1(k6_partfun1(A_18),k1_zfmisc_1(k2_zfmisc_1(A_18,A_18))) ) ),
    inference(resolution,[status(thm)],[c_57,c_2862])).

tff(c_2882,plain,(
    ! [A_18] : r2_relset_1(A_18,A_18,k6_partfun1(A_18),k6_partfun1(A_18)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_2870])).

tff(c_54,plain,(
    v1_funct_2('#skF_3','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_2513,plain,(
    ! [A_200,B_201] :
      ( k2_funct_2(A_200,B_201) = k2_funct_1(B_201)
      | ~ m1_subset_1(B_201,k1_zfmisc_1(k2_zfmisc_1(A_200,A_200)))
      | ~ v3_funct_2(B_201,A_200,A_200)
      | ~ v1_funct_2(B_201,A_200,A_200)
      | ~ v1_funct_1(B_201) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_2519,plain,
    ( k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_2513])).

tff(c_2523,plain,(
    k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_2519])).

tff(c_2501,plain,(
    ! [A_197,B_198] :
      ( v1_funct_1(k2_funct_2(A_197,B_198))
      | ~ m1_subset_1(B_198,k1_zfmisc_1(k2_zfmisc_1(A_197,A_197)))
      | ~ v3_funct_2(B_198,A_197,A_197)
      | ~ v1_funct_2(B_198,A_197,A_197)
      | ~ v1_funct_1(B_198) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_2507,plain,
    ( v1_funct_1(k2_funct_2('#skF_2','#skF_3'))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_2501])).

tff(c_2511,plain,(
    v1_funct_1(k2_funct_2('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_2507])).

tff(c_2524,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2523,c_2511])).

tff(c_2541,plain,(
    ! [A_205,B_206] :
      ( v1_funct_2(k2_funct_2(A_205,B_206),A_205,A_205)
      | ~ m1_subset_1(B_206,k1_zfmisc_1(k2_zfmisc_1(A_205,A_205)))
      | ~ v3_funct_2(B_206,A_205,A_205)
      | ~ v1_funct_2(B_206,A_205,A_205)
      | ~ v1_funct_1(B_206) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_2545,plain,
    ( v1_funct_2(k2_funct_2('#skF_2','#skF_3'),'#skF_2','#skF_2')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_2541])).

tff(c_2549,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_2523,c_2545])).

tff(c_2,plain,(
    ! [A_1] :
      ( k4_relat_1(A_1) = k2_funct_1(A_1)
      | ~ v2_funct_1(A_1)
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2404,plain,
    ( k4_relat_1('#skF_3') = k2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2401,c_2])).

tff(c_2407,plain,(
    k4_relat_1('#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_56,c_2404])).

tff(c_2320,plain,(
    ! [A_167,B_168,C_169] :
      ( k3_relset_1(A_167,B_168,C_169) = k4_relat_1(C_169)
      | ~ m1_subset_1(C_169,k1_zfmisc_1(k2_zfmisc_1(A_167,B_168))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_2328,plain,(
    k3_relset_1('#skF_2','#skF_2','#skF_3') = k4_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_2320])).

tff(c_2408,plain,(
    k3_relset_1('#skF_2','#skF_2','#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2407,c_2328])).

tff(c_2351,plain,(
    ! [A_172,B_173,C_174] :
      ( k2_relset_1(A_172,B_173,C_174) = k2_relat_1(C_174)
      | ~ m1_subset_1(C_174,k1_zfmisc_1(k2_zfmisc_1(A_172,B_173))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2359,plain,(
    k2_relset_1('#skF_2','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_2351])).

tff(c_2430,plain,(
    ! [B_186,A_187,C_188] :
      ( k1_relset_1(B_186,A_187,k3_relset_1(A_187,B_186,C_188)) = k2_relset_1(A_187,B_186,C_188)
      | ~ m1_subset_1(C_188,k1_zfmisc_1(k2_zfmisc_1(A_187,B_186))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_2434,plain,(
    k1_relset_1('#skF_2','#skF_2',k3_relset_1('#skF_2','#skF_2','#skF_3')) = k2_relset_1('#skF_2','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_2430])).

tff(c_2438,plain,(
    k1_relset_1('#skF_2','#skF_2',k2_funct_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2408,c_2359,c_2434])).

tff(c_2570,plain,(
    ! [A_212,B_213] :
      ( m1_subset_1(k2_funct_2(A_212,B_213),k1_zfmisc_1(k2_zfmisc_1(A_212,A_212)))
      | ~ m1_subset_1(B_213,k1_zfmisc_1(k2_zfmisc_1(A_212,A_212)))
      | ~ v3_funct_2(B_213,A_212,A_212)
      | ~ v1_funct_2(B_213,A_212,A_212)
      | ~ v1_funct_1(B_213) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_2614,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2523,c_2570])).

tff(c_2631,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_2614])).

tff(c_46,plain,(
    ! [A_40,B_41] :
      ( k1_relset_1(A_40,A_40,B_41) = A_40
      | ~ m1_subset_1(B_41,k1_zfmisc_1(k2_zfmisc_1(A_40,A_40)))
      | ~ v1_funct_2(B_41,A_40,A_40)
      | ~ v1_funct_1(B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_2649,plain,
    ( k1_relset_1('#skF_2','#skF_2',k2_funct_1('#skF_3')) = '#skF_2'
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2631,c_46])).

tff(c_2688,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2524,c_2549,c_2438,c_2649])).

tff(c_4,plain,(
    ! [A_2] :
      ( k5_relat_1(k2_funct_1(A_2),A_2) = k6_relat_1(k2_relat_1(A_2))
      | ~ v2_funct_1(A_2)
      | ~ v1_funct_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_59,plain,(
    ! [A_2] :
      ( k5_relat_1(k2_funct_1(A_2),A_2) = k6_partfun1(k2_relat_1(A_2))
      | ~ v2_funct_1(A_2)
      | ~ v1_funct_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_4])).

tff(c_2730,plain,(
    ! [E_216,B_215,A_217,D_214,F_218,C_219] :
      ( k1_partfun1(A_217,B_215,C_219,D_214,E_216,F_218) = k5_relat_1(E_216,F_218)
      | ~ m1_subset_1(F_218,k1_zfmisc_1(k2_zfmisc_1(C_219,D_214)))
      | ~ v1_funct_1(F_218)
      | ~ m1_subset_1(E_216,k1_zfmisc_1(k2_zfmisc_1(A_217,B_215)))
      | ~ v1_funct_1(E_216) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_2738,plain,(
    ! [A_217,B_215,E_216] :
      ( k1_partfun1(A_217,B_215,'#skF_2','#skF_2',E_216,'#skF_3') = k5_relat_1(E_216,'#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(E_216,k1_zfmisc_1(k2_zfmisc_1(A_217,B_215)))
      | ~ v1_funct_1(E_216) ) ),
    inference(resolution,[status(thm)],[c_50,c_2730])).

tff(c_2887,plain,(
    ! [A_226,B_227,E_228] :
      ( k1_partfun1(A_226,B_227,'#skF_2','#skF_2',E_228,'#skF_3') = k5_relat_1(E_228,'#skF_3')
      | ~ m1_subset_1(E_228,k1_zfmisc_1(k2_zfmisc_1(A_226,B_227)))
      | ~ v1_funct_1(E_228) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_2738])).

tff(c_2893,plain,
    ( k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_1('#skF_3'),'#skF_3') = k5_relat_1(k2_funct_1('#skF_3'),'#skF_3')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2631,c_2887])).

tff(c_2908,plain,(
    k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_1('#skF_3'),'#skF_3') = k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2524,c_2893])).

tff(c_166,plain,(
    ! [C_63,A_64,B_65] :
      ( v2_funct_1(C_63)
      | ~ v3_funct_2(C_63,A_64,B_65)
      | ~ v1_funct_1(C_63)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1(A_64,B_65))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_172,plain,
    ( v2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_166])).

tff(c_176,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_172])).

tff(c_549,plain,(
    ! [A_111,B_112] :
      ( r2_relset_1(A_111,A_111,B_112,B_112)
      | ~ m1_subset_1(B_112,k1_zfmisc_1(k2_zfmisc_1(A_111,A_111)))
      | ~ m1_subset_1(B_112,k1_zfmisc_1(k2_zfmisc_1(A_111,A_111))) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_22])).

tff(c_555,plain,(
    ! [A_18] :
      ( r2_relset_1(A_18,A_18,k6_partfun1(A_18),k6_partfun1(A_18))
      | ~ m1_subset_1(k6_partfun1(A_18),k1_zfmisc_1(k2_zfmisc_1(A_18,A_18))) ) ),
    inference(resolution,[status(thm)],[c_57,c_549])).

tff(c_564,plain,(
    ! [A_18] : r2_relset_1(A_18,A_18,k6_partfun1(A_18),k6_partfun1(A_18)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_555])).

tff(c_82,plain,(
    ! [A_49,B_50,C_51] :
      ( k1_relset_1(A_49,B_50,C_51) = k1_relat_1(C_51)
      | ~ m1_subset_1(C_51,k1_zfmisc_1(k2_zfmisc_1(A_49,B_50))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_90,plain,(
    k1_relset_1('#skF_2','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_82])).

tff(c_203,plain,(
    ! [A_69,B_70] :
      ( k1_relset_1(A_69,A_69,B_70) = A_69
      | ~ m1_subset_1(B_70,k1_zfmisc_1(k2_zfmisc_1(A_69,A_69)))
      | ~ v1_funct_2(B_70,A_69,A_69)
      | ~ v1_funct_1(B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_209,plain,
    ( k1_relset_1('#skF_2','#skF_2','#skF_3') = '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_203])).

tff(c_214,plain,(
    k1_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_90,c_209])).

tff(c_6,plain,(
    ! [A_2] :
      ( k5_relat_1(A_2,k2_funct_1(A_2)) = k6_relat_1(k1_relat_1(A_2))
      | ~ v2_funct_1(A_2)
      | ~ v1_funct_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_58,plain,(
    ! [A_2] :
      ( k5_relat_1(A_2,k2_funct_1(A_2)) = k6_partfun1(k1_relat_1(A_2))
      | ~ v2_funct_1(A_2)
      | ~ v1_funct_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_6])).

tff(c_283,plain,(
    ! [A_85,B_86] :
      ( k2_funct_2(A_85,B_86) = k2_funct_1(B_86)
      | ~ m1_subset_1(B_86,k1_zfmisc_1(k2_zfmisc_1(A_85,A_85)))
      | ~ v3_funct_2(B_86,A_85,A_85)
      | ~ v1_funct_2(B_86,A_85,A_85)
      | ~ v1_funct_1(B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_289,plain,
    ( k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_283])).

tff(c_293,plain,(
    k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_289])).

tff(c_271,plain,(
    ! [A_82,B_83] :
      ( v1_funct_1(k2_funct_2(A_82,B_83))
      | ~ m1_subset_1(B_83,k1_zfmisc_1(k2_zfmisc_1(A_82,A_82)))
      | ~ v3_funct_2(B_83,A_82,A_82)
      | ~ v1_funct_2(B_83,A_82,A_82)
      | ~ v1_funct_1(B_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_277,plain,
    ( v1_funct_1(k2_funct_2('#skF_2','#skF_3'))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_271])).

tff(c_281,plain,(
    v1_funct_1(k2_funct_2('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_277])).

tff(c_303,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_293,c_281])).

tff(c_32,plain,(
    ! [A_29,B_30] :
      ( m1_subset_1(k2_funct_2(A_29,B_30),k1_zfmisc_1(k2_zfmisc_1(A_29,A_29)))
      | ~ m1_subset_1(B_30,k1_zfmisc_1(k2_zfmisc_1(A_29,A_29)))
      | ~ v3_funct_2(B_30,A_29,A_29)
      | ~ v1_funct_2(B_30,A_29,A_29)
      | ~ v1_funct_1(B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_483,plain,(
    ! [E_104,B_103,A_105,F_106,C_107,D_102] :
      ( k1_partfun1(A_105,B_103,C_107,D_102,E_104,F_106) = k5_relat_1(E_104,F_106)
      | ~ m1_subset_1(F_106,k1_zfmisc_1(k2_zfmisc_1(C_107,D_102)))
      | ~ v1_funct_1(F_106)
      | ~ m1_subset_1(E_104,k1_zfmisc_1(k2_zfmisc_1(A_105,B_103)))
      | ~ v1_funct_1(E_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_2160,plain,(
    ! [A_155,E_159,B_156,A_157,B_158] :
      ( k1_partfun1(A_155,B_158,A_157,A_157,E_159,k2_funct_2(A_157,B_156)) = k5_relat_1(E_159,k2_funct_2(A_157,B_156))
      | ~ v1_funct_1(k2_funct_2(A_157,B_156))
      | ~ m1_subset_1(E_159,k1_zfmisc_1(k2_zfmisc_1(A_155,B_158)))
      | ~ v1_funct_1(E_159)
      | ~ m1_subset_1(B_156,k1_zfmisc_1(k2_zfmisc_1(A_157,A_157)))
      | ~ v3_funct_2(B_156,A_157,A_157)
      | ~ v1_funct_2(B_156,A_157,A_157)
      | ~ v1_funct_1(B_156) ) ),
    inference(resolution,[status(thm)],[c_32,c_483])).

tff(c_2180,plain,(
    ! [A_157,B_156] :
      ( k1_partfun1('#skF_2','#skF_2',A_157,A_157,'#skF_3',k2_funct_2(A_157,B_156)) = k5_relat_1('#skF_3',k2_funct_2(A_157,B_156))
      | ~ v1_funct_1(k2_funct_2(A_157,B_156))
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(B_156,k1_zfmisc_1(k2_zfmisc_1(A_157,A_157)))
      | ~ v3_funct_2(B_156,A_157,A_157)
      | ~ v1_funct_2(B_156,A_157,A_157)
      | ~ v1_funct_1(B_156) ) ),
    inference(resolution,[status(thm)],[c_50,c_2160])).

tff(c_2246,plain,(
    ! [A_161,B_162] :
      ( k1_partfun1('#skF_2','#skF_2',A_161,A_161,'#skF_3',k2_funct_2(A_161,B_162)) = k5_relat_1('#skF_3',k2_funct_2(A_161,B_162))
      | ~ v1_funct_1(k2_funct_2(A_161,B_162))
      | ~ m1_subset_1(B_162,k1_zfmisc_1(k2_zfmisc_1(A_161,A_161)))
      | ~ v3_funct_2(B_162,A_161,A_161)
      | ~ v1_funct_2(B_162,A_161,A_161)
      | ~ v1_funct_1(B_162) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_2180])).

tff(c_2266,plain,
    ( k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_2('#skF_2','#skF_3')) = k5_relat_1('#skF_3',k2_funct_2('#skF_2','#skF_3'))
    | ~ v1_funct_1(k2_funct_2('#skF_2','#skF_3'))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_2246])).

tff(c_2292,plain,(
    k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_1('#skF_3')) = k5_relat_1('#skF_3',k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_303,c_293,c_293,c_293,c_2266])).

tff(c_48,plain,
    ( ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_2('#skF_2','#skF_3'),'#skF_3'),k6_partfun1('#skF_2'))
    | ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_2('#skF_2','#skF_3')),k6_partfun1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_80,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_2('#skF_2','#skF_3')),k6_partfun1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_304,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_1('#skF_3')),k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_293,c_80])).

tff(c_2293,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k5_relat_1('#skF_3',k2_funct_1('#skF_3')),k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2292,c_304])).

tff(c_2300,plain,
    ( ~ r2_relset_1('#skF_2','#skF_2',k6_partfun1(k1_relat_1('#skF_3')),k6_partfun1('#skF_2'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_2293])).

tff(c_2303,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_56,c_176,c_564,c_214,c_2300])).

tff(c_2304,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_2('#skF_2','#skF_3'),'#skF_3'),k6_partfun1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_2526,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_1('#skF_3'),'#skF_3'),k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2523,c_2304])).

tff(c_3256,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k5_relat_1(k2_funct_1('#skF_3'),'#skF_3'),k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2908,c_2526])).

tff(c_3263,plain,
    ( ~ r2_relset_1('#skF_2','#skF_2',k6_partfun1(k2_relat_1('#skF_3')),k6_partfun1('#skF_2'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_59,c_3256])).

tff(c_3266,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_56,c_2401,c_2882,c_2688,c_3263])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 18:17:29 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.13/2.19  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.13/2.21  
% 6.13/2.21  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.13/2.21  %$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v2_funct_2 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k3_relset_1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > k11_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_2 > #skF_3
% 6.13/2.21  
% 6.13/2.21  %Foreground sorts:
% 6.13/2.21  
% 6.13/2.21  
% 6.13/2.21  %Background operators:
% 6.13/2.21  
% 6.13/2.21  
% 6.13/2.21  %Foreground operators:
% 6.13/2.21  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 6.13/2.21  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 6.13/2.21  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.13/2.21  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 6.13/2.21  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 6.13/2.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.13/2.21  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 6.13/2.21  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.13/2.21  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 6.13/2.21  tff(k2_funct_2, type, k2_funct_2: ($i * $i) > $i).
% 6.13/2.21  tff(k3_relset_1, type, k3_relset_1: ($i * $i * $i) > $i).
% 6.13/2.21  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.13/2.21  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.13/2.21  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.13/2.21  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 6.13/2.21  tff('#skF_2', type, '#skF_2': $i).
% 6.13/2.21  tff('#skF_3', type, '#skF_3': $i).
% 6.13/2.21  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 6.13/2.21  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 6.13/2.21  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.13/2.21  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 6.13/2.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.13/2.21  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.13/2.21  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.13/2.21  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 6.13/2.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.13/2.21  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 6.13/2.21  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.13/2.21  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 6.13/2.21  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.13/2.21  
% 6.51/2.23  tff(f_150, negated_conjecture, ~(![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, k2_funct_2(A, B)), k6_partfun1(A)) & r2_relset_1(A, A, k1_partfun1(A, A, A, A, k2_funct_2(A, B), B), k6_partfun1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_funct_2)).
% 6.51/2.23  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 6.51/2.23  tff(f_91, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_funct_2)).
% 6.51/2.23  tff(f_129, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 6.51/2.23  tff(f_67, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 6.51/2.23  tff(f_79, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A))) => ((![D]: (r2_hidden(D, A) => (k11_relat_1(B, D) = k11_relat_1(C, D)))) => r2_relset_1(A, A, B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t54_relset_1)).
% 6.51/2.23  tff(f_127, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k2_funct_2(A, B) = k2_funct_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 6.51/2.23  tff(f_107, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (((v1_funct_1(k2_funct_2(A, B)) & v1_funct_2(k2_funct_2(A, B), A, A)) & v3_funct_2(k2_funct_2(A, B), A, A)) & m1_subset_1(k2_funct_2(A, B), k1_zfmisc_1(k2_zfmisc_1(A, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_2)).
% 6.51/2.23  tff(f_33, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_funct_1)).
% 6.51/2.23  tff(f_59, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k3_relset_1(A, B, C) = k4_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k3_relset_1)).
% 6.51/2.23  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 6.51/2.23  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k1_relset_1(B, A, k3_relset_1(A, B, C)) = k2_relset_1(A, B, C)) & (k2_relset_1(B, A, k3_relset_1(A, B, C)) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_relset_1)).
% 6.51/2.23  tff(f_137, axiom, (![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k1_relset_1(A, A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_funct_2)).
% 6.51/2.23  tff(f_43, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 6.51/2.23  tff(f_117, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 6.51/2.23  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 6.51/2.23  tff(c_50, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_150])).
% 6.51/2.23  tff(c_70, plain, (![C_44, A_45, B_46]: (v1_relat_1(C_44) | ~m1_subset_1(C_44, k1_zfmisc_1(k2_zfmisc_1(A_45, B_46))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.51/2.23  tff(c_78, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_50, c_70])).
% 6.51/2.23  tff(c_56, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_150])).
% 6.51/2.23  tff(c_52, plain, (v3_funct_2('#skF_3', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_150])).
% 6.51/2.23  tff(c_2391, plain, (![C_178, A_179, B_180]: (v2_funct_1(C_178) | ~v3_funct_2(C_178, A_179, B_180) | ~v1_funct_1(C_178) | ~m1_subset_1(C_178, k1_zfmisc_1(k2_zfmisc_1(A_179, B_180))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 6.51/2.23  tff(c_2397, plain, (v2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_50, c_2391])).
% 6.51/2.23  tff(c_2401, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_2397])).
% 6.51/2.23  tff(c_44, plain, (![A_39]: (k6_relat_1(A_39)=k6_partfun1(A_39))), inference(cnfTransformation, [status(thm)], [f_129])).
% 6.51/2.23  tff(c_20, plain, (![A_18]: (m1_subset_1(k6_relat_1(A_18), k1_zfmisc_1(k2_zfmisc_1(A_18, A_18))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 6.51/2.23  tff(c_57, plain, (![A_18]: (m1_subset_1(k6_partfun1(A_18), k1_zfmisc_1(k2_zfmisc_1(A_18, A_18))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_20])).
% 6.51/2.23  tff(c_22, plain, (![C_24, A_19, B_20]: (k11_relat_1(C_24, '#skF_1'(A_19, B_20, C_24))!=k11_relat_1(B_20, '#skF_1'(A_19, B_20, C_24)) | r2_relset_1(A_19, A_19, B_20, C_24) | ~m1_subset_1(C_24, k1_zfmisc_1(k2_zfmisc_1(A_19, A_19))) | ~m1_subset_1(B_20, k1_zfmisc_1(k2_zfmisc_1(A_19, A_19))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 6.51/2.23  tff(c_2862, plain, (![A_223, B_224]: (r2_relset_1(A_223, A_223, B_224, B_224) | ~m1_subset_1(B_224, k1_zfmisc_1(k2_zfmisc_1(A_223, A_223))) | ~m1_subset_1(B_224, k1_zfmisc_1(k2_zfmisc_1(A_223, A_223))))), inference(reflexivity, [status(thm), theory('equality')], [c_22])).
% 6.51/2.23  tff(c_2870, plain, (![A_18]: (r2_relset_1(A_18, A_18, k6_partfun1(A_18), k6_partfun1(A_18)) | ~m1_subset_1(k6_partfun1(A_18), k1_zfmisc_1(k2_zfmisc_1(A_18, A_18))))), inference(resolution, [status(thm)], [c_57, c_2862])).
% 6.51/2.23  tff(c_2882, plain, (![A_18]: (r2_relset_1(A_18, A_18, k6_partfun1(A_18), k6_partfun1(A_18)))), inference(demodulation, [status(thm), theory('equality')], [c_57, c_2870])).
% 6.51/2.23  tff(c_54, plain, (v1_funct_2('#skF_3', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_150])).
% 6.51/2.23  tff(c_2513, plain, (![A_200, B_201]: (k2_funct_2(A_200, B_201)=k2_funct_1(B_201) | ~m1_subset_1(B_201, k1_zfmisc_1(k2_zfmisc_1(A_200, A_200))) | ~v3_funct_2(B_201, A_200, A_200) | ~v1_funct_2(B_201, A_200, A_200) | ~v1_funct_1(B_201))), inference(cnfTransformation, [status(thm)], [f_127])).
% 6.51/2.23  tff(c_2519, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_50, c_2513])).
% 6.51/2.23  tff(c_2523, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_2519])).
% 6.51/2.23  tff(c_2501, plain, (![A_197, B_198]: (v1_funct_1(k2_funct_2(A_197, B_198)) | ~m1_subset_1(B_198, k1_zfmisc_1(k2_zfmisc_1(A_197, A_197))) | ~v3_funct_2(B_198, A_197, A_197) | ~v1_funct_2(B_198, A_197, A_197) | ~v1_funct_1(B_198))), inference(cnfTransformation, [status(thm)], [f_107])).
% 6.51/2.23  tff(c_2507, plain, (v1_funct_1(k2_funct_2('#skF_2', '#skF_3')) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_50, c_2501])).
% 6.51/2.23  tff(c_2511, plain, (v1_funct_1(k2_funct_2('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_2507])).
% 6.51/2.23  tff(c_2524, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2523, c_2511])).
% 6.51/2.24  tff(c_2541, plain, (![A_205, B_206]: (v1_funct_2(k2_funct_2(A_205, B_206), A_205, A_205) | ~m1_subset_1(B_206, k1_zfmisc_1(k2_zfmisc_1(A_205, A_205))) | ~v3_funct_2(B_206, A_205, A_205) | ~v1_funct_2(B_206, A_205, A_205) | ~v1_funct_1(B_206))), inference(cnfTransformation, [status(thm)], [f_107])).
% 6.51/2.24  tff(c_2545, plain, (v1_funct_2(k2_funct_2('#skF_2', '#skF_3'), '#skF_2', '#skF_2') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_50, c_2541])).
% 6.51/2.24  tff(c_2549, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_2523, c_2545])).
% 6.51/2.24  tff(c_2, plain, (![A_1]: (k4_relat_1(A_1)=k2_funct_1(A_1) | ~v2_funct_1(A_1) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.51/2.24  tff(c_2404, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_2401, c_2])).
% 6.51/2.24  tff(c_2407, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_56, c_2404])).
% 6.51/2.24  tff(c_2320, plain, (![A_167, B_168, C_169]: (k3_relset_1(A_167, B_168, C_169)=k4_relat_1(C_169) | ~m1_subset_1(C_169, k1_zfmisc_1(k2_zfmisc_1(A_167, B_168))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.51/2.24  tff(c_2328, plain, (k3_relset_1('#skF_2', '#skF_2', '#skF_3')=k4_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_50, c_2320])).
% 6.51/2.24  tff(c_2408, plain, (k3_relset_1('#skF_2', '#skF_2', '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2407, c_2328])).
% 6.51/2.24  tff(c_2351, plain, (![A_172, B_173, C_174]: (k2_relset_1(A_172, B_173, C_174)=k2_relat_1(C_174) | ~m1_subset_1(C_174, k1_zfmisc_1(k2_zfmisc_1(A_172, B_173))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.51/2.24  tff(c_2359, plain, (k2_relset_1('#skF_2', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_50, c_2351])).
% 6.51/2.24  tff(c_2430, plain, (![B_186, A_187, C_188]: (k1_relset_1(B_186, A_187, k3_relset_1(A_187, B_186, C_188))=k2_relset_1(A_187, B_186, C_188) | ~m1_subset_1(C_188, k1_zfmisc_1(k2_zfmisc_1(A_187, B_186))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.51/2.24  tff(c_2434, plain, (k1_relset_1('#skF_2', '#skF_2', k3_relset_1('#skF_2', '#skF_2', '#skF_3'))=k2_relset_1('#skF_2', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_50, c_2430])).
% 6.51/2.24  tff(c_2438, plain, (k1_relset_1('#skF_2', '#skF_2', k2_funct_1('#skF_3'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2408, c_2359, c_2434])).
% 6.51/2.24  tff(c_2570, plain, (![A_212, B_213]: (m1_subset_1(k2_funct_2(A_212, B_213), k1_zfmisc_1(k2_zfmisc_1(A_212, A_212))) | ~m1_subset_1(B_213, k1_zfmisc_1(k2_zfmisc_1(A_212, A_212))) | ~v3_funct_2(B_213, A_212, A_212) | ~v1_funct_2(B_213, A_212, A_212) | ~v1_funct_1(B_213))), inference(cnfTransformation, [status(thm)], [f_107])).
% 6.51/2.24  tff(c_2614, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2523, c_2570])).
% 6.51/2.24  tff(c_2631, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_2614])).
% 6.51/2.24  tff(c_46, plain, (![A_40, B_41]: (k1_relset_1(A_40, A_40, B_41)=A_40 | ~m1_subset_1(B_41, k1_zfmisc_1(k2_zfmisc_1(A_40, A_40))) | ~v1_funct_2(B_41, A_40, A_40) | ~v1_funct_1(B_41))), inference(cnfTransformation, [status(thm)], [f_137])).
% 6.51/2.24  tff(c_2649, plain, (k1_relset_1('#skF_2', '#skF_2', k2_funct_1('#skF_3'))='#skF_2' | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_2631, c_46])).
% 6.51/2.24  tff(c_2688, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2524, c_2549, c_2438, c_2649])).
% 6.51/2.24  tff(c_4, plain, (![A_2]: (k5_relat_1(k2_funct_1(A_2), A_2)=k6_relat_1(k2_relat_1(A_2)) | ~v2_funct_1(A_2) | ~v1_funct_1(A_2) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.51/2.24  tff(c_59, plain, (![A_2]: (k5_relat_1(k2_funct_1(A_2), A_2)=k6_partfun1(k2_relat_1(A_2)) | ~v2_funct_1(A_2) | ~v1_funct_1(A_2) | ~v1_relat_1(A_2))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_4])).
% 6.51/2.24  tff(c_2730, plain, (![E_216, B_215, A_217, D_214, F_218, C_219]: (k1_partfun1(A_217, B_215, C_219, D_214, E_216, F_218)=k5_relat_1(E_216, F_218) | ~m1_subset_1(F_218, k1_zfmisc_1(k2_zfmisc_1(C_219, D_214))) | ~v1_funct_1(F_218) | ~m1_subset_1(E_216, k1_zfmisc_1(k2_zfmisc_1(A_217, B_215))) | ~v1_funct_1(E_216))), inference(cnfTransformation, [status(thm)], [f_117])).
% 6.51/2.24  tff(c_2738, plain, (![A_217, B_215, E_216]: (k1_partfun1(A_217, B_215, '#skF_2', '#skF_2', E_216, '#skF_3')=k5_relat_1(E_216, '#skF_3') | ~v1_funct_1('#skF_3') | ~m1_subset_1(E_216, k1_zfmisc_1(k2_zfmisc_1(A_217, B_215))) | ~v1_funct_1(E_216))), inference(resolution, [status(thm)], [c_50, c_2730])).
% 6.51/2.24  tff(c_2887, plain, (![A_226, B_227, E_228]: (k1_partfun1(A_226, B_227, '#skF_2', '#skF_2', E_228, '#skF_3')=k5_relat_1(E_228, '#skF_3') | ~m1_subset_1(E_228, k1_zfmisc_1(k2_zfmisc_1(A_226, B_227))) | ~v1_funct_1(E_228))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_2738])).
% 6.51/2.24  tff(c_2893, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_1('#skF_3'), '#skF_3')=k5_relat_1(k2_funct_1('#skF_3'), '#skF_3') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_2631, c_2887])).
% 6.51/2.24  tff(c_2908, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_1('#skF_3'), '#skF_3')=k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2524, c_2893])).
% 6.51/2.24  tff(c_166, plain, (![C_63, A_64, B_65]: (v2_funct_1(C_63) | ~v3_funct_2(C_63, A_64, B_65) | ~v1_funct_1(C_63) | ~m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1(A_64, B_65))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 6.51/2.24  tff(c_172, plain, (v2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_50, c_166])).
% 6.51/2.24  tff(c_176, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_172])).
% 6.51/2.24  tff(c_549, plain, (![A_111, B_112]: (r2_relset_1(A_111, A_111, B_112, B_112) | ~m1_subset_1(B_112, k1_zfmisc_1(k2_zfmisc_1(A_111, A_111))) | ~m1_subset_1(B_112, k1_zfmisc_1(k2_zfmisc_1(A_111, A_111))))), inference(reflexivity, [status(thm), theory('equality')], [c_22])).
% 6.51/2.24  tff(c_555, plain, (![A_18]: (r2_relset_1(A_18, A_18, k6_partfun1(A_18), k6_partfun1(A_18)) | ~m1_subset_1(k6_partfun1(A_18), k1_zfmisc_1(k2_zfmisc_1(A_18, A_18))))), inference(resolution, [status(thm)], [c_57, c_549])).
% 6.51/2.24  tff(c_564, plain, (![A_18]: (r2_relset_1(A_18, A_18, k6_partfun1(A_18), k6_partfun1(A_18)))), inference(demodulation, [status(thm), theory('equality')], [c_57, c_555])).
% 6.51/2.24  tff(c_82, plain, (![A_49, B_50, C_51]: (k1_relset_1(A_49, B_50, C_51)=k1_relat_1(C_51) | ~m1_subset_1(C_51, k1_zfmisc_1(k2_zfmisc_1(A_49, B_50))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.51/2.24  tff(c_90, plain, (k1_relset_1('#skF_2', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_50, c_82])).
% 6.51/2.24  tff(c_203, plain, (![A_69, B_70]: (k1_relset_1(A_69, A_69, B_70)=A_69 | ~m1_subset_1(B_70, k1_zfmisc_1(k2_zfmisc_1(A_69, A_69))) | ~v1_funct_2(B_70, A_69, A_69) | ~v1_funct_1(B_70))), inference(cnfTransformation, [status(thm)], [f_137])).
% 6.51/2.24  tff(c_209, plain, (k1_relset_1('#skF_2', '#skF_2', '#skF_3')='#skF_2' | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_50, c_203])).
% 6.51/2.24  tff(c_214, plain, (k1_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_90, c_209])).
% 6.51/2.24  tff(c_6, plain, (![A_2]: (k5_relat_1(A_2, k2_funct_1(A_2))=k6_relat_1(k1_relat_1(A_2)) | ~v2_funct_1(A_2) | ~v1_funct_1(A_2) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.51/2.24  tff(c_58, plain, (![A_2]: (k5_relat_1(A_2, k2_funct_1(A_2))=k6_partfun1(k1_relat_1(A_2)) | ~v2_funct_1(A_2) | ~v1_funct_1(A_2) | ~v1_relat_1(A_2))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_6])).
% 6.51/2.24  tff(c_283, plain, (![A_85, B_86]: (k2_funct_2(A_85, B_86)=k2_funct_1(B_86) | ~m1_subset_1(B_86, k1_zfmisc_1(k2_zfmisc_1(A_85, A_85))) | ~v3_funct_2(B_86, A_85, A_85) | ~v1_funct_2(B_86, A_85, A_85) | ~v1_funct_1(B_86))), inference(cnfTransformation, [status(thm)], [f_127])).
% 6.51/2.24  tff(c_289, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_50, c_283])).
% 6.51/2.24  tff(c_293, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_289])).
% 6.51/2.24  tff(c_271, plain, (![A_82, B_83]: (v1_funct_1(k2_funct_2(A_82, B_83)) | ~m1_subset_1(B_83, k1_zfmisc_1(k2_zfmisc_1(A_82, A_82))) | ~v3_funct_2(B_83, A_82, A_82) | ~v1_funct_2(B_83, A_82, A_82) | ~v1_funct_1(B_83))), inference(cnfTransformation, [status(thm)], [f_107])).
% 6.51/2.24  tff(c_277, plain, (v1_funct_1(k2_funct_2('#skF_2', '#skF_3')) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_50, c_271])).
% 6.51/2.24  tff(c_281, plain, (v1_funct_1(k2_funct_2('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_277])).
% 6.51/2.24  tff(c_303, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_293, c_281])).
% 6.51/2.24  tff(c_32, plain, (![A_29, B_30]: (m1_subset_1(k2_funct_2(A_29, B_30), k1_zfmisc_1(k2_zfmisc_1(A_29, A_29))) | ~m1_subset_1(B_30, k1_zfmisc_1(k2_zfmisc_1(A_29, A_29))) | ~v3_funct_2(B_30, A_29, A_29) | ~v1_funct_2(B_30, A_29, A_29) | ~v1_funct_1(B_30))), inference(cnfTransformation, [status(thm)], [f_107])).
% 6.51/2.24  tff(c_483, plain, (![E_104, B_103, A_105, F_106, C_107, D_102]: (k1_partfun1(A_105, B_103, C_107, D_102, E_104, F_106)=k5_relat_1(E_104, F_106) | ~m1_subset_1(F_106, k1_zfmisc_1(k2_zfmisc_1(C_107, D_102))) | ~v1_funct_1(F_106) | ~m1_subset_1(E_104, k1_zfmisc_1(k2_zfmisc_1(A_105, B_103))) | ~v1_funct_1(E_104))), inference(cnfTransformation, [status(thm)], [f_117])).
% 6.51/2.24  tff(c_2160, plain, (![A_155, E_159, B_156, A_157, B_158]: (k1_partfun1(A_155, B_158, A_157, A_157, E_159, k2_funct_2(A_157, B_156))=k5_relat_1(E_159, k2_funct_2(A_157, B_156)) | ~v1_funct_1(k2_funct_2(A_157, B_156)) | ~m1_subset_1(E_159, k1_zfmisc_1(k2_zfmisc_1(A_155, B_158))) | ~v1_funct_1(E_159) | ~m1_subset_1(B_156, k1_zfmisc_1(k2_zfmisc_1(A_157, A_157))) | ~v3_funct_2(B_156, A_157, A_157) | ~v1_funct_2(B_156, A_157, A_157) | ~v1_funct_1(B_156))), inference(resolution, [status(thm)], [c_32, c_483])).
% 6.51/2.24  tff(c_2180, plain, (![A_157, B_156]: (k1_partfun1('#skF_2', '#skF_2', A_157, A_157, '#skF_3', k2_funct_2(A_157, B_156))=k5_relat_1('#skF_3', k2_funct_2(A_157, B_156)) | ~v1_funct_1(k2_funct_2(A_157, B_156)) | ~v1_funct_1('#skF_3') | ~m1_subset_1(B_156, k1_zfmisc_1(k2_zfmisc_1(A_157, A_157))) | ~v3_funct_2(B_156, A_157, A_157) | ~v1_funct_2(B_156, A_157, A_157) | ~v1_funct_1(B_156))), inference(resolution, [status(thm)], [c_50, c_2160])).
% 6.51/2.24  tff(c_2246, plain, (![A_161, B_162]: (k1_partfun1('#skF_2', '#skF_2', A_161, A_161, '#skF_3', k2_funct_2(A_161, B_162))=k5_relat_1('#skF_3', k2_funct_2(A_161, B_162)) | ~v1_funct_1(k2_funct_2(A_161, B_162)) | ~m1_subset_1(B_162, k1_zfmisc_1(k2_zfmisc_1(A_161, A_161))) | ~v3_funct_2(B_162, A_161, A_161) | ~v1_funct_2(B_162, A_161, A_161) | ~v1_funct_1(B_162))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_2180])).
% 6.51/2.24  tff(c_2266, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_2('#skF_2', '#skF_3'))=k5_relat_1('#skF_3', k2_funct_2('#skF_2', '#skF_3')) | ~v1_funct_1(k2_funct_2('#skF_2', '#skF_3')) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_50, c_2246])).
% 6.51/2.24  tff(c_2292, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_1('#skF_3'))=k5_relat_1('#skF_3', k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_303, c_293, c_293, c_293, c_2266])).
% 6.51/2.24  tff(c_48, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_2('#skF_2', '#skF_3'), '#skF_3'), k6_partfun1('#skF_2')) | ~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_2('#skF_2', '#skF_3')), k6_partfun1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_150])).
% 6.51/2.24  tff(c_80, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_2('#skF_2', '#skF_3')), k6_partfun1('#skF_2'))), inference(splitLeft, [status(thm)], [c_48])).
% 6.51/2.24  tff(c_304, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_1('#skF_3')), k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_293, c_80])).
% 6.51/2.24  tff(c_2293, plain, (~r2_relset_1('#skF_2', '#skF_2', k5_relat_1('#skF_3', k2_funct_1('#skF_3')), k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2292, c_304])).
% 6.51/2.24  tff(c_2300, plain, (~r2_relset_1('#skF_2', '#skF_2', k6_partfun1(k1_relat_1('#skF_3')), k6_partfun1('#skF_2')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_58, c_2293])).
% 6.51/2.24  tff(c_2303, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_56, c_176, c_564, c_214, c_2300])).
% 6.51/2.24  tff(c_2304, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_2('#skF_2', '#skF_3'), '#skF_3'), k6_partfun1('#skF_2'))), inference(splitRight, [status(thm)], [c_48])).
% 6.51/2.24  tff(c_2526, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_1('#skF_3'), '#skF_3'), k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2523, c_2304])).
% 6.51/2.24  tff(c_3256, plain, (~r2_relset_1('#skF_2', '#skF_2', k5_relat_1(k2_funct_1('#skF_3'), '#skF_3'), k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2908, c_2526])).
% 6.51/2.24  tff(c_3263, plain, (~r2_relset_1('#skF_2', '#skF_2', k6_partfun1(k2_relat_1('#skF_3')), k6_partfun1('#skF_2')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_59, c_3256])).
% 6.51/2.24  tff(c_3266, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_56, c_2401, c_2882, c_2688, c_3263])).
% 6.51/2.24  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.51/2.24  
% 6.51/2.24  Inference rules
% 6.51/2.24  ----------------------
% 6.51/2.24  #Ref     : 2
% 6.51/2.24  #Sup     : 758
% 6.51/2.24  #Fact    : 0
% 6.51/2.24  #Define  : 0
% 6.51/2.24  #Split   : 16
% 6.51/2.24  #Chain   : 0
% 6.51/2.24  #Close   : 0
% 6.51/2.24  
% 6.51/2.24  Ordering : KBO
% 6.51/2.24  
% 6.51/2.24  Simplification rules
% 6.51/2.24  ----------------------
% 6.51/2.24  #Subsume      : 0
% 6.51/2.24  #Demod        : 1568
% 6.51/2.24  #Tautology    : 328
% 6.51/2.24  #SimpNegUnit  : 0
% 6.51/2.24  #BackRed      : 59
% 6.51/2.24  
% 6.51/2.24  #Partial instantiations: 0
% 6.51/2.24  #Strategies tried      : 1
% 6.51/2.24  
% 6.51/2.24  Timing (in seconds)
% 6.51/2.24  ----------------------
% 6.51/2.24  Preprocessing        : 0.35
% 6.51/2.24  Parsing              : 0.19
% 6.51/2.24  CNF conversion       : 0.02
% 6.51/2.24  Main loop            : 1.10
% 6.51/2.24  Inferencing          : 0.36
% 6.51/2.24  Reduction            : 0.43
% 6.51/2.24  Demodulation         : 0.34
% 6.51/2.24  BG Simplification    : 0.04
% 6.51/2.24  Subsumption          : 0.20
% 6.51/2.24  Abstraction          : 0.05
% 6.51/2.24  MUC search           : 0.00
% 6.51/2.24  Cooper               : 0.00
% 6.51/2.24  Total                : 1.51
% 6.51/2.24  Index Insertion      : 0.00
% 6.51/2.24  Index Deletion       : 0.00
% 6.51/2.24  Index Matching       : 0.00
% 6.51/2.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
