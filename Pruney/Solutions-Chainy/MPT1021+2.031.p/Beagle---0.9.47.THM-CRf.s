%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:04 EST 2020

% Result     : Theorem 6.53s
% Output     : CNFRefutation 6.53s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 346 expanded)
%              Number of leaves         :   43 ( 150 expanded)
%              Depth                    :    9
%              Number of atoms          :  271 (1063 expanded)
%              Number of equality atoms :   40 (  82 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

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

tff(f_151,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & v3_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ( r2_relset_1(A,A,k1_partfun1(A,A,A,A,B,k2_funct_2(A,B)),k6_partfun1(A))
          & r2_relset_1(A,A,k1_partfun1(A,A,A,A,k2_funct_2(A,B),B),k6_partfun1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_funct_2)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_95,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_55,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_130,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_35,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_128,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k2_funct_2(A,B) = k2_funct_1(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

tff(f_91,axiom,(
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

tff(f_118,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_108,axiom,(
    ! [A,B] :
    ? [C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
      & v1_relat_1(C)
      & v4_relat_1(C,A)
      & v5_relat_1(C,B)
      & v1_funct_1(C)
      & v1_funct_2(C,A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_funct_2)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_138,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k1_relset_1(A,A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_2)).

tff(c_60,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_85,plain,(
    ! [C_50,A_51,B_52] :
      ( v1_relat_1(C_50)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k2_zfmisc_1(A_51,B_52))) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_93,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_85])).

tff(c_66,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_62,plain,(
    v3_funct_2('#skF_3','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_2455,plain,(
    ! [C_238,A_239,B_240] :
      ( v2_funct_1(C_238)
      | ~ v3_funct_2(C_238,A_239,B_240)
      | ~ v1_funct_1(C_238)
      | ~ m1_subset_1(C_238,k1_zfmisc_1(k2_zfmisc_1(A_239,B_240))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_2464,plain,
    ( v2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_2455])).

tff(c_2471,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_62,c_2464])).

tff(c_36,plain,(
    ! [A_22] : m1_subset_1(k6_partfun1(A_22),k1_zfmisc_1(k2_zfmisc_1(A_22,A_22))) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_2493,plain,(
    ! [A_250,B_251,C_252,D_253] :
      ( r2_relset_1(A_250,B_251,C_252,C_252)
      | ~ m1_subset_1(D_253,k1_zfmisc_1(k2_zfmisc_1(A_250,B_251)))
      | ~ m1_subset_1(C_252,k1_zfmisc_1(k2_zfmisc_1(A_250,B_251))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2552,plain,(
    ! [A_258,C_259] :
      ( r2_relset_1(A_258,A_258,C_259,C_259)
      | ~ m1_subset_1(C_259,k1_zfmisc_1(k2_zfmisc_1(A_258,A_258))) ) ),
    inference(resolution,[status(thm)],[c_36,c_2493])).

tff(c_2561,plain,(
    ! [A_22] : r2_relset_1(A_22,A_22,k6_partfun1(A_22),k6_partfun1(A_22)) ),
    inference(resolution,[status(thm)],[c_36,c_2552])).

tff(c_101,plain,(
    ! [C_56,B_57,A_58] :
      ( v5_relat_1(C_56,B_57)
      | ~ m1_subset_1(C_56,k1_zfmisc_1(k2_zfmisc_1(A_58,B_57))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_114,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_101])).

tff(c_2275,plain,(
    ! [B_205,A_206] :
      ( k2_relat_1(B_205) = A_206
      | ~ v2_funct_2(B_205,A_206)
      | ~ v5_relat_1(B_205,A_206)
      | ~ v1_relat_1(B_205) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_2281,plain,
    ( k2_relat_1('#skF_3') = '#skF_2'
    | ~ v2_funct_2('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_114,c_2275])).

tff(c_2290,plain,
    ( k2_relat_1('#skF_3') = '#skF_2'
    | ~ v2_funct_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_2281])).

tff(c_2294,plain,(
    ~ v2_funct_2('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_2290])).

tff(c_2369,plain,(
    ! [C_224,B_225,A_226] :
      ( v2_funct_2(C_224,B_225)
      | ~ v3_funct_2(C_224,A_226,B_225)
      | ~ v1_funct_1(C_224)
      | ~ m1_subset_1(C_224,k1_zfmisc_1(k2_zfmisc_1(A_226,B_225))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_2378,plain,
    ( v2_funct_2('#skF_3','#skF_2')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_2369])).

tff(c_2385,plain,(
    v2_funct_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_62,c_2378])).

tff(c_2387,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2294,c_2385])).

tff(c_2388,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_2290])).

tff(c_54,plain,(
    ! [A_34] : k6_relat_1(A_34) = k6_partfun1(A_34) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_2,plain,(
    ! [A_1] :
      ( k5_relat_1(k2_funct_1(A_1),A_1) = k6_relat_1(k2_relat_1(A_1))
      | ~ v2_funct_1(A_1)
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_68,plain,(
    ! [A_1] :
      ( k5_relat_1(k2_funct_1(A_1),A_1) = k6_partfun1(k2_relat_1(A_1))
      | ~ v2_funct_1(A_1)
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_2])).

tff(c_64,plain,(
    v1_funct_2('#skF_3','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_2598,plain,(
    ! [A_267,B_268] :
      ( k2_funct_2(A_267,B_268) = k2_funct_1(B_268)
      | ~ m1_subset_1(B_268,k1_zfmisc_1(k2_zfmisc_1(A_267,A_267)))
      | ~ v3_funct_2(B_268,A_267,A_267)
      | ~ v1_funct_2(B_268,A_267,A_267)
      | ~ v1_funct_1(B_268) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_2608,plain,
    ( k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_2598])).

tff(c_2615,plain,(
    k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_2608])).

tff(c_2566,plain,(
    ! [A_261,B_262] :
      ( v1_funct_1(k2_funct_2(A_261,B_262))
      | ~ m1_subset_1(B_262,k1_zfmisc_1(k2_zfmisc_1(A_261,A_261)))
      | ~ v3_funct_2(B_262,A_261,A_261)
      | ~ v1_funct_2(B_262,A_261,A_261)
      | ~ v1_funct_1(B_262) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_2576,plain,
    ( v1_funct_1(k2_funct_2('#skF_2','#skF_3'))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_2566])).

tff(c_2583,plain,(
    v1_funct_1(k2_funct_2('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_2576])).

tff(c_2616,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2615,c_2583])).

tff(c_26,plain,(
    ! [A_20,B_21] :
      ( m1_subset_1(k2_funct_2(A_20,B_21),k1_zfmisc_1(k2_zfmisc_1(A_20,A_20)))
      | ~ m1_subset_1(B_21,k1_zfmisc_1(k2_zfmisc_1(A_20,A_20)))
      | ~ v3_funct_2(B_21,A_20,A_20)
      | ~ v1_funct_2(B_21,A_20,A_20)
      | ~ v1_funct_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_2790,plain,(
    ! [A_285,F_286,D_283,E_288,C_287,B_284] :
      ( k1_partfun1(A_285,B_284,C_287,D_283,E_288,F_286) = k5_relat_1(E_288,F_286)
      | ~ m1_subset_1(F_286,k1_zfmisc_1(k2_zfmisc_1(C_287,D_283)))
      | ~ v1_funct_1(F_286)
      | ~ m1_subset_1(E_288,k1_zfmisc_1(k2_zfmisc_1(A_285,B_284)))
      | ~ v1_funct_1(E_288) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_2800,plain,(
    ! [A_285,B_284,E_288] :
      ( k1_partfun1(A_285,B_284,'#skF_2','#skF_2',E_288,'#skF_3') = k5_relat_1(E_288,'#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(E_288,k1_zfmisc_1(k2_zfmisc_1(A_285,B_284)))
      | ~ v1_funct_1(E_288) ) ),
    inference(resolution,[status(thm)],[c_60,c_2790])).

tff(c_2823,plain,(
    ! [A_289,B_290,E_291] :
      ( k1_partfun1(A_289,B_290,'#skF_2','#skF_2',E_291,'#skF_3') = k5_relat_1(E_291,'#skF_3')
      | ~ m1_subset_1(E_291,k1_zfmisc_1(k2_zfmisc_1(A_289,B_290)))
      | ~ v1_funct_1(E_291) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_2800])).

tff(c_3073,plain,(
    ! [A_297,B_298] :
      ( k1_partfun1(A_297,A_297,'#skF_2','#skF_2',k2_funct_2(A_297,B_298),'#skF_3') = k5_relat_1(k2_funct_2(A_297,B_298),'#skF_3')
      | ~ v1_funct_1(k2_funct_2(A_297,B_298))
      | ~ m1_subset_1(B_298,k1_zfmisc_1(k2_zfmisc_1(A_297,A_297)))
      | ~ v3_funct_2(B_298,A_297,A_297)
      | ~ v1_funct_2(B_298,A_297,A_297)
      | ~ v1_funct_1(B_298) ) ),
    inference(resolution,[status(thm)],[c_26,c_2823])).

tff(c_3088,plain,
    ( k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_2('#skF_2','#skF_3'),'#skF_3') = k5_relat_1(k2_funct_2('#skF_2','#skF_3'),'#skF_3')
    | ~ v1_funct_1(k2_funct_2('#skF_2','#skF_3'))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_3073])).

tff(c_3105,plain,(
    k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_1('#skF_3'),'#skF_3') = k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_2616,c_2615,c_2615,c_2615,c_3088])).

tff(c_295,plain,(
    ! [C_94,A_95,B_96] :
      ( v2_funct_1(C_94)
      | ~ v3_funct_2(C_94,A_95,B_96)
      | ~ v1_funct_1(C_94)
      | ~ m1_subset_1(C_94,k1_zfmisc_1(k2_zfmisc_1(A_95,B_96))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_304,plain,
    ( v2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_295])).

tff(c_311,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_62,c_304])).

tff(c_48,plain,(
    ! [A_23,B_24] : m1_subset_1('#skF_1'(A_23,B_24),k1_zfmisc_1(k2_zfmisc_1(A_23,B_24))) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_368,plain,(
    ! [A_106,B_107,C_108,D_109] :
      ( r2_relset_1(A_106,B_107,C_108,C_108)
      | ~ m1_subset_1(D_109,k1_zfmisc_1(k2_zfmisc_1(A_106,B_107)))
      | ~ m1_subset_1(C_108,k1_zfmisc_1(k2_zfmisc_1(A_106,B_107))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_379,plain,(
    ! [A_112,B_113,C_114] :
      ( r2_relset_1(A_112,B_113,C_114,C_114)
      | ~ m1_subset_1(C_114,k1_zfmisc_1(k2_zfmisc_1(A_112,B_113))) ) ),
    inference(resolution,[status(thm)],[c_48,c_368])).

tff(c_387,plain,(
    ! [A_22] : r2_relset_1(A_22,A_22,k6_partfun1(A_22),k6_partfun1(A_22)) ),
    inference(resolution,[status(thm)],[c_36,c_379])).

tff(c_152,plain,(
    ! [A_67,B_68,C_69] :
      ( k1_relset_1(A_67,B_68,C_69) = k1_relat_1(C_69)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1(A_67,B_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_164,plain,(
    k1_relset_1('#skF_2','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_152])).

tff(c_331,plain,(
    ! [A_103,B_104] :
      ( k1_relset_1(A_103,A_103,B_104) = A_103
      | ~ m1_subset_1(B_104,k1_zfmisc_1(k2_zfmisc_1(A_103,A_103)))
      | ~ v1_funct_2(B_104,A_103,A_103)
      | ~ v1_funct_1(B_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_341,plain,
    ( k1_relset_1('#skF_2','#skF_2','#skF_3') = '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_331])).

tff(c_349,plain,(
    k1_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_164,c_341])).

tff(c_4,plain,(
    ! [A_1] :
      ( k5_relat_1(A_1,k2_funct_1(A_1)) = k6_relat_1(k1_relat_1(A_1))
      | ~ v2_funct_1(A_1)
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_67,plain,(
    ! [A_1] :
      ( k5_relat_1(A_1,k2_funct_1(A_1)) = k6_partfun1(k1_relat_1(A_1))
      | ~ v2_funct_1(A_1)
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_4])).

tff(c_409,plain,(
    ! [A_120,B_121] :
      ( k2_funct_2(A_120,B_121) = k2_funct_1(B_121)
      | ~ m1_subset_1(B_121,k1_zfmisc_1(k2_zfmisc_1(A_120,A_120)))
      | ~ v3_funct_2(B_121,A_120,A_120)
      | ~ v1_funct_2(B_121,A_120,A_120)
      | ~ v1_funct_1(B_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_419,plain,
    ( k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_409])).

tff(c_426,plain,(
    k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_419])).

tff(c_391,plain,(
    ! [A_118,B_119] :
      ( v1_funct_1(k2_funct_2(A_118,B_119))
      | ~ m1_subset_1(B_119,k1_zfmisc_1(k2_zfmisc_1(A_118,A_118)))
      | ~ v3_funct_2(B_119,A_118,A_118)
      | ~ v1_funct_2(B_119,A_118,A_118)
      | ~ v1_funct_1(B_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_401,plain,
    ( v1_funct_1(k2_funct_2('#skF_2','#skF_3'))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_391])).

tff(c_408,plain,(
    v1_funct_1(k2_funct_2('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_401])).

tff(c_427,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_426,c_408])).

tff(c_591,plain,(
    ! [B_137,C_140,A_138,F_139,D_136,E_141] :
      ( k1_partfun1(A_138,B_137,C_140,D_136,E_141,F_139) = k5_relat_1(E_141,F_139)
      | ~ m1_subset_1(F_139,k1_zfmisc_1(k2_zfmisc_1(C_140,D_136)))
      | ~ v1_funct_1(F_139)
      | ~ m1_subset_1(E_141,k1_zfmisc_1(k2_zfmisc_1(A_138,B_137)))
      | ~ v1_funct_1(E_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_2121,plain,(
    ! [A_195,B_194,A_193,B_197,E_196] :
      ( k1_partfun1(A_193,B_197,A_195,A_195,E_196,k2_funct_2(A_195,B_194)) = k5_relat_1(E_196,k2_funct_2(A_195,B_194))
      | ~ v1_funct_1(k2_funct_2(A_195,B_194))
      | ~ m1_subset_1(E_196,k1_zfmisc_1(k2_zfmisc_1(A_193,B_197)))
      | ~ v1_funct_1(E_196)
      | ~ m1_subset_1(B_194,k1_zfmisc_1(k2_zfmisc_1(A_195,A_195)))
      | ~ v3_funct_2(B_194,A_195,A_195)
      | ~ v1_funct_2(B_194,A_195,A_195)
      | ~ v1_funct_1(B_194) ) ),
    inference(resolution,[status(thm)],[c_26,c_591])).

tff(c_2143,plain,(
    ! [A_195,B_194] :
      ( k1_partfun1('#skF_2','#skF_2',A_195,A_195,'#skF_3',k2_funct_2(A_195,B_194)) = k5_relat_1('#skF_3',k2_funct_2(A_195,B_194))
      | ~ v1_funct_1(k2_funct_2(A_195,B_194))
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(B_194,k1_zfmisc_1(k2_zfmisc_1(A_195,A_195)))
      | ~ v3_funct_2(B_194,A_195,A_195)
      | ~ v1_funct_2(B_194,A_195,A_195)
      | ~ v1_funct_1(B_194) ) ),
    inference(resolution,[status(thm)],[c_60,c_2121])).

tff(c_2193,plain,(
    ! [A_198,B_199] :
      ( k1_partfun1('#skF_2','#skF_2',A_198,A_198,'#skF_3',k2_funct_2(A_198,B_199)) = k5_relat_1('#skF_3',k2_funct_2(A_198,B_199))
      | ~ v1_funct_1(k2_funct_2(A_198,B_199))
      | ~ m1_subset_1(B_199,k1_zfmisc_1(k2_zfmisc_1(A_198,A_198)))
      | ~ v3_funct_2(B_199,A_198,A_198)
      | ~ v1_funct_2(B_199,A_198,A_198)
      | ~ v1_funct_1(B_199) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_2143])).

tff(c_2216,plain,
    ( k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_2('#skF_2','#skF_3')) = k5_relat_1('#skF_3',k2_funct_2('#skF_2','#skF_3'))
    | ~ v1_funct_1(k2_funct_2('#skF_2','#skF_3'))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_2193])).

tff(c_2245,plain,(
    k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_1('#skF_3')) = k5_relat_1('#skF_3',k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_427,c_426,c_426,c_426,c_2216])).

tff(c_58,plain,
    ( ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_2('#skF_2','#skF_3'),'#skF_3'),k6_partfun1('#skF_2'))
    | ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_2('#skF_2','#skF_3')),k6_partfun1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_116,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_2('#skF_2','#skF_3')),k6_partfun1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_428,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_1('#skF_3')),k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_426,c_116])).

tff(c_2246,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k5_relat_1('#skF_3',k2_funct_1('#skF_3')),k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2245,c_428])).

tff(c_2253,plain,
    ( ~ r2_relset_1('#skF_2','#skF_2',k6_partfun1(k1_relat_1('#skF_3')),k6_partfun1('#skF_2'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_67,c_2246])).

tff(c_2256,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_66,c_311,c_387,c_349,c_2253])).

tff(c_2257,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_2('#skF_2','#skF_3'),'#skF_3'),k6_partfun1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_2617,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_1('#skF_3'),'#skF_3'),k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2615,c_2257])).

tff(c_3127,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k5_relat_1(k2_funct_1('#skF_3'),'#skF_3'),k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3105,c_2617])).

tff(c_3134,plain,
    ( ~ r2_relset_1('#skF_2','#skF_2',k6_partfun1(k2_relat_1('#skF_3')),k6_partfun1('#skF_2'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_3127])).

tff(c_3137,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_66,c_2471,c_2561,c_2388,c_3134])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:16:45 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.53/2.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.53/2.32  
% 6.53/2.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.53/2.33  %$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 6.53/2.33  
% 6.53/2.33  %Foreground sorts:
% 6.53/2.33  
% 6.53/2.33  
% 6.53/2.33  %Background operators:
% 6.53/2.33  
% 6.53/2.33  
% 6.53/2.33  %Foreground operators:
% 6.53/2.33  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.53/2.33  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 6.53/2.33  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 6.53/2.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.53/2.33  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 6.53/2.33  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 6.53/2.33  tff(k2_funct_2, type, k2_funct_2: ($i * $i) > $i).
% 6.53/2.33  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.53/2.33  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.53/2.33  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.53/2.33  tff('#skF_2', type, '#skF_2': $i).
% 6.53/2.33  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 6.53/2.33  tff('#skF_3', type, '#skF_3': $i).
% 6.53/2.33  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 6.53/2.33  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 6.53/2.33  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 6.53/2.33  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.53/2.33  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 6.53/2.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.53/2.33  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.53/2.33  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.53/2.33  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 6.53/2.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.53/2.33  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 6.53/2.33  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 6.53/2.33  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.53/2.33  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.53/2.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.53/2.33  
% 6.53/2.35  tff(f_151, negated_conjecture, ~(![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, k2_funct_2(A, B)), k6_partfun1(A)) & r2_relset_1(A, A, k1_partfun1(A, A, A, A, k2_funct_2(A, B), B), k6_partfun1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_funct_2)).
% 6.53/2.35  tff(f_39, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 6.53/2.35  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_funct_2)).
% 6.53/2.35  tff(f_95, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 6.53/2.35  tff(f_55, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 6.53/2.35  tff(f_45, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 6.53/2.35  tff(f_75, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 6.53/2.35  tff(f_130, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 6.53/2.35  tff(f_35, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 6.53/2.35  tff(f_128, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k2_funct_2(A, B) = k2_funct_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 6.53/2.35  tff(f_91, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (((v1_funct_1(k2_funct_2(A, B)) & v1_funct_2(k2_funct_2(A, B), A, A)) & v3_funct_2(k2_funct_2(A, B), A, A)) & m1_subset_1(k2_funct_2(A, B), k1_zfmisc_1(k2_zfmisc_1(A, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_2)).
% 6.53/2.35  tff(f_118, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 6.53/2.35  tff(f_108, axiom, (![A, B]: (?[C]: (((((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & v1_relat_1(C)) & v4_relat_1(C, A)) & v5_relat_1(C, B)) & v1_funct_1(C)) & v1_funct_2(C, A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc1_funct_2)).
% 6.53/2.35  tff(f_49, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 6.53/2.35  tff(f_138, axiom, (![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k1_relset_1(A, A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_funct_2)).
% 6.53/2.35  tff(c_60, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_151])).
% 6.53/2.35  tff(c_85, plain, (![C_50, A_51, B_52]: (v1_relat_1(C_50) | ~m1_subset_1(C_50, k1_zfmisc_1(k2_zfmisc_1(A_51, B_52))))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.53/2.35  tff(c_93, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_60, c_85])).
% 6.53/2.35  tff(c_66, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_151])).
% 6.53/2.35  tff(c_62, plain, (v3_funct_2('#skF_3', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_151])).
% 6.53/2.35  tff(c_2455, plain, (![C_238, A_239, B_240]: (v2_funct_1(C_238) | ~v3_funct_2(C_238, A_239, B_240) | ~v1_funct_1(C_238) | ~m1_subset_1(C_238, k1_zfmisc_1(k2_zfmisc_1(A_239, B_240))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 6.53/2.35  tff(c_2464, plain, (v2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_60, c_2455])).
% 6.53/2.35  tff(c_2471, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_62, c_2464])).
% 6.53/2.35  tff(c_36, plain, (![A_22]: (m1_subset_1(k6_partfun1(A_22), k1_zfmisc_1(k2_zfmisc_1(A_22, A_22))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 6.53/2.35  tff(c_2493, plain, (![A_250, B_251, C_252, D_253]: (r2_relset_1(A_250, B_251, C_252, C_252) | ~m1_subset_1(D_253, k1_zfmisc_1(k2_zfmisc_1(A_250, B_251))) | ~m1_subset_1(C_252, k1_zfmisc_1(k2_zfmisc_1(A_250, B_251))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.53/2.35  tff(c_2552, plain, (![A_258, C_259]: (r2_relset_1(A_258, A_258, C_259, C_259) | ~m1_subset_1(C_259, k1_zfmisc_1(k2_zfmisc_1(A_258, A_258))))), inference(resolution, [status(thm)], [c_36, c_2493])).
% 6.53/2.35  tff(c_2561, plain, (![A_22]: (r2_relset_1(A_22, A_22, k6_partfun1(A_22), k6_partfun1(A_22)))), inference(resolution, [status(thm)], [c_36, c_2552])).
% 6.53/2.35  tff(c_101, plain, (![C_56, B_57, A_58]: (v5_relat_1(C_56, B_57) | ~m1_subset_1(C_56, k1_zfmisc_1(k2_zfmisc_1(A_58, B_57))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.53/2.35  tff(c_114, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_60, c_101])).
% 6.53/2.35  tff(c_2275, plain, (![B_205, A_206]: (k2_relat_1(B_205)=A_206 | ~v2_funct_2(B_205, A_206) | ~v5_relat_1(B_205, A_206) | ~v1_relat_1(B_205))), inference(cnfTransformation, [status(thm)], [f_75])).
% 6.53/2.35  tff(c_2281, plain, (k2_relat_1('#skF_3')='#skF_2' | ~v2_funct_2('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_114, c_2275])).
% 6.53/2.35  tff(c_2290, plain, (k2_relat_1('#skF_3')='#skF_2' | ~v2_funct_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_93, c_2281])).
% 6.53/2.35  tff(c_2294, plain, (~v2_funct_2('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_2290])).
% 6.53/2.35  tff(c_2369, plain, (![C_224, B_225, A_226]: (v2_funct_2(C_224, B_225) | ~v3_funct_2(C_224, A_226, B_225) | ~v1_funct_1(C_224) | ~m1_subset_1(C_224, k1_zfmisc_1(k2_zfmisc_1(A_226, B_225))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 6.53/2.35  tff(c_2378, plain, (v2_funct_2('#skF_3', '#skF_2') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_60, c_2369])).
% 6.53/2.35  tff(c_2385, plain, (v2_funct_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_62, c_2378])).
% 6.53/2.35  tff(c_2387, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2294, c_2385])).
% 6.53/2.35  tff(c_2388, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(splitRight, [status(thm)], [c_2290])).
% 6.53/2.35  tff(c_54, plain, (![A_34]: (k6_relat_1(A_34)=k6_partfun1(A_34))), inference(cnfTransformation, [status(thm)], [f_130])).
% 6.53/2.35  tff(c_2, plain, (![A_1]: (k5_relat_1(k2_funct_1(A_1), A_1)=k6_relat_1(k2_relat_1(A_1)) | ~v2_funct_1(A_1) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.53/2.35  tff(c_68, plain, (![A_1]: (k5_relat_1(k2_funct_1(A_1), A_1)=k6_partfun1(k2_relat_1(A_1)) | ~v2_funct_1(A_1) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_2])).
% 6.53/2.35  tff(c_64, plain, (v1_funct_2('#skF_3', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_151])).
% 6.53/2.35  tff(c_2598, plain, (![A_267, B_268]: (k2_funct_2(A_267, B_268)=k2_funct_1(B_268) | ~m1_subset_1(B_268, k1_zfmisc_1(k2_zfmisc_1(A_267, A_267))) | ~v3_funct_2(B_268, A_267, A_267) | ~v1_funct_2(B_268, A_267, A_267) | ~v1_funct_1(B_268))), inference(cnfTransformation, [status(thm)], [f_128])).
% 6.53/2.35  tff(c_2608, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_60, c_2598])).
% 6.53/2.35  tff(c_2615, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_2608])).
% 6.53/2.35  tff(c_2566, plain, (![A_261, B_262]: (v1_funct_1(k2_funct_2(A_261, B_262)) | ~m1_subset_1(B_262, k1_zfmisc_1(k2_zfmisc_1(A_261, A_261))) | ~v3_funct_2(B_262, A_261, A_261) | ~v1_funct_2(B_262, A_261, A_261) | ~v1_funct_1(B_262))), inference(cnfTransformation, [status(thm)], [f_91])).
% 6.53/2.35  tff(c_2576, plain, (v1_funct_1(k2_funct_2('#skF_2', '#skF_3')) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_60, c_2566])).
% 6.53/2.35  tff(c_2583, plain, (v1_funct_1(k2_funct_2('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_2576])).
% 6.53/2.35  tff(c_2616, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2615, c_2583])).
% 6.53/2.35  tff(c_26, plain, (![A_20, B_21]: (m1_subset_1(k2_funct_2(A_20, B_21), k1_zfmisc_1(k2_zfmisc_1(A_20, A_20))) | ~m1_subset_1(B_21, k1_zfmisc_1(k2_zfmisc_1(A_20, A_20))) | ~v3_funct_2(B_21, A_20, A_20) | ~v1_funct_2(B_21, A_20, A_20) | ~v1_funct_1(B_21))), inference(cnfTransformation, [status(thm)], [f_91])).
% 6.53/2.35  tff(c_2790, plain, (![A_285, F_286, D_283, E_288, C_287, B_284]: (k1_partfun1(A_285, B_284, C_287, D_283, E_288, F_286)=k5_relat_1(E_288, F_286) | ~m1_subset_1(F_286, k1_zfmisc_1(k2_zfmisc_1(C_287, D_283))) | ~v1_funct_1(F_286) | ~m1_subset_1(E_288, k1_zfmisc_1(k2_zfmisc_1(A_285, B_284))) | ~v1_funct_1(E_288))), inference(cnfTransformation, [status(thm)], [f_118])).
% 6.53/2.35  tff(c_2800, plain, (![A_285, B_284, E_288]: (k1_partfun1(A_285, B_284, '#skF_2', '#skF_2', E_288, '#skF_3')=k5_relat_1(E_288, '#skF_3') | ~v1_funct_1('#skF_3') | ~m1_subset_1(E_288, k1_zfmisc_1(k2_zfmisc_1(A_285, B_284))) | ~v1_funct_1(E_288))), inference(resolution, [status(thm)], [c_60, c_2790])).
% 6.53/2.35  tff(c_2823, plain, (![A_289, B_290, E_291]: (k1_partfun1(A_289, B_290, '#skF_2', '#skF_2', E_291, '#skF_3')=k5_relat_1(E_291, '#skF_3') | ~m1_subset_1(E_291, k1_zfmisc_1(k2_zfmisc_1(A_289, B_290))) | ~v1_funct_1(E_291))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_2800])).
% 6.53/2.35  tff(c_3073, plain, (![A_297, B_298]: (k1_partfun1(A_297, A_297, '#skF_2', '#skF_2', k2_funct_2(A_297, B_298), '#skF_3')=k5_relat_1(k2_funct_2(A_297, B_298), '#skF_3') | ~v1_funct_1(k2_funct_2(A_297, B_298)) | ~m1_subset_1(B_298, k1_zfmisc_1(k2_zfmisc_1(A_297, A_297))) | ~v3_funct_2(B_298, A_297, A_297) | ~v1_funct_2(B_298, A_297, A_297) | ~v1_funct_1(B_298))), inference(resolution, [status(thm)], [c_26, c_2823])).
% 6.53/2.35  tff(c_3088, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_2('#skF_2', '#skF_3'), '#skF_3')=k5_relat_1(k2_funct_2('#skF_2', '#skF_3'), '#skF_3') | ~v1_funct_1(k2_funct_2('#skF_2', '#skF_3')) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_60, c_3073])).
% 6.53/2.35  tff(c_3105, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_1('#skF_3'), '#skF_3')=k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_2616, c_2615, c_2615, c_2615, c_3088])).
% 6.53/2.35  tff(c_295, plain, (![C_94, A_95, B_96]: (v2_funct_1(C_94) | ~v3_funct_2(C_94, A_95, B_96) | ~v1_funct_1(C_94) | ~m1_subset_1(C_94, k1_zfmisc_1(k2_zfmisc_1(A_95, B_96))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 6.53/2.35  tff(c_304, plain, (v2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_60, c_295])).
% 6.53/2.35  tff(c_311, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_62, c_304])).
% 6.53/2.35  tff(c_48, plain, (![A_23, B_24]: (m1_subset_1('#skF_1'(A_23, B_24), k1_zfmisc_1(k2_zfmisc_1(A_23, B_24))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 6.53/2.35  tff(c_368, plain, (![A_106, B_107, C_108, D_109]: (r2_relset_1(A_106, B_107, C_108, C_108) | ~m1_subset_1(D_109, k1_zfmisc_1(k2_zfmisc_1(A_106, B_107))) | ~m1_subset_1(C_108, k1_zfmisc_1(k2_zfmisc_1(A_106, B_107))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.53/2.35  tff(c_379, plain, (![A_112, B_113, C_114]: (r2_relset_1(A_112, B_113, C_114, C_114) | ~m1_subset_1(C_114, k1_zfmisc_1(k2_zfmisc_1(A_112, B_113))))), inference(resolution, [status(thm)], [c_48, c_368])).
% 6.53/2.35  tff(c_387, plain, (![A_22]: (r2_relset_1(A_22, A_22, k6_partfun1(A_22), k6_partfun1(A_22)))), inference(resolution, [status(thm)], [c_36, c_379])).
% 6.53/2.35  tff(c_152, plain, (![A_67, B_68, C_69]: (k1_relset_1(A_67, B_68, C_69)=k1_relat_1(C_69) | ~m1_subset_1(C_69, k1_zfmisc_1(k2_zfmisc_1(A_67, B_68))))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.53/2.35  tff(c_164, plain, (k1_relset_1('#skF_2', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_60, c_152])).
% 6.53/2.35  tff(c_331, plain, (![A_103, B_104]: (k1_relset_1(A_103, A_103, B_104)=A_103 | ~m1_subset_1(B_104, k1_zfmisc_1(k2_zfmisc_1(A_103, A_103))) | ~v1_funct_2(B_104, A_103, A_103) | ~v1_funct_1(B_104))), inference(cnfTransformation, [status(thm)], [f_138])).
% 6.53/2.35  tff(c_341, plain, (k1_relset_1('#skF_2', '#skF_2', '#skF_3')='#skF_2' | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_60, c_331])).
% 6.53/2.35  tff(c_349, plain, (k1_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_164, c_341])).
% 6.53/2.35  tff(c_4, plain, (![A_1]: (k5_relat_1(A_1, k2_funct_1(A_1))=k6_relat_1(k1_relat_1(A_1)) | ~v2_funct_1(A_1) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.53/2.35  tff(c_67, plain, (![A_1]: (k5_relat_1(A_1, k2_funct_1(A_1))=k6_partfun1(k1_relat_1(A_1)) | ~v2_funct_1(A_1) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_4])).
% 6.53/2.35  tff(c_409, plain, (![A_120, B_121]: (k2_funct_2(A_120, B_121)=k2_funct_1(B_121) | ~m1_subset_1(B_121, k1_zfmisc_1(k2_zfmisc_1(A_120, A_120))) | ~v3_funct_2(B_121, A_120, A_120) | ~v1_funct_2(B_121, A_120, A_120) | ~v1_funct_1(B_121))), inference(cnfTransformation, [status(thm)], [f_128])).
% 6.53/2.35  tff(c_419, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_60, c_409])).
% 6.53/2.35  tff(c_426, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_419])).
% 6.53/2.35  tff(c_391, plain, (![A_118, B_119]: (v1_funct_1(k2_funct_2(A_118, B_119)) | ~m1_subset_1(B_119, k1_zfmisc_1(k2_zfmisc_1(A_118, A_118))) | ~v3_funct_2(B_119, A_118, A_118) | ~v1_funct_2(B_119, A_118, A_118) | ~v1_funct_1(B_119))), inference(cnfTransformation, [status(thm)], [f_91])).
% 6.53/2.35  tff(c_401, plain, (v1_funct_1(k2_funct_2('#skF_2', '#skF_3')) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_60, c_391])).
% 6.53/2.35  tff(c_408, plain, (v1_funct_1(k2_funct_2('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_401])).
% 6.53/2.35  tff(c_427, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_426, c_408])).
% 6.53/2.35  tff(c_591, plain, (![B_137, C_140, A_138, F_139, D_136, E_141]: (k1_partfun1(A_138, B_137, C_140, D_136, E_141, F_139)=k5_relat_1(E_141, F_139) | ~m1_subset_1(F_139, k1_zfmisc_1(k2_zfmisc_1(C_140, D_136))) | ~v1_funct_1(F_139) | ~m1_subset_1(E_141, k1_zfmisc_1(k2_zfmisc_1(A_138, B_137))) | ~v1_funct_1(E_141))), inference(cnfTransformation, [status(thm)], [f_118])).
% 6.53/2.35  tff(c_2121, plain, (![A_195, B_194, A_193, B_197, E_196]: (k1_partfun1(A_193, B_197, A_195, A_195, E_196, k2_funct_2(A_195, B_194))=k5_relat_1(E_196, k2_funct_2(A_195, B_194)) | ~v1_funct_1(k2_funct_2(A_195, B_194)) | ~m1_subset_1(E_196, k1_zfmisc_1(k2_zfmisc_1(A_193, B_197))) | ~v1_funct_1(E_196) | ~m1_subset_1(B_194, k1_zfmisc_1(k2_zfmisc_1(A_195, A_195))) | ~v3_funct_2(B_194, A_195, A_195) | ~v1_funct_2(B_194, A_195, A_195) | ~v1_funct_1(B_194))), inference(resolution, [status(thm)], [c_26, c_591])).
% 6.53/2.35  tff(c_2143, plain, (![A_195, B_194]: (k1_partfun1('#skF_2', '#skF_2', A_195, A_195, '#skF_3', k2_funct_2(A_195, B_194))=k5_relat_1('#skF_3', k2_funct_2(A_195, B_194)) | ~v1_funct_1(k2_funct_2(A_195, B_194)) | ~v1_funct_1('#skF_3') | ~m1_subset_1(B_194, k1_zfmisc_1(k2_zfmisc_1(A_195, A_195))) | ~v3_funct_2(B_194, A_195, A_195) | ~v1_funct_2(B_194, A_195, A_195) | ~v1_funct_1(B_194))), inference(resolution, [status(thm)], [c_60, c_2121])).
% 6.53/2.35  tff(c_2193, plain, (![A_198, B_199]: (k1_partfun1('#skF_2', '#skF_2', A_198, A_198, '#skF_3', k2_funct_2(A_198, B_199))=k5_relat_1('#skF_3', k2_funct_2(A_198, B_199)) | ~v1_funct_1(k2_funct_2(A_198, B_199)) | ~m1_subset_1(B_199, k1_zfmisc_1(k2_zfmisc_1(A_198, A_198))) | ~v3_funct_2(B_199, A_198, A_198) | ~v1_funct_2(B_199, A_198, A_198) | ~v1_funct_1(B_199))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_2143])).
% 6.53/2.35  tff(c_2216, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_2('#skF_2', '#skF_3'))=k5_relat_1('#skF_3', k2_funct_2('#skF_2', '#skF_3')) | ~v1_funct_1(k2_funct_2('#skF_2', '#skF_3')) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_60, c_2193])).
% 6.53/2.35  tff(c_2245, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_1('#skF_3'))=k5_relat_1('#skF_3', k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_427, c_426, c_426, c_426, c_2216])).
% 6.53/2.35  tff(c_58, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_2('#skF_2', '#skF_3'), '#skF_3'), k6_partfun1('#skF_2')) | ~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_2('#skF_2', '#skF_3')), k6_partfun1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_151])).
% 6.53/2.35  tff(c_116, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_2('#skF_2', '#skF_3')), k6_partfun1('#skF_2'))), inference(splitLeft, [status(thm)], [c_58])).
% 6.53/2.35  tff(c_428, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_1('#skF_3')), k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_426, c_116])).
% 6.53/2.35  tff(c_2246, plain, (~r2_relset_1('#skF_2', '#skF_2', k5_relat_1('#skF_3', k2_funct_1('#skF_3')), k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2245, c_428])).
% 6.53/2.35  tff(c_2253, plain, (~r2_relset_1('#skF_2', '#skF_2', k6_partfun1(k1_relat_1('#skF_3')), k6_partfun1('#skF_2')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_67, c_2246])).
% 6.53/2.35  tff(c_2256, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_93, c_66, c_311, c_387, c_349, c_2253])).
% 6.53/2.35  tff(c_2257, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_2('#skF_2', '#skF_3'), '#skF_3'), k6_partfun1('#skF_2'))), inference(splitRight, [status(thm)], [c_58])).
% 6.53/2.35  tff(c_2617, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_1('#skF_3'), '#skF_3'), k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2615, c_2257])).
% 6.53/2.35  tff(c_3127, plain, (~r2_relset_1('#skF_2', '#skF_2', k5_relat_1(k2_funct_1('#skF_3'), '#skF_3'), k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_3105, c_2617])).
% 6.53/2.35  tff(c_3134, plain, (~r2_relset_1('#skF_2', '#skF_2', k6_partfun1(k2_relat_1('#skF_3')), k6_partfun1('#skF_2')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_68, c_3127])).
% 6.53/2.35  tff(c_3137, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_93, c_66, c_2471, c_2561, c_2388, c_3134])).
% 6.53/2.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.53/2.35  
% 6.53/2.35  Inference rules
% 6.53/2.35  ----------------------
% 6.53/2.35  #Ref     : 0
% 6.53/2.35  #Sup     : 656
% 6.53/2.35  #Fact    : 0
% 6.53/2.35  #Define  : 0
% 6.53/2.35  #Split   : 3
% 6.53/2.35  #Chain   : 0
% 6.53/2.35  #Close   : 0
% 6.53/2.35  
% 6.53/2.35  Ordering : KBO
% 6.53/2.35  
% 6.53/2.35  Simplification rules
% 6.53/2.35  ----------------------
% 6.53/2.35  #Subsume      : 6
% 6.53/2.35  #Demod        : 1479
% 6.53/2.35  #Tautology    : 259
% 6.53/2.35  #SimpNegUnit  : 2
% 6.53/2.35  #BackRed      : 48
% 6.53/2.35  
% 6.53/2.35  #Partial instantiations: 0
% 6.53/2.35  #Strategies tried      : 1
% 6.53/2.35  
% 6.53/2.35  Timing (in seconds)
% 6.53/2.35  ----------------------
% 6.53/2.35  Preprocessing        : 0.38
% 6.53/2.35  Parsing              : 0.21
% 6.53/2.35  CNF conversion       : 0.02
% 6.53/2.35  Main loop            : 1.17
% 6.53/2.35  Inferencing          : 0.38
% 6.53/2.35  Reduction            : 0.47
% 6.53/2.35  Demodulation         : 0.36
% 6.53/2.35  BG Simplification    : 0.04
% 6.53/2.35  Subsumption          : 0.19
% 6.53/2.36  Abstraction          : 0.05
% 6.53/2.36  MUC search           : 0.00
% 6.53/2.36  Cooper               : 0.00
% 6.53/2.36  Total                : 1.60
% 6.53/2.36  Index Insertion      : 0.00
% 6.53/2.36  Index Deletion       : 0.00
% 6.53/2.36  Index Matching       : 0.00
% 6.53/2.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
