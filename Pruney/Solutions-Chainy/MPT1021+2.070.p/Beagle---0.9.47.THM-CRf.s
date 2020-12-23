%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:11 EST 2020

% Result     : Theorem 5.59s
% Output     : CNFRefutation 5.72s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 358 expanded)
%              Number of leaves         :   44 ( 154 expanded)
%              Depth                    :    9
%              Number of atoms          :  276 (1089 expanded)
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

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_154,negated_conjecture,(
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

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_100,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_111,axiom,(
    ! [A,B] :
    ? [C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
      & v1_relat_1(C)
      & v4_relat_1(C,A)
      & v5_relat_1(C,B)
      & v1_funct_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_partfun1)).

tff(f_60,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_133,axiom,(
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

tff(f_131,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k2_funct_2(A,B) = k2_funct_1(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

tff(f_96,axiom,(
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

tff(f_121,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_141,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k1_relset_1(A,A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_2)).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_60,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_86,plain,(
    ! [B_54,A_55] :
      ( v1_relat_1(B_54)
      | ~ m1_subset_1(B_54,k1_zfmisc_1(A_55))
      | ~ v1_relat_1(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_95,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_2')) ),
    inference(resolution,[status(thm)],[c_60,c_86])).

tff(c_104,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_95])).

tff(c_66,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_62,plain,(
    v3_funct_2('#skF_3','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_2478,plain,(
    ! [C_236,A_237,B_238] :
      ( v2_funct_1(C_236)
      | ~ v3_funct_2(C_236,A_237,B_238)
      | ~ v1_funct_1(C_236)
      | ~ m1_subset_1(C_236,k1_zfmisc_1(k2_zfmisc_1(A_237,B_238))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_2487,plain,
    ( v2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_2478])).

tff(c_2494,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_62,c_2487])).

tff(c_38,plain,(
    ! [A_24] : m1_subset_1(k6_partfun1(A_24),k1_zfmisc_1(k2_zfmisc_1(A_24,A_24))) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_48,plain,(
    ! [A_25,B_26] : m1_subset_1('#skF_1'(A_25,B_26),k1_zfmisc_1(k2_zfmisc_1(A_25,B_26))) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_2535,plain,(
    ! [A_250,B_251,C_252,D_253] :
      ( r2_relset_1(A_250,B_251,C_252,C_252)
      | ~ m1_subset_1(D_253,k1_zfmisc_1(k2_zfmisc_1(A_250,B_251)))
      | ~ m1_subset_1(C_252,k1_zfmisc_1(k2_zfmisc_1(A_250,B_251))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_2554,plain,(
    ! [A_254,B_255,C_256] :
      ( r2_relset_1(A_254,B_255,C_256,C_256)
      | ~ m1_subset_1(C_256,k1_zfmisc_1(k2_zfmisc_1(A_254,B_255))) ) ),
    inference(resolution,[status(thm)],[c_48,c_2535])).

tff(c_2562,plain,(
    ! [A_24] : r2_relset_1(A_24,A_24,k6_partfun1(A_24),k6_partfun1(A_24)) ),
    inference(resolution,[status(thm)],[c_38,c_2554])).

tff(c_105,plain,(
    ! [C_56,B_57,A_58] :
      ( v5_relat_1(C_56,B_57)
      | ~ m1_subset_1(C_56,k1_zfmisc_1(k2_zfmisc_1(A_58,B_57))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_118,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_105])).

tff(c_2298,plain,(
    ! [B_203,A_204] :
      ( k2_relat_1(B_203) = A_204
      | ~ v2_funct_2(B_203,A_204)
      | ~ v5_relat_1(B_203,A_204)
      | ~ v1_relat_1(B_203) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_2304,plain,
    ( k2_relat_1('#skF_3') = '#skF_2'
    | ~ v2_funct_2('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_118,c_2298])).

tff(c_2313,plain,
    ( k2_relat_1('#skF_3') = '#skF_2'
    | ~ v2_funct_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_2304])).

tff(c_2317,plain,(
    ~ v2_funct_2('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_2313])).

tff(c_2392,plain,(
    ! [C_222,B_223,A_224] :
      ( v2_funct_2(C_222,B_223)
      | ~ v3_funct_2(C_222,A_224,B_223)
      | ~ v1_funct_1(C_222)
      | ~ m1_subset_1(C_222,k1_zfmisc_1(k2_zfmisc_1(A_224,B_223))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_2401,plain,
    ( v2_funct_2('#skF_3','#skF_2')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_2392])).

tff(c_2408,plain,(
    v2_funct_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_62,c_2401])).

tff(c_2410,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2317,c_2408])).

tff(c_2411,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_2313])).

tff(c_54,plain,(
    ! [A_36] : k6_relat_1(A_36) = k6_partfun1(A_36) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_6,plain,(
    ! [A_6] :
      ( k5_relat_1(k2_funct_1(A_6),A_6) = k6_relat_1(k2_relat_1(A_6))
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_68,plain,(
    ! [A_6] :
      ( k5_relat_1(k2_funct_1(A_6),A_6) = k6_partfun1(k2_relat_1(A_6))
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_6])).

tff(c_64,plain,(
    v1_funct_2('#skF_3','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_2587,plain,(
    ! [A_265,B_266] :
      ( k2_funct_2(A_265,B_266) = k2_funct_1(B_266)
      | ~ m1_subset_1(B_266,k1_zfmisc_1(k2_zfmisc_1(A_265,A_265)))
      | ~ v3_funct_2(B_266,A_265,A_265)
      | ~ v1_funct_2(B_266,A_265,A_265)
      | ~ v1_funct_1(B_266) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_2597,plain,
    ( k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_2587])).

tff(c_2604,plain,(
    k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_2597])).

tff(c_2567,plain,(
    ! [A_261,B_262] :
      ( v1_funct_1(k2_funct_2(A_261,B_262))
      | ~ m1_subset_1(B_262,k1_zfmisc_1(k2_zfmisc_1(A_261,A_261)))
      | ~ v3_funct_2(B_262,A_261,A_261)
      | ~ v1_funct_2(B_262,A_261,A_261)
      | ~ v1_funct_1(B_262) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_2577,plain,
    ( v1_funct_1(k2_funct_2('#skF_2','#skF_3'))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_2567])).

tff(c_2584,plain,(
    v1_funct_1(k2_funct_2('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_2577])).

tff(c_2605,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2604,c_2584])).

tff(c_28,plain,(
    ! [A_22,B_23] :
      ( m1_subset_1(k2_funct_2(A_22,B_23),k1_zfmisc_1(k2_zfmisc_1(A_22,A_22)))
      | ~ m1_subset_1(B_23,k1_zfmisc_1(k2_zfmisc_1(A_22,A_22)))
      | ~ v3_funct_2(B_23,A_22,A_22)
      | ~ v1_funct_2(B_23,A_22,A_22)
      | ~ v1_funct_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_2773,plain,(
    ! [D_285,A_282,E_281,F_280,C_283,B_284] :
      ( k1_partfun1(A_282,B_284,C_283,D_285,E_281,F_280) = k5_relat_1(E_281,F_280)
      | ~ m1_subset_1(F_280,k1_zfmisc_1(k2_zfmisc_1(C_283,D_285)))
      | ~ v1_funct_1(F_280)
      | ~ m1_subset_1(E_281,k1_zfmisc_1(k2_zfmisc_1(A_282,B_284)))
      | ~ v1_funct_1(E_281) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_2783,plain,(
    ! [A_282,B_284,E_281] :
      ( k1_partfun1(A_282,B_284,'#skF_2','#skF_2',E_281,'#skF_3') = k5_relat_1(E_281,'#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(E_281,k1_zfmisc_1(k2_zfmisc_1(A_282,B_284)))
      | ~ v1_funct_1(E_281) ) ),
    inference(resolution,[status(thm)],[c_60,c_2773])).

tff(c_2806,plain,(
    ! [A_286,B_287,E_288] :
      ( k1_partfun1(A_286,B_287,'#skF_2','#skF_2',E_288,'#skF_3') = k5_relat_1(E_288,'#skF_3')
      | ~ m1_subset_1(E_288,k1_zfmisc_1(k2_zfmisc_1(A_286,B_287)))
      | ~ v1_funct_1(E_288) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_2783])).

tff(c_3074,plain,(
    ! [A_296,B_297] :
      ( k1_partfun1(A_296,A_296,'#skF_2','#skF_2',k2_funct_2(A_296,B_297),'#skF_3') = k5_relat_1(k2_funct_2(A_296,B_297),'#skF_3')
      | ~ v1_funct_1(k2_funct_2(A_296,B_297))
      | ~ m1_subset_1(B_297,k1_zfmisc_1(k2_zfmisc_1(A_296,A_296)))
      | ~ v3_funct_2(B_297,A_296,A_296)
      | ~ v1_funct_2(B_297,A_296,A_296)
      | ~ v1_funct_1(B_297) ) ),
    inference(resolution,[status(thm)],[c_28,c_2806])).

tff(c_3087,plain,
    ( k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_2('#skF_2','#skF_3'),'#skF_3') = k5_relat_1(k2_funct_2('#skF_2','#skF_3'),'#skF_3')
    | ~ v1_funct_1(k2_funct_2('#skF_2','#skF_3'))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_3074])).

tff(c_3101,plain,(
    k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_1('#skF_3'),'#skF_3') = k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_2605,c_2604,c_2604,c_2604,c_3087])).

tff(c_300,plain,(
    ! [C_95,A_96,B_97] :
      ( v2_funct_1(C_95)
      | ~ v3_funct_2(C_95,A_96,B_97)
      | ~ v1_funct_1(C_95)
      | ~ m1_subset_1(C_95,k1_zfmisc_1(k2_zfmisc_1(A_96,B_97))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_309,plain,
    ( v2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_300])).

tff(c_316,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_62,c_309])).

tff(c_336,plain,(
    ! [A_104,B_105,C_106,D_107] :
      ( r2_relset_1(A_104,B_105,C_106,C_106)
      | ~ m1_subset_1(D_107,k1_zfmisc_1(k2_zfmisc_1(A_104,B_105)))
      | ~ m1_subset_1(C_106,k1_zfmisc_1(k2_zfmisc_1(A_104,B_105))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_347,plain,(
    ! [A_110,B_111,C_112] :
      ( r2_relset_1(A_110,B_111,C_112,C_112)
      | ~ m1_subset_1(C_112,k1_zfmisc_1(k2_zfmisc_1(A_110,B_111))) ) ),
    inference(resolution,[status(thm)],[c_48,c_336])).

tff(c_355,plain,(
    ! [A_24] : r2_relset_1(A_24,A_24,k6_partfun1(A_24),k6_partfun1(A_24)) ),
    inference(resolution,[status(thm)],[c_38,c_347])).

tff(c_157,plain,(
    ! [A_68,B_69,C_70] :
      ( k1_relset_1(A_68,B_69,C_70) = k1_relat_1(C_70)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_169,plain,(
    k1_relset_1('#skF_2','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_157])).

tff(c_360,plain,(
    ! [A_117,B_118] :
      ( k1_relset_1(A_117,A_117,B_118) = A_117
      | ~ m1_subset_1(B_118,k1_zfmisc_1(k2_zfmisc_1(A_117,A_117)))
      | ~ v1_funct_2(B_118,A_117,A_117)
      | ~ v1_funct_1(B_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_370,plain,
    ( k1_relset_1('#skF_2','#skF_2','#skF_3') = '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_360])).

tff(c_378,plain,(
    k1_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_169,c_370])).

tff(c_8,plain,(
    ! [A_6] :
      ( k5_relat_1(A_6,k2_funct_1(A_6)) = k6_relat_1(k1_relat_1(A_6))
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_67,plain,(
    ! [A_6] :
      ( k5_relat_1(A_6,k2_funct_1(A_6)) = k6_partfun1(k1_relat_1(A_6))
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_8])).

tff(c_406,plain,(
    ! [A_121,B_122] :
      ( k2_funct_2(A_121,B_122) = k2_funct_1(B_122)
      | ~ m1_subset_1(B_122,k1_zfmisc_1(k2_zfmisc_1(A_121,A_121)))
      | ~ v3_funct_2(B_122,A_121,A_121)
      | ~ v1_funct_2(B_122,A_121,A_121)
      | ~ v1_funct_1(B_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_416,plain,
    ( k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_406])).

tff(c_423,plain,(
    k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_416])).

tff(c_379,plain,(
    ! [A_119,B_120] :
      ( v1_funct_1(k2_funct_2(A_119,B_120))
      | ~ m1_subset_1(B_120,k1_zfmisc_1(k2_zfmisc_1(A_119,A_119)))
      | ~ v3_funct_2(B_120,A_119,A_119)
      | ~ v1_funct_2(B_120,A_119,A_119)
      | ~ v1_funct_1(B_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_389,plain,
    ( v1_funct_1(k2_funct_2('#skF_2','#skF_3'))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_379])).

tff(c_396,plain,(
    v1_funct_1(k2_funct_2('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_389])).

tff(c_424,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_423,c_396])).

tff(c_592,plain,(
    ! [E_138,C_140,D_142,A_139,B_141,F_137] :
      ( k1_partfun1(A_139,B_141,C_140,D_142,E_138,F_137) = k5_relat_1(E_138,F_137)
      | ~ m1_subset_1(F_137,k1_zfmisc_1(k2_zfmisc_1(C_140,D_142)))
      | ~ v1_funct_1(F_137)
      | ~ m1_subset_1(E_138,k1_zfmisc_1(k2_zfmisc_1(A_139,B_141)))
      | ~ v1_funct_1(E_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_2155,plain,(
    ! [A_191,B_194,E_193,A_192,B_195] :
      ( k1_partfun1(A_192,B_195,A_191,A_191,E_193,k2_funct_2(A_191,B_194)) = k5_relat_1(E_193,k2_funct_2(A_191,B_194))
      | ~ v1_funct_1(k2_funct_2(A_191,B_194))
      | ~ m1_subset_1(E_193,k1_zfmisc_1(k2_zfmisc_1(A_192,B_195)))
      | ~ v1_funct_1(E_193)
      | ~ m1_subset_1(B_194,k1_zfmisc_1(k2_zfmisc_1(A_191,A_191)))
      | ~ v3_funct_2(B_194,A_191,A_191)
      | ~ v1_funct_2(B_194,A_191,A_191)
      | ~ v1_funct_1(B_194) ) ),
    inference(resolution,[status(thm)],[c_28,c_592])).

tff(c_2177,plain,(
    ! [A_191,B_194] :
      ( k1_partfun1('#skF_2','#skF_2',A_191,A_191,'#skF_3',k2_funct_2(A_191,B_194)) = k5_relat_1('#skF_3',k2_funct_2(A_191,B_194))
      | ~ v1_funct_1(k2_funct_2(A_191,B_194))
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(B_194,k1_zfmisc_1(k2_zfmisc_1(A_191,A_191)))
      | ~ v3_funct_2(B_194,A_191,A_191)
      | ~ v1_funct_2(B_194,A_191,A_191)
      | ~ v1_funct_1(B_194) ) ),
    inference(resolution,[status(thm)],[c_60,c_2155])).

tff(c_2216,plain,(
    ! [A_196,B_197] :
      ( k1_partfun1('#skF_2','#skF_2',A_196,A_196,'#skF_3',k2_funct_2(A_196,B_197)) = k5_relat_1('#skF_3',k2_funct_2(A_196,B_197))
      | ~ v1_funct_1(k2_funct_2(A_196,B_197))
      | ~ m1_subset_1(B_197,k1_zfmisc_1(k2_zfmisc_1(A_196,A_196)))
      | ~ v3_funct_2(B_197,A_196,A_196)
      | ~ v1_funct_2(B_197,A_196,A_196)
      | ~ v1_funct_1(B_197) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_2177])).

tff(c_2239,plain,
    ( k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_2('#skF_2','#skF_3')) = k5_relat_1('#skF_3',k2_funct_2('#skF_2','#skF_3'))
    | ~ v1_funct_1(k2_funct_2('#skF_2','#skF_3'))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_2216])).

tff(c_2268,plain,(
    k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_1('#skF_3')) = k5_relat_1('#skF_3',k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_424,c_423,c_423,c_423,c_2239])).

tff(c_58,plain,
    ( ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_2('#skF_2','#skF_3'),'#skF_3'),k6_partfun1('#skF_2'))
    | ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_2('#skF_2','#skF_3')),k6_partfun1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_121,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_2('#skF_2','#skF_3')),k6_partfun1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_425,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_1('#skF_3')),k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_423,c_121])).

tff(c_2269,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k5_relat_1('#skF_3',k2_funct_1('#skF_3')),k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2268,c_425])).

tff(c_2276,plain,
    ( ~ r2_relset_1('#skF_2','#skF_2',k6_partfun1(k1_relat_1('#skF_3')),k6_partfun1('#skF_2'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_67,c_2269])).

tff(c_2279,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_66,c_316,c_355,c_378,c_2276])).

tff(c_2280,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_2('#skF_2','#skF_3'),'#skF_3'),k6_partfun1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_2606,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_1('#skF_3'),'#skF_3'),k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2604,c_2280])).

tff(c_3241,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k5_relat_1(k2_funct_1('#skF_3'),'#skF_3'),k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3101,c_2606])).

tff(c_3248,plain,
    ( ~ r2_relset_1('#skF_2','#skF_2',k6_partfun1(k2_relat_1('#skF_3')),k6_partfun1('#skF_2'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_3241])).

tff(c_3251,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_66,c_2494,c_2562,c_2411,c_3248])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:57:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.59/2.09  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.59/2.10  
% 5.59/2.10  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.59/2.10  %$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 5.59/2.10  
% 5.59/2.10  %Foreground sorts:
% 5.59/2.10  
% 5.59/2.10  
% 5.59/2.10  %Background operators:
% 5.59/2.10  
% 5.59/2.10  
% 5.59/2.10  %Foreground operators:
% 5.59/2.10  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.59/2.10  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 5.59/2.10  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.59/2.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.59/2.10  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 5.59/2.10  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 5.59/2.10  tff(k2_funct_2, type, k2_funct_2: ($i * $i) > $i).
% 5.59/2.10  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.59/2.10  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.59/2.10  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.59/2.10  tff('#skF_2', type, '#skF_2': $i).
% 5.59/2.10  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 5.59/2.10  tff('#skF_3', type, '#skF_3': $i).
% 5.59/2.10  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 5.59/2.10  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.59/2.10  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.59/2.10  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.59/2.10  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 5.59/2.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.59/2.10  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.59/2.10  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.59/2.10  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 5.59/2.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.59/2.10  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.59/2.10  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 5.59/2.10  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.59/2.10  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.59/2.10  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.59/2.10  
% 5.72/2.13  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 5.72/2.13  tff(f_154, negated_conjecture, ~(![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, k2_funct_2(A, B)), k6_partfun1(A)) & r2_relset_1(A, A, k1_partfun1(A, A, A, A, k2_funct_2(A, B), B), k6_partfun1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_funct_2)).
% 5.72/2.13  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 5.72/2.13  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_funct_2)).
% 5.72/2.13  tff(f_100, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 5.72/2.13  tff(f_111, axiom, (![A, B]: (?[C]: ((((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & v1_relat_1(C)) & v4_relat_1(C, A)) & v5_relat_1(C, B)) & v1_funct_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc1_partfun1)).
% 5.72/2.13  tff(f_60, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 5.72/2.13  tff(f_50, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.72/2.13  tff(f_80, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 5.72/2.13  tff(f_133, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 5.72/2.13  tff(f_44, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 5.72/2.13  tff(f_131, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k2_funct_2(A, B) = k2_funct_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 5.72/2.13  tff(f_96, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (((v1_funct_1(k2_funct_2(A, B)) & v1_funct_2(k2_funct_2(A, B), A, A)) & v3_funct_2(k2_funct_2(A, B), A, A)) & m1_subset_1(k2_funct_2(A, B), k1_zfmisc_1(k2_zfmisc_1(A, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_2)).
% 5.72/2.13  tff(f_121, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 5.72/2.13  tff(f_54, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.72/2.13  tff(f_141, axiom, (![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k1_relset_1(A, A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_funct_2)).
% 5.72/2.13  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.72/2.13  tff(c_60, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_154])).
% 5.72/2.13  tff(c_86, plain, (![B_54, A_55]: (v1_relat_1(B_54) | ~m1_subset_1(B_54, k1_zfmisc_1(A_55)) | ~v1_relat_1(A_55))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.72/2.13  tff(c_95, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_2'))), inference(resolution, [status(thm)], [c_60, c_86])).
% 5.72/2.13  tff(c_104, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_95])).
% 5.72/2.13  tff(c_66, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_154])).
% 5.72/2.13  tff(c_62, plain, (v3_funct_2('#skF_3', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_154])).
% 5.72/2.13  tff(c_2478, plain, (![C_236, A_237, B_238]: (v2_funct_1(C_236) | ~v3_funct_2(C_236, A_237, B_238) | ~v1_funct_1(C_236) | ~m1_subset_1(C_236, k1_zfmisc_1(k2_zfmisc_1(A_237, B_238))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.72/2.13  tff(c_2487, plain, (v2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_60, c_2478])).
% 5.72/2.13  tff(c_2494, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_62, c_2487])).
% 5.72/2.13  tff(c_38, plain, (![A_24]: (m1_subset_1(k6_partfun1(A_24), k1_zfmisc_1(k2_zfmisc_1(A_24, A_24))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 5.72/2.13  tff(c_48, plain, (![A_25, B_26]: (m1_subset_1('#skF_1'(A_25, B_26), k1_zfmisc_1(k2_zfmisc_1(A_25, B_26))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 5.72/2.13  tff(c_2535, plain, (![A_250, B_251, C_252, D_253]: (r2_relset_1(A_250, B_251, C_252, C_252) | ~m1_subset_1(D_253, k1_zfmisc_1(k2_zfmisc_1(A_250, B_251))) | ~m1_subset_1(C_252, k1_zfmisc_1(k2_zfmisc_1(A_250, B_251))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.72/2.13  tff(c_2554, plain, (![A_254, B_255, C_256]: (r2_relset_1(A_254, B_255, C_256, C_256) | ~m1_subset_1(C_256, k1_zfmisc_1(k2_zfmisc_1(A_254, B_255))))), inference(resolution, [status(thm)], [c_48, c_2535])).
% 5.72/2.13  tff(c_2562, plain, (![A_24]: (r2_relset_1(A_24, A_24, k6_partfun1(A_24), k6_partfun1(A_24)))), inference(resolution, [status(thm)], [c_38, c_2554])).
% 5.72/2.13  tff(c_105, plain, (![C_56, B_57, A_58]: (v5_relat_1(C_56, B_57) | ~m1_subset_1(C_56, k1_zfmisc_1(k2_zfmisc_1(A_58, B_57))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.72/2.13  tff(c_118, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_60, c_105])).
% 5.72/2.13  tff(c_2298, plain, (![B_203, A_204]: (k2_relat_1(B_203)=A_204 | ~v2_funct_2(B_203, A_204) | ~v5_relat_1(B_203, A_204) | ~v1_relat_1(B_203))), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.72/2.13  tff(c_2304, plain, (k2_relat_1('#skF_3')='#skF_2' | ~v2_funct_2('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_118, c_2298])).
% 5.72/2.13  tff(c_2313, plain, (k2_relat_1('#skF_3')='#skF_2' | ~v2_funct_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_104, c_2304])).
% 5.72/2.13  tff(c_2317, plain, (~v2_funct_2('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_2313])).
% 5.72/2.13  tff(c_2392, plain, (![C_222, B_223, A_224]: (v2_funct_2(C_222, B_223) | ~v3_funct_2(C_222, A_224, B_223) | ~v1_funct_1(C_222) | ~m1_subset_1(C_222, k1_zfmisc_1(k2_zfmisc_1(A_224, B_223))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.72/2.13  tff(c_2401, plain, (v2_funct_2('#skF_3', '#skF_2') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_60, c_2392])).
% 5.72/2.13  tff(c_2408, plain, (v2_funct_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_62, c_2401])).
% 5.72/2.13  tff(c_2410, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2317, c_2408])).
% 5.72/2.13  tff(c_2411, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(splitRight, [status(thm)], [c_2313])).
% 5.72/2.13  tff(c_54, plain, (![A_36]: (k6_relat_1(A_36)=k6_partfun1(A_36))), inference(cnfTransformation, [status(thm)], [f_133])).
% 5.72/2.13  tff(c_6, plain, (![A_6]: (k5_relat_1(k2_funct_1(A_6), A_6)=k6_relat_1(k2_relat_1(A_6)) | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.72/2.13  tff(c_68, plain, (![A_6]: (k5_relat_1(k2_funct_1(A_6), A_6)=k6_partfun1(k2_relat_1(A_6)) | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_6])).
% 5.72/2.13  tff(c_64, plain, (v1_funct_2('#skF_3', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_154])).
% 5.72/2.13  tff(c_2587, plain, (![A_265, B_266]: (k2_funct_2(A_265, B_266)=k2_funct_1(B_266) | ~m1_subset_1(B_266, k1_zfmisc_1(k2_zfmisc_1(A_265, A_265))) | ~v3_funct_2(B_266, A_265, A_265) | ~v1_funct_2(B_266, A_265, A_265) | ~v1_funct_1(B_266))), inference(cnfTransformation, [status(thm)], [f_131])).
% 5.72/2.13  tff(c_2597, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_60, c_2587])).
% 5.72/2.13  tff(c_2604, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_2597])).
% 5.72/2.13  tff(c_2567, plain, (![A_261, B_262]: (v1_funct_1(k2_funct_2(A_261, B_262)) | ~m1_subset_1(B_262, k1_zfmisc_1(k2_zfmisc_1(A_261, A_261))) | ~v3_funct_2(B_262, A_261, A_261) | ~v1_funct_2(B_262, A_261, A_261) | ~v1_funct_1(B_262))), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.72/2.13  tff(c_2577, plain, (v1_funct_1(k2_funct_2('#skF_2', '#skF_3')) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_60, c_2567])).
% 5.72/2.13  tff(c_2584, plain, (v1_funct_1(k2_funct_2('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_2577])).
% 5.72/2.13  tff(c_2605, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2604, c_2584])).
% 5.72/2.13  tff(c_28, plain, (![A_22, B_23]: (m1_subset_1(k2_funct_2(A_22, B_23), k1_zfmisc_1(k2_zfmisc_1(A_22, A_22))) | ~m1_subset_1(B_23, k1_zfmisc_1(k2_zfmisc_1(A_22, A_22))) | ~v3_funct_2(B_23, A_22, A_22) | ~v1_funct_2(B_23, A_22, A_22) | ~v1_funct_1(B_23))), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.72/2.13  tff(c_2773, plain, (![D_285, A_282, E_281, F_280, C_283, B_284]: (k1_partfun1(A_282, B_284, C_283, D_285, E_281, F_280)=k5_relat_1(E_281, F_280) | ~m1_subset_1(F_280, k1_zfmisc_1(k2_zfmisc_1(C_283, D_285))) | ~v1_funct_1(F_280) | ~m1_subset_1(E_281, k1_zfmisc_1(k2_zfmisc_1(A_282, B_284))) | ~v1_funct_1(E_281))), inference(cnfTransformation, [status(thm)], [f_121])).
% 5.72/2.13  tff(c_2783, plain, (![A_282, B_284, E_281]: (k1_partfun1(A_282, B_284, '#skF_2', '#skF_2', E_281, '#skF_3')=k5_relat_1(E_281, '#skF_3') | ~v1_funct_1('#skF_3') | ~m1_subset_1(E_281, k1_zfmisc_1(k2_zfmisc_1(A_282, B_284))) | ~v1_funct_1(E_281))), inference(resolution, [status(thm)], [c_60, c_2773])).
% 5.72/2.13  tff(c_2806, plain, (![A_286, B_287, E_288]: (k1_partfun1(A_286, B_287, '#skF_2', '#skF_2', E_288, '#skF_3')=k5_relat_1(E_288, '#skF_3') | ~m1_subset_1(E_288, k1_zfmisc_1(k2_zfmisc_1(A_286, B_287))) | ~v1_funct_1(E_288))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_2783])).
% 5.72/2.13  tff(c_3074, plain, (![A_296, B_297]: (k1_partfun1(A_296, A_296, '#skF_2', '#skF_2', k2_funct_2(A_296, B_297), '#skF_3')=k5_relat_1(k2_funct_2(A_296, B_297), '#skF_3') | ~v1_funct_1(k2_funct_2(A_296, B_297)) | ~m1_subset_1(B_297, k1_zfmisc_1(k2_zfmisc_1(A_296, A_296))) | ~v3_funct_2(B_297, A_296, A_296) | ~v1_funct_2(B_297, A_296, A_296) | ~v1_funct_1(B_297))), inference(resolution, [status(thm)], [c_28, c_2806])).
% 5.72/2.13  tff(c_3087, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_2('#skF_2', '#skF_3'), '#skF_3')=k5_relat_1(k2_funct_2('#skF_2', '#skF_3'), '#skF_3') | ~v1_funct_1(k2_funct_2('#skF_2', '#skF_3')) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_60, c_3074])).
% 5.72/2.13  tff(c_3101, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_1('#skF_3'), '#skF_3')=k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_2605, c_2604, c_2604, c_2604, c_3087])).
% 5.72/2.13  tff(c_300, plain, (![C_95, A_96, B_97]: (v2_funct_1(C_95) | ~v3_funct_2(C_95, A_96, B_97) | ~v1_funct_1(C_95) | ~m1_subset_1(C_95, k1_zfmisc_1(k2_zfmisc_1(A_96, B_97))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.72/2.13  tff(c_309, plain, (v2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_60, c_300])).
% 5.72/2.13  tff(c_316, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_62, c_309])).
% 5.72/2.13  tff(c_336, plain, (![A_104, B_105, C_106, D_107]: (r2_relset_1(A_104, B_105, C_106, C_106) | ~m1_subset_1(D_107, k1_zfmisc_1(k2_zfmisc_1(A_104, B_105))) | ~m1_subset_1(C_106, k1_zfmisc_1(k2_zfmisc_1(A_104, B_105))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.72/2.13  tff(c_347, plain, (![A_110, B_111, C_112]: (r2_relset_1(A_110, B_111, C_112, C_112) | ~m1_subset_1(C_112, k1_zfmisc_1(k2_zfmisc_1(A_110, B_111))))), inference(resolution, [status(thm)], [c_48, c_336])).
% 5.72/2.13  tff(c_355, plain, (![A_24]: (r2_relset_1(A_24, A_24, k6_partfun1(A_24), k6_partfun1(A_24)))), inference(resolution, [status(thm)], [c_38, c_347])).
% 5.72/2.13  tff(c_157, plain, (![A_68, B_69, C_70]: (k1_relset_1(A_68, B_69, C_70)=k1_relat_1(C_70) | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.72/2.13  tff(c_169, plain, (k1_relset_1('#skF_2', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_60, c_157])).
% 5.72/2.13  tff(c_360, plain, (![A_117, B_118]: (k1_relset_1(A_117, A_117, B_118)=A_117 | ~m1_subset_1(B_118, k1_zfmisc_1(k2_zfmisc_1(A_117, A_117))) | ~v1_funct_2(B_118, A_117, A_117) | ~v1_funct_1(B_118))), inference(cnfTransformation, [status(thm)], [f_141])).
% 5.72/2.13  tff(c_370, plain, (k1_relset_1('#skF_2', '#skF_2', '#skF_3')='#skF_2' | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_60, c_360])).
% 5.72/2.13  tff(c_378, plain, (k1_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_169, c_370])).
% 5.72/2.13  tff(c_8, plain, (![A_6]: (k5_relat_1(A_6, k2_funct_1(A_6))=k6_relat_1(k1_relat_1(A_6)) | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.72/2.13  tff(c_67, plain, (![A_6]: (k5_relat_1(A_6, k2_funct_1(A_6))=k6_partfun1(k1_relat_1(A_6)) | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_8])).
% 5.72/2.13  tff(c_406, plain, (![A_121, B_122]: (k2_funct_2(A_121, B_122)=k2_funct_1(B_122) | ~m1_subset_1(B_122, k1_zfmisc_1(k2_zfmisc_1(A_121, A_121))) | ~v3_funct_2(B_122, A_121, A_121) | ~v1_funct_2(B_122, A_121, A_121) | ~v1_funct_1(B_122))), inference(cnfTransformation, [status(thm)], [f_131])).
% 5.72/2.13  tff(c_416, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_60, c_406])).
% 5.72/2.13  tff(c_423, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_416])).
% 5.72/2.13  tff(c_379, plain, (![A_119, B_120]: (v1_funct_1(k2_funct_2(A_119, B_120)) | ~m1_subset_1(B_120, k1_zfmisc_1(k2_zfmisc_1(A_119, A_119))) | ~v3_funct_2(B_120, A_119, A_119) | ~v1_funct_2(B_120, A_119, A_119) | ~v1_funct_1(B_120))), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.72/2.13  tff(c_389, plain, (v1_funct_1(k2_funct_2('#skF_2', '#skF_3')) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_60, c_379])).
% 5.72/2.13  tff(c_396, plain, (v1_funct_1(k2_funct_2('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_389])).
% 5.72/2.13  tff(c_424, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_423, c_396])).
% 5.72/2.13  tff(c_592, plain, (![E_138, C_140, D_142, A_139, B_141, F_137]: (k1_partfun1(A_139, B_141, C_140, D_142, E_138, F_137)=k5_relat_1(E_138, F_137) | ~m1_subset_1(F_137, k1_zfmisc_1(k2_zfmisc_1(C_140, D_142))) | ~v1_funct_1(F_137) | ~m1_subset_1(E_138, k1_zfmisc_1(k2_zfmisc_1(A_139, B_141))) | ~v1_funct_1(E_138))), inference(cnfTransformation, [status(thm)], [f_121])).
% 5.72/2.13  tff(c_2155, plain, (![A_191, B_194, E_193, A_192, B_195]: (k1_partfun1(A_192, B_195, A_191, A_191, E_193, k2_funct_2(A_191, B_194))=k5_relat_1(E_193, k2_funct_2(A_191, B_194)) | ~v1_funct_1(k2_funct_2(A_191, B_194)) | ~m1_subset_1(E_193, k1_zfmisc_1(k2_zfmisc_1(A_192, B_195))) | ~v1_funct_1(E_193) | ~m1_subset_1(B_194, k1_zfmisc_1(k2_zfmisc_1(A_191, A_191))) | ~v3_funct_2(B_194, A_191, A_191) | ~v1_funct_2(B_194, A_191, A_191) | ~v1_funct_1(B_194))), inference(resolution, [status(thm)], [c_28, c_592])).
% 5.72/2.13  tff(c_2177, plain, (![A_191, B_194]: (k1_partfun1('#skF_2', '#skF_2', A_191, A_191, '#skF_3', k2_funct_2(A_191, B_194))=k5_relat_1('#skF_3', k2_funct_2(A_191, B_194)) | ~v1_funct_1(k2_funct_2(A_191, B_194)) | ~v1_funct_1('#skF_3') | ~m1_subset_1(B_194, k1_zfmisc_1(k2_zfmisc_1(A_191, A_191))) | ~v3_funct_2(B_194, A_191, A_191) | ~v1_funct_2(B_194, A_191, A_191) | ~v1_funct_1(B_194))), inference(resolution, [status(thm)], [c_60, c_2155])).
% 5.72/2.13  tff(c_2216, plain, (![A_196, B_197]: (k1_partfun1('#skF_2', '#skF_2', A_196, A_196, '#skF_3', k2_funct_2(A_196, B_197))=k5_relat_1('#skF_3', k2_funct_2(A_196, B_197)) | ~v1_funct_1(k2_funct_2(A_196, B_197)) | ~m1_subset_1(B_197, k1_zfmisc_1(k2_zfmisc_1(A_196, A_196))) | ~v3_funct_2(B_197, A_196, A_196) | ~v1_funct_2(B_197, A_196, A_196) | ~v1_funct_1(B_197))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_2177])).
% 5.72/2.13  tff(c_2239, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_2('#skF_2', '#skF_3'))=k5_relat_1('#skF_3', k2_funct_2('#skF_2', '#skF_3')) | ~v1_funct_1(k2_funct_2('#skF_2', '#skF_3')) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_60, c_2216])).
% 5.72/2.13  tff(c_2268, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_1('#skF_3'))=k5_relat_1('#skF_3', k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_424, c_423, c_423, c_423, c_2239])).
% 5.72/2.13  tff(c_58, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_2('#skF_2', '#skF_3'), '#skF_3'), k6_partfun1('#skF_2')) | ~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_2('#skF_2', '#skF_3')), k6_partfun1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_154])).
% 5.72/2.13  tff(c_121, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_2('#skF_2', '#skF_3')), k6_partfun1('#skF_2'))), inference(splitLeft, [status(thm)], [c_58])).
% 5.72/2.13  tff(c_425, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_1('#skF_3')), k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_423, c_121])).
% 5.72/2.13  tff(c_2269, plain, (~r2_relset_1('#skF_2', '#skF_2', k5_relat_1('#skF_3', k2_funct_1('#skF_3')), k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2268, c_425])).
% 5.72/2.13  tff(c_2276, plain, (~r2_relset_1('#skF_2', '#skF_2', k6_partfun1(k1_relat_1('#skF_3')), k6_partfun1('#skF_2')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_67, c_2269])).
% 5.72/2.13  tff(c_2279, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_104, c_66, c_316, c_355, c_378, c_2276])).
% 5.72/2.13  tff(c_2280, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_2('#skF_2', '#skF_3'), '#skF_3'), k6_partfun1('#skF_2'))), inference(splitRight, [status(thm)], [c_58])).
% 5.72/2.13  tff(c_2606, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_1('#skF_3'), '#skF_3'), k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2604, c_2280])).
% 5.72/2.13  tff(c_3241, plain, (~r2_relset_1('#skF_2', '#skF_2', k5_relat_1(k2_funct_1('#skF_3'), '#skF_3'), k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_3101, c_2606])).
% 5.72/2.13  tff(c_3248, plain, (~r2_relset_1('#skF_2', '#skF_2', k6_partfun1(k2_relat_1('#skF_3')), k6_partfun1('#skF_2')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_68, c_3241])).
% 5.72/2.13  tff(c_3251, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_104, c_66, c_2494, c_2562, c_2411, c_3248])).
% 5.72/2.13  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.72/2.13  
% 5.72/2.13  Inference rules
% 5.72/2.13  ----------------------
% 5.72/2.13  #Ref     : 0
% 5.72/2.13  #Sup     : 672
% 5.72/2.13  #Fact    : 0
% 5.72/2.13  #Define  : 0
% 5.72/2.13  #Split   : 3
% 5.72/2.13  #Chain   : 0
% 5.72/2.13  #Close   : 0
% 5.72/2.13  
% 5.72/2.13  Ordering : KBO
% 5.72/2.13  
% 5.72/2.13  Simplification rules
% 5.72/2.13  ----------------------
% 5.72/2.13  #Subsume      : 6
% 5.72/2.13  #Demod        : 1510
% 5.72/2.13  #Tautology    : 256
% 5.72/2.13  #SimpNegUnit  : 2
% 5.72/2.13  #BackRed      : 49
% 5.72/2.13  
% 5.72/2.13  #Partial instantiations: 0
% 5.72/2.13  #Strategies tried      : 1
% 5.72/2.13  
% 5.72/2.13  Timing (in seconds)
% 5.72/2.13  ----------------------
% 5.72/2.13  Preprocessing        : 0.36
% 5.72/2.13  Parsing              : 0.19
% 5.72/2.13  CNF conversion       : 0.02
% 5.72/2.13  Main loop            : 0.99
% 5.72/2.13  Inferencing          : 0.34
% 5.72/2.13  Reduction            : 0.39
% 5.72/2.13  Demodulation         : 0.30
% 5.72/2.13  BG Simplification    : 0.03
% 5.72/2.13  Subsumption          : 0.16
% 5.72/2.13  Abstraction          : 0.04
% 5.72/2.13  MUC search           : 0.00
% 5.72/2.13  Cooper               : 0.00
% 5.72/2.13  Total                : 1.39
% 5.72/2.13  Index Insertion      : 0.00
% 5.72/2.13  Index Deletion       : 0.00
% 5.72/2.13  Index Matching       : 0.00
% 5.72/2.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
