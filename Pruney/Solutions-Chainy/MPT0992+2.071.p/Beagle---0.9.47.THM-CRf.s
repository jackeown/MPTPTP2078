%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:41 EST 2020

% Result     : Theorem 6.75s
% Output     : CNFRefutation 6.75s
% Verified   : 
% Statistics : Number of formulae       :  200 (2192 expanded)
%              Number of leaves         :   36 ( 690 expanded)
%              Depth                    :   17
%              Number of atoms          :  358 (7121 expanded)
%              Number of equality atoms :   90 (2712 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_136,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r1_tarski(C,A)
         => ( ( B = k1_xboole_0
              & A != k1_xboole_0 )
            | ( v1_funct_1(k2_partfun1(A,B,D,C))
              & v1_funct_2(k2_partfun1(A,B,D,C),C,B)
              & m1_subset_1(k2_partfun1(A,B,D,C),k1_zfmisc_1(k2_zfmisc_1(C,B))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_funct_2)).

tff(f_50,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_90,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => ( v1_funct_2(C,A,B)
          <=> A = k1_relset_1(A,B,C) ) )
        & ( B = k1_xboole_0
         => ( A = k1_xboole_0
            | ( v1_funct_2(C,A,B)
            <=> C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_62,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_104,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_98,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_partfun1(A,B,C,D))
        & m1_subset_1(k2_partfun1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_partfun1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_116,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_29,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(c_56,plain,(
    r1_tarski('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_16,plain,(
    ! [A_9,B_10] : v1_relat_1(k2_zfmisc_1(A_9,B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_58,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_97,plain,(
    ! [B_39,A_40] :
      ( v1_relat_1(B_39)
      | ~ m1_subset_1(B_39,k1_zfmisc_1(A_40))
      | ~ v1_relat_1(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_100,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_58,c_97])).

tff(c_103,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_100])).

tff(c_54,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_67,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_60,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_3693,plain,(
    ! [A_428,B_429,C_430] :
      ( k1_relset_1(A_428,B_429,C_430) = k1_relat_1(C_430)
      | ~ m1_subset_1(C_430,k1_zfmisc_1(k2_zfmisc_1(A_428,B_429))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_3707,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_3693])).

tff(c_3861,plain,(
    ! [B_466,A_467,C_468] :
      ( k1_xboole_0 = B_466
      | k1_relset_1(A_467,B_466,C_468) = A_467
      | ~ v1_funct_2(C_468,A_467,B_466)
      | ~ m1_subset_1(C_468,k1_zfmisc_1(k2_zfmisc_1(A_467,B_466))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_3870,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_58,c_3861])).

tff(c_3882,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_3707,c_3870])).

tff(c_3883,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_3882])).

tff(c_20,plain,(
    ! [B_14,A_13] :
      ( k1_relat_1(k7_relat_1(B_14,A_13)) = A_13
      | ~ r1_tarski(A_13,k1_relat_1(B_14))
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_3895,plain,(
    ! [A_13] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_13)) = A_13
      | ~ r1_tarski(A_13,'#skF_1')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3883,c_20])).

tff(c_3903,plain,(
    ! [A_13] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_13)) = A_13
      | ~ r1_tarski(A_13,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_3895])).

tff(c_62,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_3780,plain,(
    ! [A_459,B_460,C_461,D_462] :
      ( k2_partfun1(A_459,B_460,C_461,D_462) = k7_relat_1(C_461,D_462)
      | ~ m1_subset_1(C_461,k1_zfmisc_1(k2_zfmisc_1(A_459,B_460)))
      | ~ v1_funct_1(C_461) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_3786,plain,(
    ! [D_462] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_462) = k7_relat_1('#skF_4',D_462)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_58,c_3780])).

tff(c_3797,plain,(
    ! [D_462] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_462) = k7_relat_1('#skF_4',D_462) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_3786])).

tff(c_312,plain,(
    ! [A_122,B_123,C_124,D_125] :
      ( k2_partfun1(A_122,B_123,C_124,D_125) = k7_relat_1(C_124,D_125)
      | ~ m1_subset_1(C_124,k1_zfmisc_1(k2_zfmisc_1(A_122,B_123)))
      | ~ v1_funct_1(C_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_316,plain,(
    ! [D_125] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_125) = k7_relat_1('#skF_4',D_125)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_58,c_312])).

tff(c_324,plain,(
    ! [D_125] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_125) = k7_relat_1('#skF_4',D_125) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_316])).

tff(c_473,plain,(
    ! [A_139,B_140,C_141,D_142] :
      ( m1_subset_1(k2_partfun1(A_139,B_140,C_141,D_142),k1_zfmisc_1(k2_zfmisc_1(A_139,B_140)))
      | ~ m1_subset_1(C_141,k1_zfmisc_1(k2_zfmisc_1(A_139,B_140)))
      | ~ v1_funct_1(C_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_498,plain,(
    ! [D_125] :
      ( m1_subset_1(k7_relat_1('#skF_4',D_125),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_324,c_473])).

tff(c_524,plain,(
    ! [D_144] : m1_subset_1(k7_relat_1('#skF_4',D_144),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_498])).

tff(c_10,plain,(
    ! [B_6,A_4] :
      ( v1_relat_1(B_6)
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_4))
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_546,plain,(
    ! [D_144] :
      ( v1_relat_1(k7_relat_1('#skF_4',D_144))
      | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_524,c_10])).

tff(c_566,plain,(
    ! [D_144] : v1_relat_1(k7_relat_1('#skF_4',D_144)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_546])).

tff(c_22,plain,(
    ! [C_17,B_16,A_15] :
      ( v5_relat_1(C_17,B_16)
      | ~ m1_subset_1(C_17,k1_zfmisc_1(k2_zfmisc_1(A_15,B_16))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_563,plain,(
    ! [D_144] : v5_relat_1(k7_relat_1('#skF_4',D_144),'#skF_2') ),
    inference(resolution,[status(thm)],[c_524,c_22])).

tff(c_14,plain,(
    ! [B_8,A_7] :
      ( r1_tarski(k2_relat_1(B_8),A_7)
      | ~ v5_relat_1(B_8,A_7)
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_268,plain,(
    ! [A_107,B_108,C_109,D_110] :
      ( v1_funct_1(k2_partfun1(A_107,B_108,C_109,D_110))
      | ~ m1_subset_1(C_109,k1_zfmisc_1(k2_zfmisc_1(A_107,B_108)))
      | ~ v1_funct_1(C_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_270,plain,(
    ! [D_110] :
      ( v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_110))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_58,c_268])).

tff(c_277,plain,(
    ! [D_110] : v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_110)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_270])).

tff(c_325,plain,(
    ! [D_110] : v1_funct_1(k7_relat_1('#skF_4',D_110)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_324,c_277])).

tff(c_243,plain,(
    ! [A_92,B_93,C_94] :
      ( k1_relset_1(A_92,B_93,C_94) = k1_relat_1(C_94)
      | ~ m1_subset_1(C_94,k1_zfmisc_1(k2_zfmisc_1(A_92,B_93))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_253,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_243])).

tff(c_417,plain,(
    ! [B_135,A_136,C_137] :
      ( k1_xboole_0 = B_135
      | k1_relset_1(A_136,B_135,C_137) = A_136
      | ~ v1_funct_2(C_137,A_136,B_135)
      | ~ m1_subset_1(C_137,k1_zfmisc_1(k2_zfmisc_1(A_136,B_135))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_423,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_58,c_417])).

tff(c_433,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_253,c_423])).

tff(c_434,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_433])).

tff(c_450,plain,(
    ! [A_13] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_13)) = A_13
      | ~ r1_tarski(A_13,'#skF_1')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_434,c_20])).

tff(c_597,plain,(
    ! [A_149] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_149)) = A_149
      | ~ r1_tarski(A_149,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_450])).

tff(c_46,plain,(
    ! [B_33,A_32] :
      ( m1_subset_1(B_33,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_33),A_32)))
      | ~ r1_tarski(k2_relat_1(B_33),A_32)
      | ~ v1_funct_1(B_33)
      | ~ v1_relat_1(B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_603,plain,(
    ! [A_149,A_32] :
      ( m1_subset_1(k7_relat_1('#skF_4',A_149),k1_zfmisc_1(k2_zfmisc_1(A_149,A_32)))
      | ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4',A_149)),A_32)
      | ~ v1_funct_1(k7_relat_1('#skF_4',A_149))
      | ~ v1_relat_1(k7_relat_1('#skF_4',A_149))
      | ~ r1_tarski(A_149,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_597,c_46])).

tff(c_3578,plain,(
    ! [A_423,A_424] :
      ( m1_subset_1(k7_relat_1('#skF_4',A_423),k1_zfmisc_1(k2_zfmisc_1(A_423,A_424)))
      | ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4',A_423)),A_424)
      | ~ r1_tarski(A_423,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_566,c_325,c_603])).

tff(c_195,plain,(
    ! [A_76,B_77,C_78,D_79] :
      ( v1_funct_1(k2_partfun1(A_76,B_77,C_78,D_79))
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77)))
      | ~ v1_funct_1(C_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_197,plain,(
    ! [D_79] :
      ( v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_79))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_58,c_195])).

tff(c_204,plain,(
    ! [D_79] : v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_79)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_197])).

tff(c_52,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2')
    | ~ v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_138,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_207,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_204,c_138])).

tff(c_208,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2')
    | ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_234,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_208])).

tff(c_326,plain,(
    ~ m1_subset_1(k7_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_324,c_234])).

tff(c_3597,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_2')
    | ~ r1_tarski('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_3578,c_326])).

tff(c_3642,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_3597])).

tff(c_3658,plain,
    ( ~ v5_relat_1(k7_relat_1('#skF_4','#skF_3'),'#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_14,c_3642])).

tff(c_3662,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_566,c_563,c_3658])).

tff(c_3663,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_208])).

tff(c_3806,plain,(
    ~ v1_funct_2(k7_relat_1('#skF_4','#skF_3'),'#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3797,c_3663])).

tff(c_3664,plain,(
    m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_208])).

tff(c_3706,plain,(
    k1_relset_1('#skF_3','#skF_2',k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) = k1_relat_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_3664,c_3693])).

tff(c_3799,plain,(
    k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) = k1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3797,c_3797,c_3706])).

tff(c_3805,plain,(
    m1_subset_1(k7_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3797,c_3664])).

tff(c_3955,plain,(
    ! [B_472,C_473,A_474] :
      ( k1_xboole_0 = B_472
      | v1_funct_2(C_473,A_474,B_472)
      | k1_relset_1(A_474,B_472,C_473) != A_474
      | ~ m1_subset_1(C_473,k1_zfmisc_1(k2_zfmisc_1(A_474,B_472))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_3958,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2(k7_relat_1('#skF_4','#skF_3'),'#skF_3','#skF_2')
    | k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(resolution,[status(thm)],[c_3805,c_3955])).

tff(c_3972,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2(k7_relat_1('#skF_4','#skF_3'),'#skF_3','#skF_2')
    | k1_relat_1(k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3799,c_3958])).

tff(c_3973,plain,(
    k1_relat_1(k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_3806,c_67,c_3972])).

tff(c_3982,plain,(
    ~ r1_tarski('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_3903,c_3973])).

tff(c_3986,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_3982])).

tff(c_3987,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_8,plain,(
    ! [B_3] : k2_zfmisc_1(k1_xboole_0,B_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_4003,plain,(
    ! [B_477] : k2_zfmisc_1('#skF_1',B_477) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3987,c_3987,c_8])).

tff(c_4007,plain,(
    v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_4003,c_16])).

tff(c_4001,plain,(
    ! [B_3] : k2_zfmisc_1('#skF_1',B_3) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3987,c_3987,c_8])).

tff(c_3988,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_3993,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3987,c_3988])).

tff(c_3999,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3993,c_58])).

tff(c_4002,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4001,c_3999])).

tff(c_4356,plain,(
    ! [C_553,B_554,A_555] :
      ( v5_relat_1(C_553,B_554)
      | ~ m1_subset_1(C_553,k1_zfmisc_1(k2_zfmisc_1(A_555,B_554))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_4408,plain,(
    ! [C_559,B_560] :
      ( v5_relat_1(C_559,B_560)
      | ~ m1_subset_1(C_559,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4001,c_4356])).

tff(c_4411,plain,(
    ! [B_560] : v5_relat_1('#skF_4',B_560) ),
    inference(resolution,[status(thm)],[c_4002,c_4408])).

tff(c_4310,plain,(
    ! [B_537,A_538] :
      ( v1_relat_1(B_537)
      | ~ m1_subset_1(B_537,k1_zfmisc_1(A_538))
      | ~ v1_relat_1(A_538) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_4313,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_4002,c_4310])).

tff(c_4316,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4007,c_4313])).

tff(c_6,plain,(
    ! [A_2] : k2_zfmisc_1(A_2,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_4012,plain,(
    ! [A_2] : k2_zfmisc_1(A_2,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3987,c_3987,c_6])).

tff(c_4318,plain,(
    ! [C_541,A_542,B_543] :
      ( v4_relat_1(C_541,A_542)
      | ~ m1_subset_1(C_541,k1_zfmisc_1(k2_zfmisc_1(A_542,B_543))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_4326,plain,(
    ! [C_546,A_547] :
      ( v4_relat_1(C_546,A_547)
      | ~ m1_subset_1(C_546,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4012,c_4318])).

tff(c_4330,plain,(
    ! [A_548] : v4_relat_1('#skF_4',A_548) ),
    inference(resolution,[status(thm)],[c_4002,c_4326])).

tff(c_18,plain,(
    ! [B_12,A_11] :
      ( k7_relat_1(B_12,A_11) = B_12
      | ~ v4_relat_1(B_12,A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_4333,plain,(
    ! [A_548] :
      ( k7_relat_1('#skF_4',A_548) = '#skF_4'
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_4330,c_18])).

tff(c_4336,plain,(
    ! [A_548] : k7_relat_1('#skF_4',A_548) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4316,c_4333])).

tff(c_4753,plain,(
    ! [A_616,B_617,C_618,D_619] :
      ( k2_partfun1(A_616,B_617,C_618,D_619) = k7_relat_1(C_618,D_619)
      | ~ m1_subset_1(C_618,k1_zfmisc_1(k2_zfmisc_1(A_616,B_617)))
      | ~ v1_funct_1(C_618) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_4815,plain,(
    ! [A_638,C_639,D_640] :
      ( k2_partfun1(A_638,'#skF_1',C_639,D_640) = k7_relat_1(C_639,D_640)
      | ~ m1_subset_1(C_639,k1_zfmisc_1('#skF_1'))
      | ~ v1_funct_1(C_639) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4012,c_4753])).

tff(c_4819,plain,(
    ! [A_638,D_640] :
      ( k2_partfun1(A_638,'#skF_1','#skF_4',D_640) = k7_relat_1('#skF_4',D_640)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_4002,c_4815])).

tff(c_4823,plain,(
    ! [A_638,D_640] : k2_partfun1(A_638,'#skF_1','#skF_4',D_640) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_4336,c_4819])).

tff(c_4778,plain,(
    ! [B_630,C_631,D_632] :
      ( k2_partfun1('#skF_1',B_630,C_631,D_632) = k7_relat_1(C_631,D_632)
      | ~ m1_subset_1(C_631,k1_zfmisc_1('#skF_1'))
      | ~ v1_funct_1(C_631) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4001,c_4753])).

tff(c_4782,plain,(
    ! [B_630,D_632] :
      ( k2_partfun1('#skF_1',B_630,'#skF_4',D_632) = k7_relat_1('#skF_4',D_632)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_4002,c_4778])).

tff(c_4786,plain,(
    ! [B_630,D_632] : k2_partfun1('#skF_1',B_630,'#skF_4',D_632) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_4336,c_4782])).

tff(c_4600,plain,(
    ! [A_588,B_589,C_590,D_591] :
      ( v1_funct_1(k2_partfun1(A_588,B_589,C_590,D_591))
      | ~ m1_subset_1(C_590,k1_zfmisc_1(k2_zfmisc_1(A_588,B_589)))
      | ~ v1_funct_1(C_590) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_4605,plain,(
    ! [A_592,C_593,D_594] :
      ( v1_funct_1(k2_partfun1(A_592,'#skF_1',C_593,D_594))
      | ~ m1_subset_1(C_593,k1_zfmisc_1('#skF_1'))
      | ~ v1_funct_1(C_593) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4012,c_4600])).

tff(c_4607,plain,(
    ! [A_592,D_594] :
      ( v1_funct_1(k2_partfun1(A_592,'#skF_1','#skF_4',D_594))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_4002,c_4605])).

tff(c_4610,plain,(
    ! [A_592,D_594] : v1_funct_1(k2_partfun1(A_592,'#skF_1','#skF_4',D_594)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_4607])).

tff(c_4620,plain,(
    ! [B_602,A_603] :
      ( m1_subset_1(B_602,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_602),A_603)))
      | ~ r1_tarski(k2_relat_1(B_602),A_603)
      | ~ v1_funct_1(B_602)
      | ~ v1_relat_1(B_602) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_4672,plain,(
    ! [B_608] :
      ( m1_subset_1(B_608,k1_zfmisc_1('#skF_1'))
      | ~ r1_tarski(k2_relat_1(B_608),'#skF_1')
      | ~ v1_funct_1(B_608)
      | ~ v1_relat_1(B_608) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4012,c_4620])).

tff(c_4698,plain,(
    ! [B_611] :
      ( m1_subset_1(B_611,k1_zfmisc_1('#skF_1'))
      | ~ v1_funct_1(B_611)
      | ~ v5_relat_1(B_611,'#skF_1')
      | ~ v1_relat_1(B_611) ) ),
    inference(resolution,[status(thm)],[c_14,c_4672])).

tff(c_4282,plain,(
    ! [A_528,B_529,C_530,D_531] :
      ( v1_funct_1(k2_partfun1(A_528,B_529,C_530,D_531))
      | ~ m1_subset_1(C_530,k1_zfmisc_1(k2_zfmisc_1(A_528,B_529)))
      | ~ v1_funct_1(C_530) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_4287,plain,(
    ! [A_532,C_533,D_534] :
      ( v1_funct_1(k2_partfun1(A_532,'#skF_1',C_533,D_534))
      | ~ m1_subset_1(C_533,k1_zfmisc_1('#skF_1'))
      | ~ v1_funct_1(C_533) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4012,c_4282])).

tff(c_4289,plain,(
    ! [A_532,D_534] :
      ( v1_funct_1(k2_partfun1(A_532,'#skF_1','#skF_4',D_534))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_4002,c_4287])).

tff(c_4292,plain,(
    ! [A_532,D_534] : v1_funct_1(k2_partfun1(A_532,'#skF_1','#skF_4',D_534)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_4289])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ r1_tarski(A_1,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_4032,plain,(
    ! [A_479] :
      ( A_479 = '#skF_1'
      | ~ r1_tarski(A_479,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3987,c_3987,c_2])).

tff(c_4036,plain,(
    '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_56,c_4032])).

tff(c_4047,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),k1_zfmisc_1('#skF_1'))
    | ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4036,c_3993,c_4036,c_4036,c_3993,c_3993,c_4036,c_4012,c_3993,c_3993,c_52])).

tff(c_4048,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_4047])).

tff(c_4295,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4292,c_4048])).

tff(c_4296,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),'#skF_1','#skF_1')
    | ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),k1_zfmisc_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_4047])).

tff(c_4344,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),k1_zfmisc_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_4296])).

tff(c_4716,plain,
    ( ~ v1_funct_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'))
    | ~ v5_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),'#skF_1')
    | ~ v1_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ),
    inference(resolution,[status(thm)],[c_4698,c_4344])).

tff(c_4733,plain,
    ( ~ v5_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),'#skF_1')
    | ~ v1_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4610,c_4716])).

tff(c_4770,plain,(
    ~ v1_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_4733])).

tff(c_4787,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4786,c_4770])).

tff(c_4792,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4316,c_4787])).

tff(c_4793,plain,(
    ~ v5_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_4733])).

tff(c_4824,plain,(
    ~ v5_relat_1('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4823,c_4793])).

tff(c_4830,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4411,c_4824])).

tff(c_4832,plain,(
    m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),k1_zfmisc_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_4296])).

tff(c_4837,plain,
    ( v1_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'))
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_4832,c_10])).

tff(c_4841,plain,(
    v1_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4007,c_4837])).

tff(c_4297,plain,(
    v1_funct_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_4047])).

tff(c_4860,plain,(
    ! [C_645,B_646,A_647] :
      ( v5_relat_1(C_645,B_646)
      | ~ m1_subset_1(C_645,k1_zfmisc_1(k2_zfmisc_1(A_647,B_646))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_4914,plain,(
    ! [C_651,B_652] :
      ( v5_relat_1(C_651,B_652)
      | ~ m1_subset_1(C_651,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4001,c_4860])).

tff(c_4920,plain,(
    ! [B_652] : v5_relat_1('#skF_4',B_652) ),
    inference(resolution,[status(thm)],[c_4002,c_4914])).

tff(c_4867,plain,(
    ! [C_648] :
      ( v5_relat_1(C_648,'#skF_1')
      | ~ m1_subset_1(C_648,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4012,c_4860])).

tff(c_4875,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_4002,c_4867])).

tff(c_4849,plain,(
    ! [B_642,A_643] :
      ( r1_tarski(k2_relat_1(B_642),A_643)
      | ~ v5_relat_1(B_642,A_643)
      | ~ v1_relat_1(B_642) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_4031,plain,(
    ! [A_1] :
      ( A_1 = '#skF_1'
      | ~ r1_tarski(A_1,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3987,c_3987,c_2])).

tff(c_4858,plain,(
    ! [B_642] :
      ( k2_relat_1(B_642) = '#skF_1'
      | ~ v5_relat_1(B_642,'#skF_1')
      | ~ v1_relat_1(B_642) ) ),
    inference(resolution,[status(thm)],[c_4849,c_4031])).

tff(c_4878,plain,
    ( k2_relat_1('#skF_4') = '#skF_1'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_4875,c_4858])).

tff(c_4881,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4316,c_4878])).

tff(c_4885,plain,(
    ! [A_7] :
      ( r1_tarski('#skF_1',A_7)
      | ~ v5_relat_1('#skF_4',A_7)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4881,c_14])).

tff(c_4892,plain,(
    ! [A_7] :
      ( r1_tarski('#skF_1',A_7)
      | ~ v5_relat_1('#skF_4',A_7) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4316,c_4885])).

tff(c_4923,plain,(
    ! [A_7] : r1_tarski('#skF_1',A_7) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4920,c_4892])).

tff(c_4874,plain,(
    v5_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_4832,c_4867])).

tff(c_4945,plain,
    ( k2_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) = '#skF_1'
    | ~ v1_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ),
    inference(resolution,[status(thm)],[c_4874,c_4858])).

tff(c_4948,plain,(
    k2_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4841,c_4945])).

tff(c_4321,plain,(
    ! [C_541,A_2] :
      ( v4_relat_1(C_541,A_2)
      | ~ m1_subset_1(C_541,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4012,c_4318])).

tff(c_4842,plain,(
    ! [A_641] : v4_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),A_641) ),
    inference(resolution,[status(thm)],[c_4832,c_4321])).

tff(c_4845,plain,(
    ! [A_641] :
      ( k7_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),A_641) = k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')
      | ~ v1_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_4842,c_18])).

tff(c_5064,plain,(
    ! [A_670] : k7_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),A_670) = k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4841,c_4845])).

tff(c_4973,plain,(
    ! [B_656,A_657] :
      ( k1_relat_1(k7_relat_1(B_656,A_657)) = A_657
      | ~ r1_tarski(A_657,k1_relat_1(B_656))
      | ~ v1_relat_1(B_656) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_4982,plain,(
    ! [B_656] :
      ( k1_relat_1(k7_relat_1(B_656,'#skF_1')) = '#skF_1'
      | ~ v1_relat_1(B_656) ) ),
    inference(resolution,[status(thm)],[c_4923,c_4973])).

tff(c_5070,plain,
    ( k1_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) = '#skF_1'
    | ~ v1_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_5064,c_4982])).

tff(c_5075,plain,(
    k1_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4841,c_5070])).

tff(c_5105,plain,(
    ! [B_674,A_675] :
      ( v1_funct_2(B_674,k1_relat_1(B_674),A_675)
      | ~ r1_tarski(k2_relat_1(B_674),A_675)
      | ~ v1_funct_1(B_674)
      | ~ v1_relat_1(B_674) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_5111,plain,(
    ! [A_675] :
      ( v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),'#skF_1',A_675)
      | ~ r1_tarski(k2_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')),A_675)
      | ~ v1_funct_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'))
      | ~ v1_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5075,c_5105])).

tff(c_5120,plain,(
    ! [A_675] : v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),'#skF_1',A_675) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4841,c_4297,c_4923,c_4948,c_5111])).

tff(c_4831,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),'#skF_1','#skF_1') ),
    inference(splitRight,[status(thm)],[c_4296])).

tff(c_5125,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5120,c_4831])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n006.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 18:30:07 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.75/2.36  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.75/2.39  
% 6.75/2.39  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.75/2.39  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 6.75/2.39  
% 6.75/2.39  %Foreground sorts:
% 6.75/2.39  
% 6.75/2.39  
% 6.75/2.39  %Background operators:
% 6.75/2.39  
% 6.75/2.39  
% 6.75/2.39  %Foreground operators:
% 6.75/2.39  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.75/2.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.75/2.39  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 6.75/2.39  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.75/2.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.75/2.39  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.75/2.39  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.75/2.39  tff('#skF_2', type, '#skF_2': $i).
% 6.75/2.39  tff('#skF_3', type, '#skF_3': $i).
% 6.75/2.39  tff('#skF_1', type, '#skF_1': $i).
% 6.75/2.39  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 6.75/2.39  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 6.75/2.39  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.75/2.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.75/2.39  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.75/2.39  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.75/2.39  tff('#skF_4', type, '#skF_4': $i).
% 6.75/2.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.75/2.39  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 6.75/2.39  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 6.75/2.39  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.75/2.39  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.75/2.39  
% 6.75/2.42  tff(f_136, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(C, A) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(k2_partfun1(A, B, D, C)) & v1_funct_2(k2_partfun1(A, B, D, C), C, B)) & m1_subset_1(k2_partfun1(A, B, D, C), k1_zfmisc_1(k2_zfmisc_1(C, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_funct_2)).
% 6.75/2.42  tff(f_50, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 6.75/2.42  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 6.75/2.42  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 6.75/2.42  tff(f_90, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 6.75/2.42  tff(f_62, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_relat_1)).
% 6.75/2.42  tff(f_104, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 6.75/2.42  tff(f_98, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (v1_funct_1(k2_partfun1(A, B, C, D)) & m1_subset_1(k2_partfun1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_partfun1)).
% 6.75/2.42  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 6.75/2.42  tff(f_48, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 6.75/2.42  tff(f_116, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_funct_2)).
% 6.75/2.42  tff(f_35, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 6.75/2.42  tff(f_56, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 6.75/2.42  tff(f_29, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 6.75/2.42  tff(c_56, plain, (r1_tarski('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_136])).
% 6.75/2.42  tff(c_16, plain, (![A_9, B_10]: (v1_relat_1(k2_zfmisc_1(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 6.75/2.42  tff(c_58, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_136])).
% 6.75/2.42  tff(c_97, plain, (![B_39, A_40]: (v1_relat_1(B_39) | ~m1_subset_1(B_39, k1_zfmisc_1(A_40)) | ~v1_relat_1(A_40))), inference(cnfTransformation, [status(thm)], [f_42])).
% 6.75/2.42  tff(c_100, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_58, c_97])).
% 6.75/2.42  tff(c_103, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_100])).
% 6.75/2.42  tff(c_54, plain, (k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_136])).
% 6.75/2.42  tff(c_67, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_54])).
% 6.75/2.42  tff(c_60, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_136])).
% 6.75/2.42  tff(c_3693, plain, (![A_428, B_429, C_430]: (k1_relset_1(A_428, B_429, C_430)=k1_relat_1(C_430) | ~m1_subset_1(C_430, k1_zfmisc_1(k2_zfmisc_1(A_428, B_429))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 6.75/2.42  tff(c_3707, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_58, c_3693])).
% 6.75/2.42  tff(c_3861, plain, (![B_466, A_467, C_468]: (k1_xboole_0=B_466 | k1_relset_1(A_467, B_466, C_468)=A_467 | ~v1_funct_2(C_468, A_467, B_466) | ~m1_subset_1(C_468, k1_zfmisc_1(k2_zfmisc_1(A_467, B_466))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 6.75/2.42  tff(c_3870, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_58, c_3861])).
% 6.75/2.42  tff(c_3882, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_3707, c_3870])).
% 6.75/2.42  tff(c_3883, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_67, c_3882])).
% 6.75/2.42  tff(c_20, plain, (![B_14, A_13]: (k1_relat_1(k7_relat_1(B_14, A_13))=A_13 | ~r1_tarski(A_13, k1_relat_1(B_14)) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_62])).
% 6.75/2.42  tff(c_3895, plain, (![A_13]: (k1_relat_1(k7_relat_1('#skF_4', A_13))=A_13 | ~r1_tarski(A_13, '#skF_1') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_3883, c_20])).
% 6.75/2.42  tff(c_3903, plain, (![A_13]: (k1_relat_1(k7_relat_1('#skF_4', A_13))=A_13 | ~r1_tarski(A_13, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_3895])).
% 6.75/2.42  tff(c_62, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_136])).
% 6.75/2.42  tff(c_3780, plain, (![A_459, B_460, C_461, D_462]: (k2_partfun1(A_459, B_460, C_461, D_462)=k7_relat_1(C_461, D_462) | ~m1_subset_1(C_461, k1_zfmisc_1(k2_zfmisc_1(A_459, B_460))) | ~v1_funct_1(C_461))), inference(cnfTransformation, [status(thm)], [f_104])).
% 6.75/2.42  tff(c_3786, plain, (![D_462]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_462)=k7_relat_1('#skF_4', D_462) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_58, c_3780])).
% 6.75/2.42  tff(c_3797, plain, (![D_462]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_462)=k7_relat_1('#skF_4', D_462))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_3786])).
% 6.75/2.42  tff(c_312, plain, (![A_122, B_123, C_124, D_125]: (k2_partfun1(A_122, B_123, C_124, D_125)=k7_relat_1(C_124, D_125) | ~m1_subset_1(C_124, k1_zfmisc_1(k2_zfmisc_1(A_122, B_123))) | ~v1_funct_1(C_124))), inference(cnfTransformation, [status(thm)], [f_104])).
% 6.75/2.42  tff(c_316, plain, (![D_125]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_125)=k7_relat_1('#skF_4', D_125) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_58, c_312])).
% 6.75/2.42  tff(c_324, plain, (![D_125]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_125)=k7_relat_1('#skF_4', D_125))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_316])).
% 6.75/2.42  tff(c_473, plain, (![A_139, B_140, C_141, D_142]: (m1_subset_1(k2_partfun1(A_139, B_140, C_141, D_142), k1_zfmisc_1(k2_zfmisc_1(A_139, B_140))) | ~m1_subset_1(C_141, k1_zfmisc_1(k2_zfmisc_1(A_139, B_140))) | ~v1_funct_1(C_141))), inference(cnfTransformation, [status(thm)], [f_98])).
% 6.75/2.42  tff(c_498, plain, (![D_125]: (m1_subset_1(k7_relat_1('#skF_4', D_125), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_324, c_473])).
% 6.75/2.42  tff(c_524, plain, (![D_144]: (m1_subset_1(k7_relat_1('#skF_4', D_144), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_58, c_498])).
% 6.75/2.42  tff(c_10, plain, (![B_6, A_4]: (v1_relat_1(B_6) | ~m1_subset_1(B_6, k1_zfmisc_1(A_4)) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_42])).
% 6.75/2.42  tff(c_546, plain, (![D_144]: (v1_relat_1(k7_relat_1('#skF_4', D_144)) | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(resolution, [status(thm)], [c_524, c_10])).
% 6.75/2.42  tff(c_566, plain, (![D_144]: (v1_relat_1(k7_relat_1('#skF_4', D_144)))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_546])).
% 6.75/2.42  tff(c_22, plain, (![C_17, B_16, A_15]: (v5_relat_1(C_17, B_16) | ~m1_subset_1(C_17, k1_zfmisc_1(k2_zfmisc_1(A_15, B_16))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 6.75/2.42  tff(c_563, plain, (![D_144]: (v5_relat_1(k7_relat_1('#skF_4', D_144), '#skF_2'))), inference(resolution, [status(thm)], [c_524, c_22])).
% 6.75/2.42  tff(c_14, plain, (![B_8, A_7]: (r1_tarski(k2_relat_1(B_8), A_7) | ~v5_relat_1(B_8, A_7) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_48])).
% 6.75/2.42  tff(c_268, plain, (![A_107, B_108, C_109, D_110]: (v1_funct_1(k2_partfun1(A_107, B_108, C_109, D_110)) | ~m1_subset_1(C_109, k1_zfmisc_1(k2_zfmisc_1(A_107, B_108))) | ~v1_funct_1(C_109))), inference(cnfTransformation, [status(thm)], [f_98])).
% 6.75/2.42  tff(c_270, plain, (![D_110]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_110)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_58, c_268])).
% 6.75/2.42  tff(c_277, plain, (![D_110]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_110)))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_270])).
% 6.75/2.42  tff(c_325, plain, (![D_110]: (v1_funct_1(k7_relat_1('#skF_4', D_110)))), inference(demodulation, [status(thm), theory('equality')], [c_324, c_277])).
% 6.75/2.42  tff(c_243, plain, (![A_92, B_93, C_94]: (k1_relset_1(A_92, B_93, C_94)=k1_relat_1(C_94) | ~m1_subset_1(C_94, k1_zfmisc_1(k2_zfmisc_1(A_92, B_93))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 6.75/2.42  tff(c_253, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_58, c_243])).
% 6.75/2.42  tff(c_417, plain, (![B_135, A_136, C_137]: (k1_xboole_0=B_135 | k1_relset_1(A_136, B_135, C_137)=A_136 | ~v1_funct_2(C_137, A_136, B_135) | ~m1_subset_1(C_137, k1_zfmisc_1(k2_zfmisc_1(A_136, B_135))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 6.75/2.42  tff(c_423, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_58, c_417])).
% 6.75/2.42  tff(c_433, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_253, c_423])).
% 6.75/2.42  tff(c_434, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_67, c_433])).
% 6.75/2.42  tff(c_450, plain, (![A_13]: (k1_relat_1(k7_relat_1('#skF_4', A_13))=A_13 | ~r1_tarski(A_13, '#skF_1') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_434, c_20])).
% 6.75/2.42  tff(c_597, plain, (![A_149]: (k1_relat_1(k7_relat_1('#skF_4', A_149))=A_149 | ~r1_tarski(A_149, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_450])).
% 6.75/2.42  tff(c_46, plain, (![B_33, A_32]: (m1_subset_1(B_33, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_33), A_32))) | ~r1_tarski(k2_relat_1(B_33), A_32) | ~v1_funct_1(B_33) | ~v1_relat_1(B_33))), inference(cnfTransformation, [status(thm)], [f_116])).
% 6.75/2.42  tff(c_603, plain, (![A_149, A_32]: (m1_subset_1(k7_relat_1('#skF_4', A_149), k1_zfmisc_1(k2_zfmisc_1(A_149, A_32))) | ~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', A_149)), A_32) | ~v1_funct_1(k7_relat_1('#skF_4', A_149)) | ~v1_relat_1(k7_relat_1('#skF_4', A_149)) | ~r1_tarski(A_149, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_597, c_46])).
% 6.75/2.42  tff(c_3578, plain, (![A_423, A_424]: (m1_subset_1(k7_relat_1('#skF_4', A_423), k1_zfmisc_1(k2_zfmisc_1(A_423, A_424))) | ~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', A_423)), A_424) | ~r1_tarski(A_423, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_566, c_325, c_603])).
% 6.75/2.42  tff(c_195, plain, (![A_76, B_77, C_78, D_79]: (v1_funct_1(k2_partfun1(A_76, B_77, C_78, D_79)) | ~m1_subset_1(C_78, k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))) | ~v1_funct_1(C_78))), inference(cnfTransformation, [status(thm)], [f_98])).
% 6.75/2.42  tff(c_197, plain, (![D_79]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_79)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_58, c_195])).
% 6.75/2.42  tff(c_204, plain, (![D_79]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_79)))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_197])).
% 6.75/2.42  tff(c_52, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2') | ~v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_136])).
% 6.75/2.42  tff(c_138, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_52])).
% 6.75/2.42  tff(c_207, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_204, c_138])).
% 6.75/2.42  tff(c_208, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2') | ~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_52])).
% 6.75/2.42  tff(c_234, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitLeft, [status(thm)], [c_208])).
% 6.75/2.42  tff(c_326, plain, (~m1_subset_1(k7_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_324, c_234])).
% 6.75/2.42  tff(c_3597, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_2') | ~r1_tarski('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_3578, c_326])).
% 6.75/2.42  tff(c_3642, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_3597])).
% 6.75/2.42  tff(c_3658, plain, (~v5_relat_1(k7_relat_1('#skF_4', '#skF_3'), '#skF_2') | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_14, c_3642])).
% 6.75/2.42  tff(c_3662, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_566, c_563, c_3658])).
% 6.75/2.42  tff(c_3663, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_208])).
% 6.75/2.42  tff(c_3806, plain, (~v1_funct_2(k7_relat_1('#skF_4', '#skF_3'), '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3797, c_3663])).
% 6.75/2.42  tff(c_3664, plain, (m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_208])).
% 6.75/2.42  tff(c_3706, plain, (k1_relset_1('#skF_3', '#skF_2', k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))=k1_relat_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_3664, c_3693])).
% 6.75/2.42  tff(c_3799, plain, (k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))=k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_3797, c_3797, c_3706])).
% 6.75/2.42  tff(c_3805, plain, (m1_subset_1(k7_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_3797, c_3664])).
% 6.75/2.42  tff(c_3955, plain, (![B_472, C_473, A_474]: (k1_xboole_0=B_472 | v1_funct_2(C_473, A_474, B_472) | k1_relset_1(A_474, B_472, C_473)!=A_474 | ~m1_subset_1(C_473, k1_zfmisc_1(k2_zfmisc_1(A_474, B_472))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 6.75/2.42  tff(c_3958, plain, (k1_xboole_0='#skF_2' | v1_funct_2(k7_relat_1('#skF_4', '#skF_3'), '#skF_3', '#skF_2') | k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(resolution, [status(thm)], [c_3805, c_3955])).
% 6.75/2.42  tff(c_3972, plain, (k1_xboole_0='#skF_2' | v1_funct_2(k7_relat_1('#skF_4', '#skF_3'), '#skF_3', '#skF_2') | k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_3799, c_3958])).
% 6.75/2.42  tff(c_3973, plain, (k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_3806, c_67, c_3972])).
% 6.75/2.42  tff(c_3982, plain, (~r1_tarski('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_3903, c_3973])).
% 6.75/2.42  tff(c_3986, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_3982])).
% 6.75/2.42  tff(c_3987, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_54])).
% 6.75/2.42  tff(c_8, plain, (![B_3]: (k2_zfmisc_1(k1_xboole_0, B_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.75/2.42  tff(c_4003, plain, (![B_477]: (k2_zfmisc_1('#skF_1', B_477)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3987, c_3987, c_8])).
% 6.75/2.42  tff(c_4007, plain, (v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_4003, c_16])).
% 6.75/2.42  tff(c_4001, plain, (![B_3]: (k2_zfmisc_1('#skF_1', B_3)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3987, c_3987, c_8])).
% 6.75/2.42  tff(c_3988, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_54])).
% 6.75/2.42  tff(c_3993, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3987, c_3988])).
% 6.75/2.42  tff(c_3999, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_3993, c_58])).
% 6.75/2.42  tff(c_4002, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_4001, c_3999])).
% 6.75/2.42  tff(c_4356, plain, (![C_553, B_554, A_555]: (v5_relat_1(C_553, B_554) | ~m1_subset_1(C_553, k1_zfmisc_1(k2_zfmisc_1(A_555, B_554))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 6.75/2.42  tff(c_4408, plain, (![C_559, B_560]: (v5_relat_1(C_559, B_560) | ~m1_subset_1(C_559, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_4001, c_4356])).
% 6.75/2.42  tff(c_4411, plain, (![B_560]: (v5_relat_1('#skF_4', B_560))), inference(resolution, [status(thm)], [c_4002, c_4408])).
% 6.75/2.42  tff(c_4310, plain, (![B_537, A_538]: (v1_relat_1(B_537) | ~m1_subset_1(B_537, k1_zfmisc_1(A_538)) | ~v1_relat_1(A_538))), inference(cnfTransformation, [status(thm)], [f_42])).
% 6.75/2.42  tff(c_4313, plain, (v1_relat_1('#skF_4') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_4002, c_4310])).
% 6.75/2.42  tff(c_4316, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4007, c_4313])).
% 6.75/2.42  tff(c_6, plain, (![A_2]: (k2_zfmisc_1(A_2, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.75/2.42  tff(c_4012, plain, (![A_2]: (k2_zfmisc_1(A_2, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3987, c_3987, c_6])).
% 6.75/2.42  tff(c_4318, plain, (![C_541, A_542, B_543]: (v4_relat_1(C_541, A_542) | ~m1_subset_1(C_541, k1_zfmisc_1(k2_zfmisc_1(A_542, B_543))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 6.75/2.42  tff(c_4326, plain, (![C_546, A_547]: (v4_relat_1(C_546, A_547) | ~m1_subset_1(C_546, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_4012, c_4318])).
% 6.75/2.42  tff(c_4330, plain, (![A_548]: (v4_relat_1('#skF_4', A_548))), inference(resolution, [status(thm)], [c_4002, c_4326])).
% 6.75/2.42  tff(c_18, plain, (![B_12, A_11]: (k7_relat_1(B_12, A_11)=B_12 | ~v4_relat_1(B_12, A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_56])).
% 6.75/2.42  tff(c_4333, plain, (![A_548]: (k7_relat_1('#skF_4', A_548)='#skF_4' | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_4330, c_18])).
% 6.75/2.42  tff(c_4336, plain, (![A_548]: (k7_relat_1('#skF_4', A_548)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4316, c_4333])).
% 6.75/2.42  tff(c_4753, plain, (![A_616, B_617, C_618, D_619]: (k2_partfun1(A_616, B_617, C_618, D_619)=k7_relat_1(C_618, D_619) | ~m1_subset_1(C_618, k1_zfmisc_1(k2_zfmisc_1(A_616, B_617))) | ~v1_funct_1(C_618))), inference(cnfTransformation, [status(thm)], [f_104])).
% 6.75/2.42  tff(c_4815, plain, (![A_638, C_639, D_640]: (k2_partfun1(A_638, '#skF_1', C_639, D_640)=k7_relat_1(C_639, D_640) | ~m1_subset_1(C_639, k1_zfmisc_1('#skF_1')) | ~v1_funct_1(C_639))), inference(superposition, [status(thm), theory('equality')], [c_4012, c_4753])).
% 6.75/2.42  tff(c_4819, plain, (![A_638, D_640]: (k2_partfun1(A_638, '#skF_1', '#skF_4', D_640)=k7_relat_1('#skF_4', D_640) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_4002, c_4815])).
% 6.75/2.42  tff(c_4823, plain, (![A_638, D_640]: (k2_partfun1(A_638, '#skF_1', '#skF_4', D_640)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_4336, c_4819])).
% 6.75/2.42  tff(c_4778, plain, (![B_630, C_631, D_632]: (k2_partfun1('#skF_1', B_630, C_631, D_632)=k7_relat_1(C_631, D_632) | ~m1_subset_1(C_631, k1_zfmisc_1('#skF_1')) | ~v1_funct_1(C_631))), inference(superposition, [status(thm), theory('equality')], [c_4001, c_4753])).
% 6.75/2.42  tff(c_4782, plain, (![B_630, D_632]: (k2_partfun1('#skF_1', B_630, '#skF_4', D_632)=k7_relat_1('#skF_4', D_632) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_4002, c_4778])).
% 6.75/2.42  tff(c_4786, plain, (![B_630, D_632]: (k2_partfun1('#skF_1', B_630, '#skF_4', D_632)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_4336, c_4782])).
% 6.75/2.42  tff(c_4600, plain, (![A_588, B_589, C_590, D_591]: (v1_funct_1(k2_partfun1(A_588, B_589, C_590, D_591)) | ~m1_subset_1(C_590, k1_zfmisc_1(k2_zfmisc_1(A_588, B_589))) | ~v1_funct_1(C_590))), inference(cnfTransformation, [status(thm)], [f_98])).
% 6.75/2.42  tff(c_4605, plain, (![A_592, C_593, D_594]: (v1_funct_1(k2_partfun1(A_592, '#skF_1', C_593, D_594)) | ~m1_subset_1(C_593, k1_zfmisc_1('#skF_1')) | ~v1_funct_1(C_593))), inference(superposition, [status(thm), theory('equality')], [c_4012, c_4600])).
% 6.75/2.42  tff(c_4607, plain, (![A_592, D_594]: (v1_funct_1(k2_partfun1(A_592, '#skF_1', '#skF_4', D_594)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_4002, c_4605])).
% 6.75/2.42  tff(c_4610, plain, (![A_592, D_594]: (v1_funct_1(k2_partfun1(A_592, '#skF_1', '#skF_4', D_594)))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_4607])).
% 6.75/2.42  tff(c_4620, plain, (![B_602, A_603]: (m1_subset_1(B_602, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_602), A_603))) | ~r1_tarski(k2_relat_1(B_602), A_603) | ~v1_funct_1(B_602) | ~v1_relat_1(B_602))), inference(cnfTransformation, [status(thm)], [f_116])).
% 6.75/2.42  tff(c_4672, plain, (![B_608]: (m1_subset_1(B_608, k1_zfmisc_1('#skF_1')) | ~r1_tarski(k2_relat_1(B_608), '#skF_1') | ~v1_funct_1(B_608) | ~v1_relat_1(B_608))), inference(superposition, [status(thm), theory('equality')], [c_4012, c_4620])).
% 6.75/2.42  tff(c_4698, plain, (![B_611]: (m1_subset_1(B_611, k1_zfmisc_1('#skF_1')) | ~v1_funct_1(B_611) | ~v5_relat_1(B_611, '#skF_1') | ~v1_relat_1(B_611))), inference(resolution, [status(thm)], [c_14, c_4672])).
% 6.75/2.42  tff(c_4282, plain, (![A_528, B_529, C_530, D_531]: (v1_funct_1(k2_partfun1(A_528, B_529, C_530, D_531)) | ~m1_subset_1(C_530, k1_zfmisc_1(k2_zfmisc_1(A_528, B_529))) | ~v1_funct_1(C_530))), inference(cnfTransformation, [status(thm)], [f_98])).
% 6.75/2.42  tff(c_4287, plain, (![A_532, C_533, D_534]: (v1_funct_1(k2_partfun1(A_532, '#skF_1', C_533, D_534)) | ~m1_subset_1(C_533, k1_zfmisc_1('#skF_1')) | ~v1_funct_1(C_533))), inference(superposition, [status(thm), theory('equality')], [c_4012, c_4282])).
% 6.75/2.42  tff(c_4289, plain, (![A_532, D_534]: (v1_funct_1(k2_partfun1(A_532, '#skF_1', '#skF_4', D_534)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_4002, c_4287])).
% 6.75/2.42  tff(c_4292, plain, (![A_532, D_534]: (v1_funct_1(k2_partfun1(A_532, '#skF_1', '#skF_4', D_534)))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_4289])).
% 6.75/2.42  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~r1_tarski(A_1, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.75/2.42  tff(c_4032, plain, (![A_479]: (A_479='#skF_1' | ~r1_tarski(A_479, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_3987, c_3987, c_2])).
% 6.75/2.42  tff(c_4036, plain, ('#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_56, c_4032])).
% 6.75/2.42  tff(c_4047, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), k1_zfmisc_1('#skF_1')) | ~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), '#skF_1', '#skF_1') | ~v1_funct_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_4036, c_3993, c_4036, c_4036, c_3993, c_3993, c_4036, c_4012, c_3993, c_3993, c_52])).
% 6.75/2.42  tff(c_4048, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))), inference(splitLeft, [status(thm)], [c_4047])).
% 6.75/2.42  tff(c_4295, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4292, c_4048])).
% 6.75/2.42  tff(c_4296, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), '#skF_1', '#skF_1') | ~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), k1_zfmisc_1('#skF_1'))), inference(splitRight, [status(thm)], [c_4047])).
% 6.75/2.42  tff(c_4344, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), k1_zfmisc_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_4296])).
% 6.75/2.42  tff(c_4716, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1')) | ~v5_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), '#skF_1') | ~v1_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))), inference(resolution, [status(thm)], [c_4698, c_4344])).
% 6.75/2.42  tff(c_4733, plain, (~v5_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), '#skF_1') | ~v1_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_4610, c_4716])).
% 6.75/2.42  tff(c_4770, plain, (~v1_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))), inference(splitLeft, [status(thm)], [c_4733])).
% 6.75/2.42  tff(c_4787, plain, (~v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4786, c_4770])).
% 6.75/2.42  tff(c_4792, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4316, c_4787])).
% 6.75/2.42  tff(c_4793, plain, (~v5_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), '#skF_1')), inference(splitRight, [status(thm)], [c_4733])).
% 6.75/2.42  tff(c_4824, plain, (~v5_relat_1('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4823, c_4793])).
% 6.75/2.42  tff(c_4830, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4411, c_4824])).
% 6.75/2.42  tff(c_4832, plain, (m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), k1_zfmisc_1('#skF_1'))), inference(splitRight, [status(thm)], [c_4296])).
% 6.75/2.42  tff(c_4837, plain, (v1_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1')) | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_4832, c_10])).
% 6.75/2.42  tff(c_4841, plain, (v1_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_4007, c_4837])).
% 6.75/2.42  tff(c_4297, plain, (v1_funct_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))), inference(splitRight, [status(thm)], [c_4047])).
% 6.75/2.42  tff(c_4860, plain, (![C_645, B_646, A_647]: (v5_relat_1(C_645, B_646) | ~m1_subset_1(C_645, k1_zfmisc_1(k2_zfmisc_1(A_647, B_646))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 6.75/2.42  tff(c_4914, plain, (![C_651, B_652]: (v5_relat_1(C_651, B_652) | ~m1_subset_1(C_651, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_4001, c_4860])).
% 6.75/2.42  tff(c_4920, plain, (![B_652]: (v5_relat_1('#skF_4', B_652))), inference(resolution, [status(thm)], [c_4002, c_4914])).
% 6.75/2.42  tff(c_4867, plain, (![C_648]: (v5_relat_1(C_648, '#skF_1') | ~m1_subset_1(C_648, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_4012, c_4860])).
% 6.75/2.42  tff(c_4875, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_4002, c_4867])).
% 6.75/2.42  tff(c_4849, plain, (![B_642, A_643]: (r1_tarski(k2_relat_1(B_642), A_643) | ~v5_relat_1(B_642, A_643) | ~v1_relat_1(B_642))), inference(cnfTransformation, [status(thm)], [f_48])).
% 6.75/2.42  tff(c_4031, plain, (![A_1]: (A_1='#skF_1' | ~r1_tarski(A_1, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_3987, c_3987, c_2])).
% 6.75/2.42  tff(c_4858, plain, (![B_642]: (k2_relat_1(B_642)='#skF_1' | ~v5_relat_1(B_642, '#skF_1') | ~v1_relat_1(B_642))), inference(resolution, [status(thm)], [c_4849, c_4031])).
% 6.75/2.42  tff(c_4878, plain, (k2_relat_1('#skF_4')='#skF_1' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_4875, c_4858])).
% 6.75/2.42  tff(c_4881, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_4316, c_4878])).
% 6.75/2.42  tff(c_4885, plain, (![A_7]: (r1_tarski('#skF_1', A_7) | ~v5_relat_1('#skF_4', A_7) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_4881, c_14])).
% 6.75/2.42  tff(c_4892, plain, (![A_7]: (r1_tarski('#skF_1', A_7) | ~v5_relat_1('#skF_4', A_7))), inference(demodulation, [status(thm), theory('equality')], [c_4316, c_4885])).
% 6.75/2.42  tff(c_4923, plain, (![A_7]: (r1_tarski('#skF_1', A_7))), inference(demodulation, [status(thm), theory('equality')], [c_4920, c_4892])).
% 6.75/2.42  tff(c_4874, plain, (v5_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), '#skF_1')), inference(resolution, [status(thm)], [c_4832, c_4867])).
% 6.75/2.42  tff(c_4945, plain, (k2_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))='#skF_1' | ~v1_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))), inference(resolution, [status(thm)], [c_4874, c_4858])).
% 6.75/2.42  tff(c_4948, plain, (k2_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_4841, c_4945])).
% 6.75/2.42  tff(c_4321, plain, (![C_541, A_2]: (v4_relat_1(C_541, A_2) | ~m1_subset_1(C_541, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_4012, c_4318])).
% 6.75/2.42  tff(c_4842, plain, (![A_641]: (v4_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), A_641))), inference(resolution, [status(thm)], [c_4832, c_4321])).
% 6.75/2.42  tff(c_4845, plain, (![A_641]: (k7_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), A_641)=k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1') | ~v1_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1')))), inference(resolution, [status(thm)], [c_4842, c_18])).
% 6.75/2.42  tff(c_5064, plain, (![A_670]: (k7_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), A_670)=k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_4841, c_4845])).
% 6.75/2.42  tff(c_4973, plain, (![B_656, A_657]: (k1_relat_1(k7_relat_1(B_656, A_657))=A_657 | ~r1_tarski(A_657, k1_relat_1(B_656)) | ~v1_relat_1(B_656))), inference(cnfTransformation, [status(thm)], [f_62])).
% 6.75/2.42  tff(c_4982, plain, (![B_656]: (k1_relat_1(k7_relat_1(B_656, '#skF_1'))='#skF_1' | ~v1_relat_1(B_656))), inference(resolution, [status(thm)], [c_4923, c_4973])).
% 6.75/2.42  tff(c_5070, plain, (k1_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))='#skF_1' | ~v1_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_5064, c_4982])).
% 6.75/2.42  tff(c_5075, plain, (k1_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_4841, c_5070])).
% 6.75/2.42  tff(c_5105, plain, (![B_674, A_675]: (v1_funct_2(B_674, k1_relat_1(B_674), A_675) | ~r1_tarski(k2_relat_1(B_674), A_675) | ~v1_funct_1(B_674) | ~v1_relat_1(B_674))), inference(cnfTransformation, [status(thm)], [f_116])).
% 6.75/2.42  tff(c_5111, plain, (![A_675]: (v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), '#skF_1', A_675) | ~r1_tarski(k2_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1')), A_675) | ~v1_funct_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1')) | ~v1_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_5075, c_5105])).
% 6.75/2.42  tff(c_5120, plain, (![A_675]: (v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), '#skF_1', A_675))), inference(demodulation, [status(thm), theory('equality')], [c_4841, c_4297, c_4923, c_4948, c_5111])).
% 6.75/2.42  tff(c_4831, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), '#skF_1', '#skF_1')), inference(splitRight, [status(thm)], [c_4296])).
% 6.75/2.42  tff(c_5125, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5120, c_4831])).
% 6.75/2.42  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.75/2.42  
% 6.75/2.42  Inference rules
% 6.75/2.42  ----------------------
% 6.75/2.42  #Ref     : 0
% 6.75/2.42  #Sup     : 1159
% 6.75/2.42  #Fact    : 0
% 6.75/2.42  #Define  : 0
% 6.75/2.42  #Split   : 16
% 6.75/2.42  #Chain   : 0
% 6.75/2.42  #Close   : 0
% 6.75/2.42  
% 6.75/2.42  Ordering : KBO
% 6.75/2.42  
% 6.75/2.42  Simplification rules
% 6.75/2.42  ----------------------
% 6.75/2.42  #Subsume      : 154
% 6.75/2.42  #Demod        : 1152
% 6.75/2.42  #Tautology    : 521
% 6.75/2.42  #SimpNegUnit  : 15
% 6.75/2.42  #BackRed      : 41
% 6.75/2.42  
% 6.75/2.42  #Partial instantiations: 0
% 6.75/2.42  #Strategies tried      : 1
% 6.75/2.42  
% 6.75/2.42  Timing (in seconds)
% 6.75/2.42  ----------------------
% 6.75/2.43  Preprocessing        : 0.34
% 6.75/2.43  Parsing              : 0.19
% 6.75/2.43  CNF conversion       : 0.02
% 6.75/2.43  Main loop            : 1.25
% 6.75/2.43  Inferencing          : 0.44
% 6.75/2.43  Reduction            : 0.46
% 6.75/2.43  Demodulation         : 0.34
% 6.75/2.43  BG Simplification    : 0.05
% 6.75/2.43  Subsumption          : 0.20
% 6.75/2.43  Abstraction          : 0.05
% 6.75/2.43  MUC search           : 0.00
% 6.75/2.43  Cooper               : 0.00
% 6.75/2.43  Total                : 1.67
% 6.75/2.43  Index Insertion      : 0.00
% 6.75/2.43  Index Deletion       : 0.00
% 6.75/2.43  Index Matching       : 0.00
% 6.75/2.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
