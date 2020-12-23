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
% DateTime   : Thu Dec  3 09:57:58 EST 2020

% Result     : Theorem 2.62s
% Output     : CNFRefutation 2.81s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 456 expanded)
%              Number of leaves         :   29 ( 156 expanded)
%              Depth                    :   11
%              Number of atoms          :  130 ( 918 expanded)
%              Number of equality atoms :   43 ( 260 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k8_setfam_1 > k6_setfam_1 > k4_xboole_0 > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k8_setfam_1,type,(
    k8_setfam_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k6_setfam_1,type,(
    k6_setfam_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_95,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
           => ( r1_tarski(B,C)
             => r1_tarski(k8_setfam_1(A,C),k8_setfam_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_setfam_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k6_setfam_1(A,B) = k1_setfam_1(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( ( B != k1_xboole_0
         => k8_setfam_1(A,B) = k6_setfam_1(A,B) )
        & ( B = k1_xboole_0
         => k8_setfam_1(A,B) = A ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_setfam_1)).

tff(f_43,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_31,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_41,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k8_setfam_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_setfam_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => ( A = k1_xboole_0
        | r1_tarski(k1_setfam_1(B),k1_setfam_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_setfam_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_32,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_24,plain,(
    ! [A_17,B_18] :
      ( m1_subset_1(A_17,k1_zfmisc_1(B_18))
      | ~ r1_tarski(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_97,plain,(
    ! [B_39,A_40] :
      ( v1_xboole_0(B_39)
      | ~ m1_subset_1(B_39,k1_zfmisc_1(A_40))
      | ~ v1_xboole_0(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_117,plain,(
    ! [A_41,B_42] :
      ( v1_xboole_0(A_41)
      | ~ v1_xboole_0(B_42)
      | ~ r1_tarski(A_41,B_42) ) ),
    inference(resolution,[status(thm)],[c_24,c_97])).

tff(c_134,plain,
    ( v1_xboole_0('#skF_2')
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_117])).

tff(c_135,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_134])).

tff(c_36,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_136,plain,(
    ! [A_43,B_44] :
      ( k6_setfam_1(A_43,B_44) = k1_setfam_1(B_44)
      | ~ m1_subset_1(B_44,k1_zfmisc_1(k1_zfmisc_1(A_43))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_152,plain,(
    k6_setfam_1('#skF_1','#skF_2') = k1_setfam_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_136])).

tff(c_298,plain,(
    ! [A_68,B_69] :
      ( k8_setfam_1(A_68,B_69) = k6_setfam_1(A_68,B_69)
      | k1_xboole_0 = B_69
      | ~ m1_subset_1(B_69,k1_zfmisc_1(k1_zfmisc_1(A_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_313,plain,
    ( k8_setfam_1('#skF_1','#skF_2') = k6_setfam_1('#skF_1','#skF_2')
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_36,c_298])).

tff(c_326,plain,
    ( k8_setfam_1('#skF_1','#skF_2') = k1_setfam_1('#skF_2')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_313])).

tff(c_332,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_326])).

tff(c_34,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_153,plain,(
    k6_setfam_1('#skF_1','#skF_3') = k1_setfam_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_136])).

tff(c_316,plain,
    ( k8_setfam_1('#skF_1','#skF_3') = k6_setfam_1('#skF_1','#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_34,c_298])).

tff(c_328,plain,
    ( k8_setfam_1('#skF_1','#skF_3') = k1_setfam_1('#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_153,c_316])).

tff(c_348,plain,
    ( k8_setfam_1('#skF_1','#skF_3') = k1_setfam_1('#skF_3')
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_332,c_328])).

tff(c_349,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_348])).

tff(c_10,plain,(
    ! [A_7] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_62,plain,(
    ! [A_32,B_33] :
      ( r1_tarski(A_32,B_33)
      | ~ m1_subset_1(A_32,k1_zfmisc_1(B_33)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_74,plain,(
    ! [A_7] : r1_tarski(k1_xboole_0,A_7) ),
    inference(resolution,[status(thm)],[c_10,c_62])).

tff(c_4,plain,(
    ! [A_2] : k4_xboole_0(k1_xboole_0,A_2) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_57,plain,(
    ! [A_29,B_30] : r1_xboole_0(k4_xboole_0(A_29,B_30),B_30) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_60,plain,(
    ! [A_2] : r1_xboole_0(k1_xboole_0,A_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_57])).

tff(c_81,plain,(
    ! [B_37,A_38] :
      ( ~ r1_xboole_0(B_37,A_38)
      | ~ r1_tarski(B_37,A_38)
      | v1_xboole_0(B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_84,plain,(
    ! [A_2] :
      ( ~ r1_tarski(k1_xboole_0,A_2)
      | v1_xboole_0(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_60,c_81])).

tff(c_90,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_84])).

tff(c_337,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_332,c_90])).

tff(c_350,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_349,c_337])).

tff(c_360,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_135,c_350])).

tff(c_361,plain,(
    k8_setfam_1('#skF_1','#skF_3') = k1_setfam_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_348])).

tff(c_14,plain,(
    ! [A_11] :
      ( k8_setfam_1(A_11,k1_xboole_0) = A_11
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(A_11))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_38,plain,(
    ! [A_11] : k8_setfam_1(A_11,k1_xboole_0) = A_11 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_14])).

tff(c_340,plain,(
    ! [A_11] : k8_setfam_1(A_11,'#skF_2') = A_11 ),
    inference(demodulation,[status(thm),theory(equality)],[c_332,c_38])).

tff(c_30,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_1','#skF_3'),k8_setfam_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_382,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_1','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_340,c_30])).

tff(c_446,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_361,c_382])).

tff(c_18,plain,(
    ! [A_13,B_14] :
      ( m1_subset_1(k8_setfam_1(A_13,B_14),k1_zfmisc_1(A_13))
      | ~ m1_subset_1(B_14,k1_zfmisc_1(k1_zfmisc_1(A_13))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_450,plain,
    ( m1_subset_1(k1_setfam_1('#skF_3'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_361,c_18])).

tff(c_454,plain,(
    m1_subset_1(k1_setfam_1('#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_450])).

tff(c_22,plain,(
    ! [A_17,B_18] :
      ( r1_tarski(A_17,B_18)
      | ~ m1_subset_1(A_17,k1_zfmisc_1(B_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_466,plain,(
    r1_tarski(k1_setfam_1('#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_454,c_22])).

tff(c_472,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_446,c_466])).

tff(c_474,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_326])).

tff(c_28,plain,(
    ! [B_23,A_22] :
      ( r1_tarski(k1_setfam_1(B_23),k1_setfam_1(A_22))
      | k1_xboole_0 = A_22
      | ~ r1_tarski(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_500,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_328])).

tff(c_506,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_500,c_90])).

tff(c_514,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_135,c_506])).

tff(c_515,plain,(
    k8_setfam_1('#skF_1','#skF_3') = k1_setfam_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_328])).

tff(c_473,plain,(
    k8_setfam_1('#skF_1','#skF_2') = k1_setfam_1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_326])).

tff(c_475,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_1','#skF_3'),k1_setfam_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_473,c_30])).

tff(c_517,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_3'),k1_setfam_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_515,c_475])).

tff(c_529,plain,
    ( k1_xboole_0 = '#skF_2'
    | ~ r1_tarski('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_517])).

tff(c_532,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_529])).

tff(c_534,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_474,c_532])).

tff(c_536,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_134])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_544,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_536,c_2])).

tff(c_535,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_134])).

tff(c_540,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_535,c_2])).

tff(c_557,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_544,c_540])).

tff(c_549,plain,(
    ! [A_7] : m1_subset_1('#skF_2',k1_zfmisc_1(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_540,c_10])).

tff(c_615,plain,(
    ! [A_7] : m1_subset_1('#skF_3',k1_zfmisc_1(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_557,c_549])).

tff(c_548,plain,(
    ! [A_11] : k8_setfam_1(A_11,'#skF_2') = A_11 ),
    inference(demodulation,[status(thm),theory(equality)],[c_540,c_38])).

tff(c_628,plain,(
    ! [A_11] : k8_setfam_1(A_11,'#skF_3') = A_11 ),
    inference(demodulation,[status(thm),theory(equality)],[c_557,c_548])).

tff(c_679,plain,(
    ! [A_102,B_103] :
      ( m1_subset_1(k8_setfam_1(A_102,B_103),k1_zfmisc_1(A_102))
      | ~ m1_subset_1(B_103,k1_zfmisc_1(k1_zfmisc_1(A_102))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_694,plain,(
    ! [A_11] :
      ( m1_subset_1(A_11,k1_zfmisc_1(A_11))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(A_11))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_628,c_679])).

tff(c_701,plain,(
    ! [A_104] : m1_subset_1(A_104,k1_zfmisc_1(A_104)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_615,c_694])).

tff(c_717,plain,(
    ! [A_104] : r1_tarski(A_104,A_104) ),
    inference(resolution,[status(thm)],[c_701,c_22])).

tff(c_564,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_1','#skF_3'),k8_setfam_1('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_557,c_30])).

tff(c_629,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_628,c_628,c_564])).

tff(c_720,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_717,c_629])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:34:39 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.62/1.35  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.62/1.36  
% 2.62/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.62/1.36  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k8_setfam_1 > k6_setfam_1 > k4_xboole_0 > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.62/1.36  
% 2.62/1.36  %Foreground sorts:
% 2.62/1.36  
% 2.62/1.36  
% 2.62/1.36  %Background operators:
% 2.62/1.36  
% 2.62/1.36  
% 2.62/1.36  %Foreground operators:
% 2.62/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.62/1.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.62/1.36  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.62/1.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.62/1.36  tff(k8_setfam_1, type, k8_setfam_1: ($i * $i) > $i).
% 2.62/1.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.62/1.36  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.62/1.36  tff('#skF_2', type, '#skF_2': $i).
% 2.62/1.36  tff('#skF_3', type, '#skF_3': $i).
% 2.62/1.36  tff('#skF_1', type, '#skF_1': $i).
% 2.62/1.36  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.62/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.62/1.36  tff(k6_setfam_1, type, k6_setfam_1: ($i * $i) > $i).
% 2.62/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.62/1.36  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.62/1.36  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.62/1.36  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.62/1.36  
% 2.81/1.38  tff(f_95, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => (r1_tarski(B, C) => r1_tarski(k8_setfam_1(A, C), k8_setfam_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_setfam_1)).
% 2.81/1.38  tff(f_73, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.81/1.38  tff(f_50, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 2.81/1.38  tff(f_69, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k6_setfam_1(A, B) = k1_setfam_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_setfam_1)).
% 2.81/1.38  tff(f_61, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => ((~(B = k1_xboole_0) => (k8_setfam_1(A, B) = k6_setfam_1(A, B))) & ((B = k1_xboole_0) => (k8_setfam_1(A, B) = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_setfam_1)).
% 2.81/1.38  tff(f_43, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.81/1.38  tff(f_31, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 2.81/1.38  tff(f_41, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 2.81/1.38  tff(f_39, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_xboole_1)).
% 2.81/1.38  tff(f_65, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k8_setfam_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_setfam_1)).
% 2.81/1.38  tff(f_85, axiom, (![A, B]: (r1_tarski(A, B) => ((A = k1_xboole_0) | r1_tarski(k1_setfam_1(B), k1_setfam_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_setfam_1)).
% 2.81/1.38  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.81/1.38  tff(c_32, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.81/1.38  tff(c_24, plain, (![A_17, B_18]: (m1_subset_1(A_17, k1_zfmisc_1(B_18)) | ~r1_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.81/1.38  tff(c_97, plain, (![B_39, A_40]: (v1_xboole_0(B_39) | ~m1_subset_1(B_39, k1_zfmisc_1(A_40)) | ~v1_xboole_0(A_40))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.81/1.38  tff(c_117, plain, (![A_41, B_42]: (v1_xboole_0(A_41) | ~v1_xboole_0(B_42) | ~r1_tarski(A_41, B_42))), inference(resolution, [status(thm)], [c_24, c_97])).
% 2.81/1.38  tff(c_134, plain, (v1_xboole_0('#skF_2') | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_32, c_117])).
% 2.81/1.38  tff(c_135, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_134])).
% 2.81/1.38  tff(c_36, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.81/1.38  tff(c_136, plain, (![A_43, B_44]: (k6_setfam_1(A_43, B_44)=k1_setfam_1(B_44) | ~m1_subset_1(B_44, k1_zfmisc_1(k1_zfmisc_1(A_43))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.81/1.38  tff(c_152, plain, (k6_setfam_1('#skF_1', '#skF_2')=k1_setfam_1('#skF_2')), inference(resolution, [status(thm)], [c_36, c_136])).
% 2.81/1.38  tff(c_298, plain, (![A_68, B_69]: (k8_setfam_1(A_68, B_69)=k6_setfam_1(A_68, B_69) | k1_xboole_0=B_69 | ~m1_subset_1(B_69, k1_zfmisc_1(k1_zfmisc_1(A_68))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.81/1.38  tff(c_313, plain, (k8_setfam_1('#skF_1', '#skF_2')=k6_setfam_1('#skF_1', '#skF_2') | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_36, c_298])).
% 2.81/1.38  tff(c_326, plain, (k8_setfam_1('#skF_1', '#skF_2')=k1_setfam_1('#skF_2') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_152, c_313])).
% 2.81/1.38  tff(c_332, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_326])).
% 2.81/1.38  tff(c_34, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.81/1.38  tff(c_153, plain, (k6_setfam_1('#skF_1', '#skF_3')=k1_setfam_1('#skF_3')), inference(resolution, [status(thm)], [c_34, c_136])).
% 2.81/1.38  tff(c_316, plain, (k8_setfam_1('#skF_1', '#skF_3')=k6_setfam_1('#skF_1', '#skF_3') | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_34, c_298])).
% 2.81/1.38  tff(c_328, plain, (k8_setfam_1('#skF_1', '#skF_3')=k1_setfam_1('#skF_3') | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_153, c_316])).
% 2.81/1.38  tff(c_348, plain, (k8_setfam_1('#skF_1', '#skF_3')=k1_setfam_1('#skF_3') | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_332, c_328])).
% 2.81/1.38  tff(c_349, plain, ('#skF_2'='#skF_3'), inference(splitLeft, [status(thm)], [c_348])).
% 2.81/1.38  tff(c_10, plain, (![A_7]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.81/1.38  tff(c_62, plain, (![A_32, B_33]: (r1_tarski(A_32, B_33) | ~m1_subset_1(A_32, k1_zfmisc_1(B_33)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.81/1.38  tff(c_74, plain, (![A_7]: (r1_tarski(k1_xboole_0, A_7))), inference(resolution, [status(thm)], [c_10, c_62])).
% 2.81/1.38  tff(c_4, plain, (![A_2]: (k4_xboole_0(k1_xboole_0, A_2)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.81/1.38  tff(c_57, plain, (![A_29, B_30]: (r1_xboole_0(k4_xboole_0(A_29, B_30), B_30))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.81/1.38  tff(c_60, plain, (![A_2]: (r1_xboole_0(k1_xboole_0, A_2))), inference(superposition, [status(thm), theory('equality')], [c_4, c_57])).
% 2.81/1.38  tff(c_81, plain, (![B_37, A_38]: (~r1_xboole_0(B_37, A_38) | ~r1_tarski(B_37, A_38) | v1_xboole_0(B_37))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.81/1.38  tff(c_84, plain, (![A_2]: (~r1_tarski(k1_xboole_0, A_2) | v1_xboole_0(k1_xboole_0))), inference(resolution, [status(thm)], [c_60, c_81])).
% 2.81/1.38  tff(c_90, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_74, c_84])).
% 2.81/1.38  tff(c_337, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_332, c_90])).
% 2.81/1.38  tff(c_350, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_349, c_337])).
% 2.81/1.38  tff(c_360, plain, $false, inference(negUnitSimplification, [status(thm)], [c_135, c_350])).
% 2.81/1.38  tff(c_361, plain, (k8_setfam_1('#skF_1', '#skF_3')=k1_setfam_1('#skF_3')), inference(splitRight, [status(thm)], [c_348])).
% 2.81/1.38  tff(c_14, plain, (![A_11]: (k8_setfam_1(A_11, k1_xboole_0)=A_11 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1(A_11))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.81/1.38  tff(c_38, plain, (![A_11]: (k8_setfam_1(A_11, k1_xboole_0)=A_11)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_14])).
% 2.81/1.38  tff(c_340, plain, (![A_11]: (k8_setfam_1(A_11, '#skF_2')=A_11)), inference(demodulation, [status(thm), theory('equality')], [c_332, c_38])).
% 2.81/1.38  tff(c_30, plain, (~r1_tarski(k8_setfam_1('#skF_1', '#skF_3'), k8_setfam_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.81/1.38  tff(c_382, plain, (~r1_tarski(k8_setfam_1('#skF_1', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_340, c_30])).
% 2.81/1.38  tff(c_446, plain, (~r1_tarski(k1_setfam_1('#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_361, c_382])).
% 2.81/1.38  tff(c_18, plain, (![A_13, B_14]: (m1_subset_1(k8_setfam_1(A_13, B_14), k1_zfmisc_1(A_13)) | ~m1_subset_1(B_14, k1_zfmisc_1(k1_zfmisc_1(A_13))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.81/1.38  tff(c_450, plain, (m1_subset_1(k1_setfam_1('#skF_3'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_361, c_18])).
% 2.81/1.38  tff(c_454, plain, (m1_subset_1(k1_setfam_1('#skF_3'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_450])).
% 2.81/1.38  tff(c_22, plain, (![A_17, B_18]: (r1_tarski(A_17, B_18) | ~m1_subset_1(A_17, k1_zfmisc_1(B_18)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.81/1.38  tff(c_466, plain, (r1_tarski(k1_setfam_1('#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_454, c_22])).
% 2.81/1.38  tff(c_472, plain, $false, inference(negUnitSimplification, [status(thm)], [c_446, c_466])).
% 2.81/1.38  tff(c_474, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_326])).
% 2.81/1.38  tff(c_28, plain, (![B_23, A_22]: (r1_tarski(k1_setfam_1(B_23), k1_setfam_1(A_22)) | k1_xboole_0=A_22 | ~r1_tarski(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.81/1.38  tff(c_500, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_328])).
% 2.81/1.38  tff(c_506, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_500, c_90])).
% 2.81/1.38  tff(c_514, plain, $false, inference(negUnitSimplification, [status(thm)], [c_135, c_506])).
% 2.81/1.38  tff(c_515, plain, (k8_setfam_1('#skF_1', '#skF_3')=k1_setfam_1('#skF_3')), inference(splitRight, [status(thm)], [c_328])).
% 2.81/1.38  tff(c_473, plain, (k8_setfam_1('#skF_1', '#skF_2')=k1_setfam_1('#skF_2')), inference(splitRight, [status(thm)], [c_326])).
% 2.81/1.38  tff(c_475, plain, (~r1_tarski(k8_setfam_1('#skF_1', '#skF_3'), k1_setfam_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_473, c_30])).
% 2.81/1.38  tff(c_517, plain, (~r1_tarski(k1_setfam_1('#skF_3'), k1_setfam_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_515, c_475])).
% 2.81/1.38  tff(c_529, plain, (k1_xboole_0='#skF_2' | ~r1_tarski('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_28, c_517])).
% 2.81/1.38  tff(c_532, plain, (k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_529])).
% 2.81/1.38  tff(c_534, plain, $false, inference(negUnitSimplification, [status(thm)], [c_474, c_532])).
% 2.81/1.38  tff(c_536, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_134])).
% 2.81/1.38  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.81/1.38  tff(c_544, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_536, c_2])).
% 2.81/1.38  tff(c_535, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_134])).
% 2.81/1.38  tff(c_540, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_535, c_2])).
% 2.81/1.38  tff(c_557, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_544, c_540])).
% 2.81/1.38  tff(c_549, plain, (![A_7]: (m1_subset_1('#skF_2', k1_zfmisc_1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_540, c_10])).
% 2.81/1.38  tff(c_615, plain, (![A_7]: (m1_subset_1('#skF_3', k1_zfmisc_1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_557, c_549])).
% 2.81/1.38  tff(c_548, plain, (![A_11]: (k8_setfam_1(A_11, '#skF_2')=A_11)), inference(demodulation, [status(thm), theory('equality')], [c_540, c_38])).
% 2.81/1.38  tff(c_628, plain, (![A_11]: (k8_setfam_1(A_11, '#skF_3')=A_11)), inference(demodulation, [status(thm), theory('equality')], [c_557, c_548])).
% 2.81/1.38  tff(c_679, plain, (![A_102, B_103]: (m1_subset_1(k8_setfam_1(A_102, B_103), k1_zfmisc_1(A_102)) | ~m1_subset_1(B_103, k1_zfmisc_1(k1_zfmisc_1(A_102))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.81/1.38  tff(c_694, plain, (![A_11]: (m1_subset_1(A_11, k1_zfmisc_1(A_11)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(A_11))))), inference(superposition, [status(thm), theory('equality')], [c_628, c_679])).
% 2.81/1.38  tff(c_701, plain, (![A_104]: (m1_subset_1(A_104, k1_zfmisc_1(A_104)))), inference(demodulation, [status(thm), theory('equality')], [c_615, c_694])).
% 2.81/1.38  tff(c_717, plain, (![A_104]: (r1_tarski(A_104, A_104))), inference(resolution, [status(thm)], [c_701, c_22])).
% 2.81/1.38  tff(c_564, plain, (~r1_tarski(k8_setfam_1('#skF_1', '#skF_3'), k8_setfam_1('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_557, c_30])).
% 2.81/1.38  tff(c_629, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_628, c_628, c_564])).
% 2.81/1.38  tff(c_720, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_717, c_629])).
% 2.81/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.81/1.38  
% 2.81/1.38  Inference rules
% 2.81/1.38  ----------------------
% 2.81/1.38  #Ref     : 0
% 2.81/1.38  #Sup     : 136
% 2.81/1.38  #Fact    : 0
% 2.81/1.38  #Define  : 0
% 2.81/1.38  #Split   : 7
% 2.81/1.38  #Chain   : 0
% 2.81/1.38  #Close   : 0
% 2.81/1.38  
% 2.81/1.38  Ordering : KBO
% 2.81/1.38  
% 2.81/1.38  Simplification rules
% 2.81/1.38  ----------------------
% 2.81/1.38  #Subsume      : 8
% 2.81/1.38  #Demod        : 119
% 2.81/1.38  #Tautology    : 79
% 2.81/1.38  #SimpNegUnit  : 4
% 2.81/1.38  #BackRed      : 51
% 2.81/1.38  
% 2.81/1.38  #Partial instantiations: 0
% 2.81/1.38  #Strategies tried      : 1
% 2.81/1.38  
% 2.81/1.38  Timing (in seconds)
% 2.81/1.38  ----------------------
% 2.81/1.38  Preprocessing        : 0.31
% 2.81/1.38  Parsing              : 0.17
% 2.81/1.38  CNF conversion       : 0.02
% 2.81/1.38  Main loop            : 0.31
% 2.81/1.38  Inferencing          : 0.11
% 2.81/1.38  Reduction            : 0.10
% 2.81/1.38  Demodulation         : 0.07
% 2.81/1.38  BG Simplification    : 0.02
% 2.81/1.38  Subsumption          : 0.04
% 2.81/1.38  Abstraction          : 0.02
% 2.81/1.38  MUC search           : 0.00
% 2.81/1.38  Cooper               : 0.00
% 2.81/1.38  Total                : 0.66
% 2.81/1.38  Index Insertion      : 0.00
% 2.81/1.38  Index Deletion       : 0.00
% 2.81/1.38  Index Matching       : 0.00
% 2.81/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
