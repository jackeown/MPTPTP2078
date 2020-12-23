%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:11 EST 2020

% Result     : Theorem 3.16s
% Output     : CNFRefutation 3.16s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 194 expanded)
%              Number of leaves         :   41 (  83 expanded)
%              Depth                    :   13
%              Number of atoms          :  148 ( 302 expanded)
%              Number of equality atoms :   59 ( 130 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_xboole_0 > v1_relat_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k6_subset_1 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k4_relat_1 > k3_tarski > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_109,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( k5_relat_1(k1_xboole_0,A) = k1_xboole_0
          & k5_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_58,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_30,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_50,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_32,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_102,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_92,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k2_relat_1(A),k1_relat_1(B))
           => k1_relat_1(k5_relat_1(A,B)) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).

tff(f_76,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_xboole_0(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relat_1)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

tff(f_28,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_34,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_52,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_83,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k4_relat_1(k6_subset_1(A,B)) = k6_subset_1(k4_relat_1(A),k4_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_relat_1)).

tff(f_72,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k4_relat_1(k4_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).

tff(f_99,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k4_relat_1(k5_relat_1(A,B)) = k5_relat_1(k4_relat_1(B),k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relat_1)).

tff(c_52,plain,
    ( k5_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0
    | k5_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_101,plain,(
    k5_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_54,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_96,plain,(
    ! [A_48] :
      ( v1_relat_1(A_48)
      | ~ v1_xboole_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_100,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_96])).

tff(c_36,plain,(
    ! [A_31,B_32] :
      ( v1_relat_1(k5_relat_1(A_31,B_32))
      | ~ v1_relat_1(B_32)
      | ~ v1_relat_1(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_6,plain,(
    ! [A_3] : k3_xboole_0(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_26,plain,(
    ! [B_24] : k2_zfmisc_1(k1_xboole_0,B_24) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_8,plain,(
    ! [A_4] : r1_tarski(k1_xboole_0,A_4) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_50,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_48,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_467,plain,(
    ! [A_91,B_92] :
      ( k1_relat_1(k5_relat_1(A_91,B_92)) = k1_relat_1(A_91)
      | ~ r1_tarski(k2_relat_1(A_91),k1_relat_1(B_92))
      | ~ v1_relat_1(B_92)
      | ~ v1_relat_1(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_473,plain,(
    ! [B_92] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_92)) = k1_relat_1(k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k1_relat_1(B_92))
      | ~ v1_relat_1(B_92)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_467])).

tff(c_478,plain,(
    ! [B_93] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_93)) = k1_xboole_0
      | ~ v1_relat_1(B_93) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_8,c_50,c_473])).

tff(c_40,plain,(
    ! [A_34] :
      ( k3_xboole_0(A_34,k2_zfmisc_1(k1_relat_1(A_34),k2_relat_1(A_34))) = A_34
      | ~ v1_relat_1(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_487,plain,(
    ! [B_93] :
      ( k3_xboole_0(k5_relat_1(k1_xboole_0,B_93),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,B_93)))) = k5_relat_1(k1_xboole_0,B_93)
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_93))
      | ~ v1_relat_1(B_93) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_478,c_40])).

tff(c_497,plain,(
    ! [B_94] :
      ( k5_relat_1(k1_xboole_0,B_94) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_94))
      | ~ v1_relat_1(B_94) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_26,c_487])).

tff(c_504,plain,(
    ! [B_32] :
      ( k5_relat_1(k1_xboole_0,B_32) = k1_xboole_0
      | ~ v1_relat_1(B_32)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_36,c_497])).

tff(c_508,plain,(
    ! [B_95] :
      ( k5_relat_1(k1_xboole_0,B_95) = k1_xboole_0
      | ~ v1_relat_1(B_95) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_504])).

tff(c_520,plain,(
    k5_relat_1(k1_xboole_0,'#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_54,c_508])).

tff(c_527,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_101,c_520])).

tff(c_528,plain,(
    k5_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_34,plain,(
    ! [A_30] :
      ( v1_relat_1(k4_relat_1(A_30))
      | ~ v1_relat_1(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_4,plain,(
    ! [A_1] : k2_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_571,plain,(
    ! [A_101,B_102] : k4_xboole_0(A_101,k2_xboole_0(A_101,B_102)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_578,plain,(
    ! [A_1] : k4_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_571])).

tff(c_28,plain,(
    ! [A_25,B_26] : k6_subset_1(A_25,B_26) = k4_xboole_0(A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_42,plain,(
    ! [A_35,B_37] :
      ( k6_subset_1(k4_relat_1(A_35),k4_relat_1(B_37)) = k4_relat_1(k6_subset_1(A_35,B_37))
      | ~ v1_relat_1(B_37)
      | ~ v1_relat_1(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_687,plain,(
    ! [A_124,B_125] :
      ( k4_xboole_0(k4_relat_1(A_124),k4_relat_1(B_125)) = k4_relat_1(k4_xboole_0(A_124,B_125))
      | ~ v1_relat_1(B_125)
      | ~ v1_relat_1(A_124) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_28,c_42])).

tff(c_694,plain,(
    ! [B_125] :
      ( k4_relat_1(k4_xboole_0(B_125,B_125)) = k1_xboole_0
      | ~ v1_relat_1(B_125)
      | ~ v1_relat_1(B_125) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_687,c_578])).

tff(c_709,plain,(
    ! [B_125] :
      ( k4_relat_1(k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(B_125)
      | ~ v1_relat_1(B_125) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_578,c_694])).

tff(c_713,plain,(
    ! [B_126] :
      ( ~ v1_relat_1(B_126)
      | ~ v1_relat_1(B_126) ) ),
    inference(splitLeft,[status(thm)],[c_709])).

tff(c_719,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_100,c_713])).

tff(c_727,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_719])).

tff(c_728,plain,(
    k4_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_709])).

tff(c_812,plain,(
    ! [A_134,B_135] :
      ( k1_relat_1(k5_relat_1(A_134,B_135)) = k1_relat_1(A_134)
      | ~ r1_tarski(k2_relat_1(A_134),k1_relat_1(B_135))
      | ~ v1_relat_1(B_135)
      | ~ v1_relat_1(A_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_818,plain,(
    ! [B_135] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_135)) = k1_relat_1(k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k1_relat_1(B_135))
      | ~ v1_relat_1(B_135)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_812])).

tff(c_823,plain,(
    ! [B_136] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_136)) = k1_xboole_0
      | ~ v1_relat_1(B_136) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_8,c_50,c_818])).

tff(c_832,plain,(
    ! [B_136] :
      ( k3_xboole_0(k5_relat_1(k1_xboole_0,B_136),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,B_136)))) = k5_relat_1(k1_xboole_0,B_136)
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_136))
      | ~ v1_relat_1(B_136) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_823,c_40])).

tff(c_873,plain,(
    ! [B_137] :
      ( k5_relat_1(k1_xboole_0,B_137) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_137))
      | ~ v1_relat_1(B_137) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_26,c_832])).

tff(c_877,plain,(
    ! [B_32] :
      ( k5_relat_1(k1_xboole_0,B_32) = k1_xboole_0
      | ~ v1_relat_1(B_32)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_36,c_873])).

tff(c_886,plain,(
    ! [B_138] :
      ( k5_relat_1(k1_xboole_0,B_138) = k1_xboole_0
      | ~ v1_relat_1(B_138) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_877])).

tff(c_900,plain,(
    ! [A_30] :
      ( k5_relat_1(k1_xboole_0,k4_relat_1(A_30)) = k1_xboole_0
      | ~ v1_relat_1(A_30) ) ),
    inference(resolution,[status(thm)],[c_34,c_886])).

tff(c_38,plain,(
    ! [A_33] :
      ( k4_relat_1(k4_relat_1(A_33)) = A_33
      | ~ v1_relat_1(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_46,plain,(
    ! [B_43,A_41] :
      ( k5_relat_1(k4_relat_1(B_43),k4_relat_1(A_41)) = k4_relat_1(k5_relat_1(A_41,B_43))
      | ~ v1_relat_1(B_43)
      | ~ v1_relat_1(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_741,plain,(
    ! [B_43] :
      ( k5_relat_1(k4_relat_1(B_43),k1_xboole_0) = k4_relat_1(k5_relat_1(k1_xboole_0,B_43))
      | ~ v1_relat_1(B_43)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_728,c_46])).

tff(c_790,plain,(
    ! [B_133] :
      ( k5_relat_1(k4_relat_1(B_133),k1_xboole_0) = k4_relat_1(k5_relat_1(k1_xboole_0,B_133))
      | ~ v1_relat_1(B_133) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_741])).

tff(c_1390,plain,(
    ! [A_153] :
      ( k4_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(A_153))) = k5_relat_1(A_153,k1_xboole_0)
      | ~ v1_relat_1(k4_relat_1(A_153))
      | ~ v1_relat_1(A_153) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_790])).

tff(c_1459,plain,(
    ! [A_30] :
      ( k5_relat_1(A_30,k1_xboole_0) = k4_relat_1(k1_xboole_0)
      | ~ v1_relat_1(k4_relat_1(A_30))
      | ~ v1_relat_1(A_30)
      | ~ v1_relat_1(A_30) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_900,c_1390])).

tff(c_1476,plain,(
    ! [A_154] :
      ( k5_relat_1(A_154,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k4_relat_1(A_154))
      | ~ v1_relat_1(A_154)
      | ~ v1_relat_1(A_154) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_728,c_1459])).

tff(c_1509,plain,(
    ! [A_155] :
      ( k5_relat_1(A_155,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_155) ) ),
    inference(resolution,[status(thm)],[c_34,c_1476])).

tff(c_1530,plain,(
    k5_relat_1('#skF_1',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_54,c_1509])).

tff(c_1541,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_528,c_1530])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:31:56 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.16/1.51  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.16/1.51  
% 3.16/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.16/1.51  %$ r1_tarski > v1_xboole_0 > v1_relat_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k6_subset_1 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k4_relat_1 > k3_tarski > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 3.16/1.51  
% 3.16/1.51  %Foreground sorts:
% 3.16/1.51  
% 3.16/1.51  
% 3.16/1.51  %Background operators:
% 3.16/1.51  
% 3.16/1.51  
% 3.16/1.51  %Foreground operators:
% 3.16/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.16/1.51  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.16/1.51  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.16/1.51  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.16/1.51  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.16/1.51  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.16/1.51  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.16/1.51  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.16/1.51  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.16/1.51  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.16/1.51  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 3.16/1.51  tff('#skF_1', type, '#skF_1': $i).
% 3.16/1.51  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.16/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.16/1.51  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.16/1.51  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.16/1.51  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.16/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.16/1.51  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.16/1.51  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.16/1.51  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.16/1.51  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.16/1.51  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 3.16/1.51  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.16/1.51  
% 3.16/1.53  tff(f_109, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_relat_1)).
% 3.16/1.53  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.16/1.53  tff(f_58, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 3.16/1.53  tff(f_68, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 3.16/1.53  tff(f_30, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 3.16/1.53  tff(f_50, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.16/1.53  tff(f_32, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.16/1.53  tff(f_102, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 3.16/1.53  tff(f_92, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(A), k1_relat_1(B)) => (k1_relat_1(k5_relat_1(A, B)) = k1_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_relat_1)).
% 3.16/1.53  tff(f_76, axiom, (![A]: (v1_relat_1(A) => (k3_xboole_0(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_relat_1)).
% 3.16/1.53  tff(f_62, axiom, (![A]: (v1_relat_1(A) => v1_relat_1(k4_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 3.16/1.53  tff(f_28, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 3.16/1.53  tff(f_34, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 3.16/1.53  tff(f_52, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 3.16/1.53  tff(f_83, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k4_relat_1(k6_subset_1(A, B)) = k6_subset_1(k4_relat_1(A), k4_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_relat_1)).
% 3.16/1.53  tff(f_72, axiom, (![A]: (v1_relat_1(A) => (k4_relat_1(k4_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k4_relat_1)).
% 3.16/1.53  tff(f_99, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k4_relat_1(k5_relat_1(A, B)) = k5_relat_1(k4_relat_1(B), k4_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_relat_1)).
% 3.16/1.53  tff(c_52, plain, (k5_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0 | k5_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.16/1.53  tff(c_101, plain, (k5_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_52])).
% 3.16/1.53  tff(c_54, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.16/1.53  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.16/1.53  tff(c_96, plain, (![A_48]: (v1_relat_1(A_48) | ~v1_xboole_0(A_48))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.16/1.53  tff(c_100, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_96])).
% 3.16/1.53  tff(c_36, plain, (![A_31, B_32]: (v1_relat_1(k5_relat_1(A_31, B_32)) | ~v1_relat_1(B_32) | ~v1_relat_1(A_31))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.16/1.53  tff(c_6, plain, (![A_3]: (k3_xboole_0(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_30])).
% 3.16/1.53  tff(c_26, plain, (![B_24]: (k2_zfmisc_1(k1_xboole_0, B_24)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.16/1.53  tff(c_8, plain, (![A_4]: (r1_tarski(k1_xboole_0, A_4))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.16/1.53  tff(c_50, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.16/1.53  tff(c_48, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.16/1.53  tff(c_467, plain, (![A_91, B_92]: (k1_relat_1(k5_relat_1(A_91, B_92))=k1_relat_1(A_91) | ~r1_tarski(k2_relat_1(A_91), k1_relat_1(B_92)) | ~v1_relat_1(B_92) | ~v1_relat_1(A_91))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.16/1.53  tff(c_473, plain, (![B_92]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_92))=k1_relat_1(k1_xboole_0) | ~r1_tarski(k1_xboole_0, k1_relat_1(B_92)) | ~v1_relat_1(B_92) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_48, c_467])).
% 3.16/1.53  tff(c_478, plain, (![B_93]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_93))=k1_xboole_0 | ~v1_relat_1(B_93))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_8, c_50, c_473])).
% 3.16/1.53  tff(c_40, plain, (![A_34]: (k3_xboole_0(A_34, k2_zfmisc_1(k1_relat_1(A_34), k2_relat_1(A_34)))=A_34 | ~v1_relat_1(A_34))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.16/1.53  tff(c_487, plain, (![B_93]: (k3_xboole_0(k5_relat_1(k1_xboole_0, B_93), k2_zfmisc_1(k1_xboole_0, k2_relat_1(k5_relat_1(k1_xboole_0, B_93))))=k5_relat_1(k1_xboole_0, B_93) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_93)) | ~v1_relat_1(B_93))), inference(superposition, [status(thm), theory('equality')], [c_478, c_40])).
% 3.16/1.53  tff(c_497, plain, (![B_94]: (k5_relat_1(k1_xboole_0, B_94)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_94)) | ~v1_relat_1(B_94))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_26, c_487])).
% 3.16/1.53  tff(c_504, plain, (![B_32]: (k5_relat_1(k1_xboole_0, B_32)=k1_xboole_0 | ~v1_relat_1(B_32) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_36, c_497])).
% 3.16/1.53  tff(c_508, plain, (![B_95]: (k5_relat_1(k1_xboole_0, B_95)=k1_xboole_0 | ~v1_relat_1(B_95))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_504])).
% 3.16/1.53  tff(c_520, plain, (k5_relat_1(k1_xboole_0, '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_54, c_508])).
% 3.16/1.53  tff(c_527, plain, $false, inference(negUnitSimplification, [status(thm)], [c_101, c_520])).
% 3.16/1.53  tff(c_528, plain, (k5_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_52])).
% 3.16/1.53  tff(c_34, plain, (![A_30]: (v1_relat_1(k4_relat_1(A_30)) | ~v1_relat_1(A_30))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.16/1.53  tff(c_4, plain, (![A_1]: (k2_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_28])).
% 3.16/1.53  tff(c_571, plain, (![A_101, B_102]: (k4_xboole_0(A_101, k2_xboole_0(A_101, B_102))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.16/1.53  tff(c_578, plain, (![A_1]: (k4_xboole_0(A_1, A_1)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4, c_571])).
% 3.16/1.53  tff(c_28, plain, (![A_25, B_26]: (k6_subset_1(A_25, B_26)=k4_xboole_0(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.16/1.53  tff(c_42, plain, (![A_35, B_37]: (k6_subset_1(k4_relat_1(A_35), k4_relat_1(B_37))=k4_relat_1(k6_subset_1(A_35, B_37)) | ~v1_relat_1(B_37) | ~v1_relat_1(A_35))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.16/1.53  tff(c_687, plain, (![A_124, B_125]: (k4_xboole_0(k4_relat_1(A_124), k4_relat_1(B_125))=k4_relat_1(k4_xboole_0(A_124, B_125)) | ~v1_relat_1(B_125) | ~v1_relat_1(A_124))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_28, c_42])).
% 3.16/1.53  tff(c_694, plain, (![B_125]: (k4_relat_1(k4_xboole_0(B_125, B_125))=k1_xboole_0 | ~v1_relat_1(B_125) | ~v1_relat_1(B_125))), inference(superposition, [status(thm), theory('equality')], [c_687, c_578])).
% 3.16/1.53  tff(c_709, plain, (![B_125]: (k4_relat_1(k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(B_125) | ~v1_relat_1(B_125))), inference(demodulation, [status(thm), theory('equality')], [c_578, c_694])).
% 3.16/1.53  tff(c_713, plain, (![B_126]: (~v1_relat_1(B_126) | ~v1_relat_1(B_126))), inference(splitLeft, [status(thm)], [c_709])).
% 3.16/1.53  tff(c_719, plain, (~v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_100, c_713])).
% 3.16/1.53  tff(c_727, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_100, c_719])).
% 3.16/1.53  tff(c_728, plain, (k4_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_709])).
% 3.16/1.53  tff(c_812, plain, (![A_134, B_135]: (k1_relat_1(k5_relat_1(A_134, B_135))=k1_relat_1(A_134) | ~r1_tarski(k2_relat_1(A_134), k1_relat_1(B_135)) | ~v1_relat_1(B_135) | ~v1_relat_1(A_134))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.16/1.53  tff(c_818, plain, (![B_135]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_135))=k1_relat_1(k1_xboole_0) | ~r1_tarski(k1_xboole_0, k1_relat_1(B_135)) | ~v1_relat_1(B_135) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_48, c_812])).
% 3.16/1.53  tff(c_823, plain, (![B_136]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_136))=k1_xboole_0 | ~v1_relat_1(B_136))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_8, c_50, c_818])).
% 3.16/1.53  tff(c_832, plain, (![B_136]: (k3_xboole_0(k5_relat_1(k1_xboole_0, B_136), k2_zfmisc_1(k1_xboole_0, k2_relat_1(k5_relat_1(k1_xboole_0, B_136))))=k5_relat_1(k1_xboole_0, B_136) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_136)) | ~v1_relat_1(B_136))), inference(superposition, [status(thm), theory('equality')], [c_823, c_40])).
% 3.16/1.53  tff(c_873, plain, (![B_137]: (k5_relat_1(k1_xboole_0, B_137)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_137)) | ~v1_relat_1(B_137))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_26, c_832])).
% 3.16/1.53  tff(c_877, plain, (![B_32]: (k5_relat_1(k1_xboole_0, B_32)=k1_xboole_0 | ~v1_relat_1(B_32) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_36, c_873])).
% 3.16/1.53  tff(c_886, plain, (![B_138]: (k5_relat_1(k1_xboole_0, B_138)=k1_xboole_0 | ~v1_relat_1(B_138))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_877])).
% 3.16/1.53  tff(c_900, plain, (![A_30]: (k5_relat_1(k1_xboole_0, k4_relat_1(A_30))=k1_xboole_0 | ~v1_relat_1(A_30))), inference(resolution, [status(thm)], [c_34, c_886])).
% 3.16/1.53  tff(c_38, plain, (![A_33]: (k4_relat_1(k4_relat_1(A_33))=A_33 | ~v1_relat_1(A_33))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.16/1.53  tff(c_46, plain, (![B_43, A_41]: (k5_relat_1(k4_relat_1(B_43), k4_relat_1(A_41))=k4_relat_1(k5_relat_1(A_41, B_43)) | ~v1_relat_1(B_43) | ~v1_relat_1(A_41))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.16/1.53  tff(c_741, plain, (![B_43]: (k5_relat_1(k4_relat_1(B_43), k1_xboole_0)=k4_relat_1(k5_relat_1(k1_xboole_0, B_43)) | ~v1_relat_1(B_43) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_728, c_46])).
% 3.16/1.53  tff(c_790, plain, (![B_133]: (k5_relat_1(k4_relat_1(B_133), k1_xboole_0)=k4_relat_1(k5_relat_1(k1_xboole_0, B_133)) | ~v1_relat_1(B_133))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_741])).
% 3.16/1.53  tff(c_1390, plain, (![A_153]: (k4_relat_1(k5_relat_1(k1_xboole_0, k4_relat_1(A_153)))=k5_relat_1(A_153, k1_xboole_0) | ~v1_relat_1(k4_relat_1(A_153)) | ~v1_relat_1(A_153))), inference(superposition, [status(thm), theory('equality')], [c_38, c_790])).
% 3.16/1.53  tff(c_1459, plain, (![A_30]: (k5_relat_1(A_30, k1_xboole_0)=k4_relat_1(k1_xboole_0) | ~v1_relat_1(k4_relat_1(A_30)) | ~v1_relat_1(A_30) | ~v1_relat_1(A_30))), inference(superposition, [status(thm), theory('equality')], [c_900, c_1390])).
% 3.16/1.53  tff(c_1476, plain, (![A_154]: (k5_relat_1(A_154, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k4_relat_1(A_154)) | ~v1_relat_1(A_154) | ~v1_relat_1(A_154))), inference(demodulation, [status(thm), theory('equality')], [c_728, c_1459])).
% 3.16/1.53  tff(c_1509, plain, (![A_155]: (k5_relat_1(A_155, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_155))), inference(resolution, [status(thm)], [c_34, c_1476])).
% 3.16/1.53  tff(c_1530, plain, (k5_relat_1('#skF_1', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_54, c_1509])).
% 3.16/1.53  tff(c_1541, plain, $false, inference(negUnitSimplification, [status(thm)], [c_528, c_1530])).
% 3.16/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.16/1.53  
% 3.16/1.53  Inference rules
% 3.16/1.53  ----------------------
% 3.16/1.53  #Ref     : 0
% 3.16/1.53  #Sup     : 359
% 3.16/1.53  #Fact    : 0
% 3.16/1.53  #Define  : 0
% 3.16/1.53  #Split   : 3
% 3.16/1.53  #Chain   : 0
% 3.16/1.53  #Close   : 0
% 3.16/1.53  
% 3.16/1.53  Ordering : KBO
% 3.16/1.53  
% 3.16/1.53  Simplification rules
% 3.16/1.53  ----------------------
% 3.16/1.53  #Subsume      : 8
% 3.16/1.53  #Demod        : 290
% 3.16/1.53  #Tautology    : 210
% 3.16/1.53  #SimpNegUnit  : 2
% 3.16/1.53  #BackRed      : 1
% 3.16/1.53  
% 3.16/1.53  #Partial instantiations: 0
% 3.16/1.53  #Strategies tried      : 1
% 3.16/1.53  
% 3.16/1.53  Timing (in seconds)
% 3.16/1.53  ----------------------
% 3.16/1.53  Preprocessing        : 0.33
% 3.16/1.53  Parsing              : 0.18
% 3.16/1.53  CNF conversion       : 0.02
% 3.16/1.53  Main loop            : 0.43
% 3.16/1.53  Inferencing          : 0.16
% 3.16/1.53  Reduction            : 0.13
% 3.16/1.53  Demodulation         : 0.10
% 3.16/1.53  BG Simplification    : 0.03
% 3.16/1.53  Subsumption          : 0.08
% 3.16/1.53  Abstraction          : 0.03
% 3.16/1.53  MUC search           : 0.00
% 3.16/1.53  Cooper               : 0.00
% 3.16/1.53  Total                : 0.79
% 3.16/1.53  Index Insertion      : 0.00
% 3.16/1.53  Index Deletion       : 0.00
% 3.16/1.53  Index Matching       : 0.00
% 3.16/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
