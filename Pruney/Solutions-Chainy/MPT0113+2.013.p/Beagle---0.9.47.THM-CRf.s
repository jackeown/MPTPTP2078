%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:13 EST 2020

% Result     : Theorem 13.65s
% Output     : CNFRefutation 13.65s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 170 expanded)
%              Number of leaves         :   26 (  65 expanded)
%              Depth                    :   10
%              Number of atoms          :   91 ( 187 expanded)
%              Number of equality atoms :   66 ( 131 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_62,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,k4_xboole_0(B,C))
       => ( r1_tarski(A,B)
          & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_51,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_55,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_53,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_49,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_xboole_0(k3_xboole_0(A,B),k5_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l97_xboole_1)).

tff(c_42738,plain,(
    ! [A_321,B_322] :
      ( r1_xboole_0(A_321,B_322)
      | k3_xboole_0(A_321,B_322) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_30,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_3')
    | ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_197,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_10,plain,(
    ! [A_7] : k3_xboole_0(A_7,A_7) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_32,plain,(
    r1_tarski('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_201,plain,(
    ! [A_40,B_41] :
      ( k3_xboole_0(A_40,B_41) = A_40
      | ~ r1_tarski(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_209,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_32,c_201])).

tff(c_20,plain,(
    ! [A_18,B_19] : r1_tarski(k4_xboole_0(A_18,B_19),A_18) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_3588,plain,(
    ! [A_112,B_113] : k3_xboole_0(k4_xboole_0(A_112,B_113),A_112) = k4_xboole_0(A_112,B_113) ),
    inference(resolution,[status(thm)],[c_20,c_201])).

tff(c_1111,plain,(
    ! [A_74,B_75,C_76] : k3_xboole_0(k3_xboole_0(A_74,B_75),C_76) = k3_xboole_0(A_74,k3_xboole_0(B_75,C_76)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1168,plain,(
    ! [C_76] : k3_xboole_0('#skF_1',k3_xboole_0(k4_xboole_0('#skF_2','#skF_3'),C_76)) = k3_xboole_0('#skF_1',C_76) ),
    inference(superposition,[status(thm),theory(equality)],[c_209,c_1111])).

tff(c_3630,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = k3_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_3588,c_1168])).

tff(c_3722,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_209,c_3630])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4912,plain,(
    ! [B_122,A_123,B_124] : k3_xboole_0(B_122,k3_xboole_0(A_123,B_124)) = k3_xboole_0(A_123,k3_xboole_0(B_124,B_122)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1111])).

tff(c_7161,plain,(
    ! [A_137,B_138] : k3_xboole_0(A_137,k3_xboole_0(A_137,B_138)) = k3_xboole_0(B_138,A_137) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_4912])).

tff(c_7329,plain,(
    k3_xboole_0('#skF_2','#skF_1') = k3_xboole_0('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_3722,c_7161])).

tff(c_7468,plain,(
    k3_xboole_0('#skF_2','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_7329])).

tff(c_102,plain,(
    ! [B_35,A_36] : k5_xboole_0(B_35,A_36) = k5_xboole_0(A_36,B_35) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_24,plain,(
    ! [A_23] : k5_xboole_0(A_23,k1_xboole_0) = A_23 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_118,plain,(
    ! [A_36] : k5_xboole_0(k1_xboole_0,A_36) = A_36 ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_24])).

tff(c_14,plain,(
    ! [A_11,B_12] : k5_xboole_0(A_11,k3_xboole_0(A_11,B_12)) = k4_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_28,plain,(
    ! [A_27] : k5_xboole_0(A_27,A_27) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_621,plain,(
    ! [A_63,B_64,C_65] : k5_xboole_0(k5_xboole_0(A_63,B_64),C_65) = k5_xboole_0(A_63,k5_xboole_0(B_64,C_65)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_691,plain,(
    ! [A_27,C_65] : k5_xboole_0(A_27,k5_xboole_0(A_27,C_65)) = k5_xboole_0(k1_xboole_0,C_65) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_621])).

tff(c_705,plain,(
    ! [A_66,C_67] : k5_xboole_0(A_66,k5_xboole_0(A_66,C_67)) = C_67 ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_691])).

tff(c_10278,plain,(
    ! [A_157,B_158] : k5_xboole_0(A_157,k4_xboole_0(A_157,B_158)) = k3_xboole_0(A_157,B_158) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_705])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6474,plain,(
    ! [B_132,A_133,B_134] : k5_xboole_0(B_132,k5_xboole_0(A_133,B_134)) = k5_xboole_0(A_133,k5_xboole_0(B_134,B_132)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_621])).

tff(c_6791,plain,(
    ! [A_36,B_132] : k5_xboole_0(k1_xboole_0,k5_xboole_0(A_36,B_132)) = k5_xboole_0(B_132,A_36) ),
    inference(superposition,[status(thm),theory(equality)],[c_118,c_6474])).

tff(c_10290,plain,(
    ! [A_157,B_158] : k5_xboole_0(k4_xboole_0(A_157,B_158),A_157) = k5_xboole_0(k1_xboole_0,k3_xboole_0(A_157,B_158)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10278,c_6791])).

tff(c_10415,plain,(
    ! [A_157,B_158] : k5_xboole_0(k4_xboole_0(A_157,B_158),A_157) = k3_xboole_0(A_157,B_158) ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_10290])).

tff(c_479,plain,(
    ! [A_57,B_58,C_59] : k4_xboole_0(k3_xboole_0(A_57,B_58),C_59) = k3_xboole_0(A_57,k4_xboole_0(B_58,C_59)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_522,plain,(
    ! [A_7,C_59] : k3_xboole_0(A_7,k4_xboole_0(A_7,C_59)) = k4_xboole_0(A_7,C_59) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_479])).

tff(c_7827,plain,(
    ! [A_141,B_142] : k5_xboole_0(k1_xboole_0,k5_xboole_0(A_141,B_142)) = k5_xboole_0(B_142,A_141) ),
    inference(superposition,[status(thm),theory(equality)],[c_118,c_6474])).

tff(c_7965,plain,(
    ! [A_11,B_12] : k5_xboole_0(k3_xboole_0(A_11,B_12),A_11) = k5_xboole_0(k1_xboole_0,k4_xboole_0(A_11,B_12)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_7827])).

tff(c_20689,plain,(
    ! [A_220,B_221] : k5_xboole_0(k3_xboole_0(A_220,B_221),A_220) = k4_xboole_0(A_220,B_221) ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_7965])).

tff(c_20898,plain,(
    ! [A_7,C_59] : k5_xboole_0(k4_xboole_0(A_7,C_59),A_7) = k4_xboole_0(A_7,k4_xboole_0(A_7,C_59)) ),
    inference(superposition,[status(thm),theory(equality)],[c_522,c_20689])).

tff(c_42013,plain,(
    ! [A_317,C_318] : k4_xboole_0(A_317,k4_xboole_0(A_317,C_318)) = k3_xboole_0(A_317,C_318) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10415,c_20898])).

tff(c_42467,plain,(
    ! [A_319,C_320] : r1_tarski(k3_xboole_0(A_319,C_320),A_319) ),
    inference(superposition,[status(thm),theory(equality)],[c_42013,c_20])).

tff(c_42587,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_7468,c_42467])).

tff(c_42733,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_197,c_42587])).

tff(c_42734,plain,(
    ~ r1_xboole_0('#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_42742,plain,(
    k3_xboole_0('#skF_1','#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_42738,c_42734])).

tff(c_42748,plain,(
    ! [A_325,B_326] : r1_xboole_0(k3_xboole_0(A_325,B_326),k5_xboole_0(A_325,B_326)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_42769,plain,(
    ! [A_7] : r1_xboole_0(A_7,k5_xboole_0(A_7,A_7)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_42748])).

tff(c_42779,plain,(
    ! [A_327] : r1_xboole_0(A_327,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_42769])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( k3_xboole_0(A_5,B_6) = k1_xboole_0
      | ~ r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_42783,plain,(
    ! [A_327] : k3_xboole_0(A_327,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_42779,c_6])).

tff(c_42735,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_42820,plain,(
    ! [A_329,B_330] :
      ( k3_xboole_0(A_329,B_330) = A_329
      | ~ r1_tarski(A_329,B_330) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_42830,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_42735,c_42820])).

tff(c_43039,plain,(
    ! [A_340,B_341,C_342] : k4_xboole_0(k3_xboole_0(A_340,B_341),C_342) = k3_xboole_0(A_340,k4_xboole_0(B_341,C_342)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_44376,plain,(
    ! [C_365] : k3_xboole_0('#skF_1',k4_xboole_0('#skF_2',C_365)) = k4_xboole_0('#skF_1',C_365) ),
    inference(superposition,[status(thm),theory(equality)],[c_42830,c_43039])).

tff(c_42832,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_32,c_42820])).

tff(c_44403,plain,(
    k4_xboole_0('#skF_1','#skF_3') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_44376,c_42832])).

tff(c_22,plain,(
    ! [A_20,B_21,C_22] : k4_xboole_0(k3_xboole_0(A_20,B_21),C_22) = k3_xboole_0(A_20,k4_xboole_0(B_21,C_22)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_43224,plain,(
    ! [A_346,B_347,C_348] : k3_xboole_0(k3_xboole_0(A_346,B_347),C_348) = k3_xboole_0(A_346,k3_xboole_0(B_347,C_348)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_44886,plain,(
    ! [A_375,C_376] : k3_xboole_0(A_375,k3_xboole_0(A_375,C_376)) = k3_xboole_0(A_375,C_376) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_43224])).

tff(c_42904,plain,(
    ! [A_333,B_334] : k5_xboole_0(A_333,k3_xboole_0(A_333,B_334)) = k4_xboole_0(A_333,B_334) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_42936,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_42904])).

tff(c_44906,plain,(
    ! [A_375,C_376] : k5_xboole_0(k3_xboole_0(A_375,C_376),k3_xboole_0(A_375,C_376)) = k4_xboole_0(k3_xboole_0(A_375,C_376),A_375) ),
    inference(superposition,[status(thm),theory(equality)],[c_44886,c_42936])).

tff(c_45024,plain,(
    ! [A_377,C_378] : k3_xboole_0(A_377,k4_xboole_0(C_378,A_377)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_28,c_44906])).

tff(c_45081,plain,(
    k3_xboole_0('#skF_3','#skF_1') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_44403,c_45024])).

tff(c_43301,plain,(
    ! [A_7,C_348] : k3_xboole_0(A_7,k3_xboole_0(A_7,C_348)) = k3_xboole_0(A_7,C_348) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_43224])).

tff(c_45145,plain,(
    k3_xboole_0('#skF_3',k1_xboole_0) = k3_xboole_0('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_45081,c_43301])).

tff(c_45181,plain,(
    k3_xboole_0('#skF_1','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_42783,c_2,c_45145])).

tff(c_45183,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42742,c_45181])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:35:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.65/6.93  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.65/6.94  
% 13.65/6.94  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.65/6.95  %$ r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 13.65/6.95  
% 13.65/6.95  %Foreground sorts:
% 13.65/6.95  
% 13.65/6.95  
% 13.65/6.95  %Background operators:
% 13.65/6.95  
% 13.65/6.95  
% 13.65/6.95  %Foreground operators:
% 13.65/6.95  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.65/6.95  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 13.65/6.95  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 13.65/6.95  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 13.65/6.95  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 13.65/6.95  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 13.65/6.95  tff('#skF_2', type, '#skF_2': $i).
% 13.65/6.95  tff('#skF_3', type, '#skF_3': $i).
% 13.65/6.95  tff('#skF_1', type, '#skF_1': $i).
% 13.65/6.95  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.65/6.95  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.65/6.95  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 13.65/6.95  
% 13.65/6.96  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 13.65/6.96  tff(f_62, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 13.65/6.96  tff(f_35, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 13.65/6.96  tff(f_45, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 13.65/6.96  tff(f_47, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 13.65/6.96  tff(f_41, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_xboole_1)).
% 13.65/6.96  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 13.65/6.96  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 13.65/6.96  tff(f_51, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 13.65/6.96  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 13.65/6.96  tff(f_55, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 13.65/6.96  tff(f_53, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 13.65/6.96  tff(f_49, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 13.65/6.96  tff(f_37, axiom, (![A, B]: r1_xboole_0(k3_xboole_0(A, B), k5_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l97_xboole_1)).
% 13.65/6.96  tff(c_42738, plain, (![A_321, B_322]: (r1_xboole_0(A_321, B_322) | k3_xboole_0(A_321, B_322)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 13.65/6.96  tff(c_30, plain, (~r1_xboole_0('#skF_1', '#skF_3') | ~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_62])).
% 13.65/6.96  tff(c_197, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_30])).
% 13.65/6.96  tff(c_10, plain, (![A_7]: (k3_xboole_0(A_7, A_7)=A_7)), inference(cnfTransformation, [status(thm)], [f_35])).
% 13.65/6.96  tff(c_32, plain, (r1_tarski('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_62])).
% 13.65/6.96  tff(c_201, plain, (![A_40, B_41]: (k3_xboole_0(A_40, B_41)=A_40 | ~r1_tarski(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_45])).
% 13.65/6.96  tff(c_209, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))='#skF_1'), inference(resolution, [status(thm)], [c_32, c_201])).
% 13.65/6.96  tff(c_20, plain, (![A_18, B_19]: (r1_tarski(k4_xboole_0(A_18, B_19), A_18))), inference(cnfTransformation, [status(thm)], [f_47])).
% 13.65/6.96  tff(c_3588, plain, (![A_112, B_113]: (k3_xboole_0(k4_xboole_0(A_112, B_113), A_112)=k4_xboole_0(A_112, B_113))), inference(resolution, [status(thm)], [c_20, c_201])).
% 13.65/6.96  tff(c_1111, plain, (![A_74, B_75, C_76]: (k3_xboole_0(k3_xboole_0(A_74, B_75), C_76)=k3_xboole_0(A_74, k3_xboole_0(B_75, C_76)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 13.65/6.96  tff(c_1168, plain, (![C_76]: (k3_xboole_0('#skF_1', k3_xboole_0(k4_xboole_0('#skF_2', '#skF_3'), C_76))=k3_xboole_0('#skF_1', C_76))), inference(superposition, [status(thm), theory('equality')], [c_209, c_1111])).
% 13.65/6.96  tff(c_3630, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))=k3_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_3588, c_1168])).
% 13.65/6.96  tff(c_3722, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_209, c_3630])).
% 13.65/6.96  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 13.65/6.96  tff(c_4912, plain, (![B_122, A_123, B_124]: (k3_xboole_0(B_122, k3_xboole_0(A_123, B_124))=k3_xboole_0(A_123, k3_xboole_0(B_124, B_122)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1111])).
% 13.65/6.96  tff(c_7161, plain, (![A_137, B_138]: (k3_xboole_0(A_137, k3_xboole_0(A_137, B_138))=k3_xboole_0(B_138, A_137))), inference(superposition, [status(thm), theory('equality')], [c_10, c_4912])).
% 13.65/6.96  tff(c_7329, plain, (k3_xboole_0('#skF_2', '#skF_1')=k3_xboole_0('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_3722, c_7161])).
% 13.65/6.96  tff(c_7468, plain, (k3_xboole_0('#skF_2', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_10, c_7329])).
% 13.65/6.96  tff(c_102, plain, (![B_35, A_36]: (k5_xboole_0(B_35, A_36)=k5_xboole_0(A_36, B_35))), inference(cnfTransformation, [status(thm)], [f_29])).
% 13.65/6.96  tff(c_24, plain, (![A_23]: (k5_xboole_0(A_23, k1_xboole_0)=A_23)), inference(cnfTransformation, [status(thm)], [f_51])).
% 13.65/6.96  tff(c_118, plain, (![A_36]: (k5_xboole_0(k1_xboole_0, A_36)=A_36)), inference(superposition, [status(thm), theory('equality')], [c_102, c_24])).
% 13.65/6.96  tff(c_14, plain, (![A_11, B_12]: (k5_xboole_0(A_11, k3_xboole_0(A_11, B_12))=k4_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_39])).
% 13.65/6.96  tff(c_28, plain, (![A_27]: (k5_xboole_0(A_27, A_27)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_55])).
% 13.65/6.96  tff(c_621, plain, (![A_63, B_64, C_65]: (k5_xboole_0(k5_xboole_0(A_63, B_64), C_65)=k5_xboole_0(A_63, k5_xboole_0(B_64, C_65)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 13.65/6.96  tff(c_691, plain, (![A_27, C_65]: (k5_xboole_0(A_27, k5_xboole_0(A_27, C_65))=k5_xboole_0(k1_xboole_0, C_65))), inference(superposition, [status(thm), theory('equality')], [c_28, c_621])).
% 13.65/6.96  tff(c_705, plain, (![A_66, C_67]: (k5_xboole_0(A_66, k5_xboole_0(A_66, C_67))=C_67)), inference(demodulation, [status(thm), theory('equality')], [c_118, c_691])).
% 13.65/6.96  tff(c_10278, plain, (![A_157, B_158]: (k5_xboole_0(A_157, k4_xboole_0(A_157, B_158))=k3_xboole_0(A_157, B_158))), inference(superposition, [status(thm), theory('equality')], [c_14, c_705])).
% 13.65/6.96  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 13.65/6.96  tff(c_6474, plain, (![B_132, A_133, B_134]: (k5_xboole_0(B_132, k5_xboole_0(A_133, B_134))=k5_xboole_0(A_133, k5_xboole_0(B_134, B_132)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_621])).
% 13.65/6.96  tff(c_6791, plain, (![A_36, B_132]: (k5_xboole_0(k1_xboole_0, k5_xboole_0(A_36, B_132))=k5_xboole_0(B_132, A_36))), inference(superposition, [status(thm), theory('equality')], [c_118, c_6474])).
% 13.65/6.96  tff(c_10290, plain, (![A_157, B_158]: (k5_xboole_0(k4_xboole_0(A_157, B_158), A_157)=k5_xboole_0(k1_xboole_0, k3_xboole_0(A_157, B_158)))), inference(superposition, [status(thm), theory('equality')], [c_10278, c_6791])).
% 13.65/6.96  tff(c_10415, plain, (![A_157, B_158]: (k5_xboole_0(k4_xboole_0(A_157, B_158), A_157)=k3_xboole_0(A_157, B_158))), inference(demodulation, [status(thm), theory('equality')], [c_118, c_10290])).
% 13.65/6.96  tff(c_479, plain, (![A_57, B_58, C_59]: (k4_xboole_0(k3_xboole_0(A_57, B_58), C_59)=k3_xboole_0(A_57, k4_xboole_0(B_58, C_59)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 13.65/6.96  tff(c_522, plain, (![A_7, C_59]: (k3_xboole_0(A_7, k4_xboole_0(A_7, C_59))=k4_xboole_0(A_7, C_59))), inference(superposition, [status(thm), theory('equality')], [c_10, c_479])).
% 13.65/6.96  tff(c_7827, plain, (![A_141, B_142]: (k5_xboole_0(k1_xboole_0, k5_xboole_0(A_141, B_142))=k5_xboole_0(B_142, A_141))), inference(superposition, [status(thm), theory('equality')], [c_118, c_6474])).
% 13.65/6.96  tff(c_7965, plain, (![A_11, B_12]: (k5_xboole_0(k3_xboole_0(A_11, B_12), A_11)=k5_xboole_0(k1_xboole_0, k4_xboole_0(A_11, B_12)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_7827])).
% 13.65/6.96  tff(c_20689, plain, (![A_220, B_221]: (k5_xboole_0(k3_xboole_0(A_220, B_221), A_220)=k4_xboole_0(A_220, B_221))), inference(demodulation, [status(thm), theory('equality')], [c_118, c_7965])).
% 13.65/6.96  tff(c_20898, plain, (![A_7, C_59]: (k5_xboole_0(k4_xboole_0(A_7, C_59), A_7)=k4_xboole_0(A_7, k4_xboole_0(A_7, C_59)))), inference(superposition, [status(thm), theory('equality')], [c_522, c_20689])).
% 13.65/6.96  tff(c_42013, plain, (![A_317, C_318]: (k4_xboole_0(A_317, k4_xboole_0(A_317, C_318))=k3_xboole_0(A_317, C_318))), inference(demodulation, [status(thm), theory('equality')], [c_10415, c_20898])).
% 13.65/6.96  tff(c_42467, plain, (![A_319, C_320]: (r1_tarski(k3_xboole_0(A_319, C_320), A_319))), inference(superposition, [status(thm), theory('equality')], [c_42013, c_20])).
% 13.65/6.96  tff(c_42587, plain, (r1_tarski('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_7468, c_42467])).
% 13.65/6.96  tff(c_42733, plain, $false, inference(negUnitSimplification, [status(thm)], [c_197, c_42587])).
% 13.65/6.96  tff(c_42734, plain, (~r1_xboole_0('#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_30])).
% 13.65/6.96  tff(c_42742, plain, (k3_xboole_0('#skF_1', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_42738, c_42734])).
% 13.65/6.96  tff(c_42748, plain, (![A_325, B_326]: (r1_xboole_0(k3_xboole_0(A_325, B_326), k5_xboole_0(A_325, B_326)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 13.65/6.96  tff(c_42769, plain, (![A_7]: (r1_xboole_0(A_7, k5_xboole_0(A_7, A_7)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_42748])).
% 13.65/6.96  tff(c_42779, plain, (![A_327]: (r1_xboole_0(A_327, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_42769])).
% 13.65/6.96  tff(c_6, plain, (![A_5, B_6]: (k3_xboole_0(A_5, B_6)=k1_xboole_0 | ~r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 13.65/6.96  tff(c_42783, plain, (![A_327]: (k3_xboole_0(A_327, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_42779, c_6])).
% 13.65/6.96  tff(c_42735, plain, (r1_tarski('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_30])).
% 13.65/6.96  tff(c_42820, plain, (![A_329, B_330]: (k3_xboole_0(A_329, B_330)=A_329 | ~r1_tarski(A_329, B_330))), inference(cnfTransformation, [status(thm)], [f_45])).
% 13.65/6.96  tff(c_42830, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(resolution, [status(thm)], [c_42735, c_42820])).
% 13.65/6.96  tff(c_43039, plain, (![A_340, B_341, C_342]: (k4_xboole_0(k3_xboole_0(A_340, B_341), C_342)=k3_xboole_0(A_340, k4_xboole_0(B_341, C_342)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 13.65/6.96  tff(c_44376, plain, (![C_365]: (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', C_365))=k4_xboole_0('#skF_1', C_365))), inference(superposition, [status(thm), theory('equality')], [c_42830, c_43039])).
% 13.65/6.96  tff(c_42832, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))='#skF_1'), inference(resolution, [status(thm)], [c_32, c_42820])).
% 13.65/6.96  tff(c_44403, plain, (k4_xboole_0('#skF_1', '#skF_3')='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_44376, c_42832])).
% 13.65/6.96  tff(c_22, plain, (![A_20, B_21, C_22]: (k4_xboole_0(k3_xboole_0(A_20, B_21), C_22)=k3_xboole_0(A_20, k4_xboole_0(B_21, C_22)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 13.65/6.96  tff(c_43224, plain, (![A_346, B_347, C_348]: (k3_xboole_0(k3_xboole_0(A_346, B_347), C_348)=k3_xboole_0(A_346, k3_xboole_0(B_347, C_348)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 13.65/6.96  tff(c_44886, plain, (![A_375, C_376]: (k3_xboole_0(A_375, k3_xboole_0(A_375, C_376))=k3_xboole_0(A_375, C_376))), inference(superposition, [status(thm), theory('equality')], [c_10, c_43224])).
% 13.65/6.96  tff(c_42904, plain, (![A_333, B_334]: (k5_xboole_0(A_333, k3_xboole_0(A_333, B_334))=k4_xboole_0(A_333, B_334))), inference(cnfTransformation, [status(thm)], [f_39])).
% 13.65/6.96  tff(c_42936, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_42904])).
% 13.65/6.96  tff(c_44906, plain, (![A_375, C_376]: (k5_xboole_0(k3_xboole_0(A_375, C_376), k3_xboole_0(A_375, C_376))=k4_xboole_0(k3_xboole_0(A_375, C_376), A_375))), inference(superposition, [status(thm), theory('equality')], [c_44886, c_42936])).
% 13.65/6.96  tff(c_45024, plain, (![A_377, C_378]: (k3_xboole_0(A_377, k4_xboole_0(C_378, A_377))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_28, c_44906])).
% 13.65/6.96  tff(c_45081, plain, (k3_xboole_0('#skF_3', '#skF_1')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_44403, c_45024])).
% 13.65/6.96  tff(c_43301, plain, (![A_7, C_348]: (k3_xboole_0(A_7, k3_xboole_0(A_7, C_348))=k3_xboole_0(A_7, C_348))), inference(superposition, [status(thm), theory('equality')], [c_10, c_43224])).
% 13.65/6.96  tff(c_45145, plain, (k3_xboole_0('#skF_3', k1_xboole_0)=k3_xboole_0('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_45081, c_43301])).
% 13.65/6.96  tff(c_45181, plain, (k3_xboole_0('#skF_1', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_42783, c_2, c_45145])).
% 13.65/6.96  tff(c_45183, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42742, c_45181])).
% 13.65/6.96  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.65/6.96  
% 13.65/6.96  Inference rules
% 13.65/6.96  ----------------------
% 13.65/6.96  #Ref     : 0
% 13.65/6.96  #Sup     : 11393
% 13.65/6.96  #Fact    : 0
% 13.65/6.96  #Define  : 0
% 13.65/6.96  #Split   : 1
% 13.65/6.96  #Chain   : 0
% 13.65/6.96  #Close   : 0
% 13.65/6.96  
% 13.65/6.96  Ordering : KBO
% 13.65/6.96  
% 13.65/6.96  Simplification rules
% 13.65/6.96  ----------------------
% 13.65/6.96  #Subsume      : 157
% 13.65/6.96  #Demod        : 15934
% 13.65/6.96  #Tautology    : 7640
% 13.65/6.96  #SimpNegUnit  : 2
% 13.65/6.96  #BackRed      : 9
% 13.65/6.96  
% 13.65/6.96  #Partial instantiations: 0
% 13.65/6.96  #Strategies tried      : 1
% 13.65/6.96  
% 13.65/6.96  Timing (in seconds)
% 13.65/6.96  ----------------------
% 13.65/6.97  Preprocessing        : 0.30
% 13.65/6.97  Parsing              : 0.17
% 13.65/6.97  CNF conversion       : 0.02
% 13.65/6.97  Main loop            : 5.88
% 13.65/6.97  Inferencing          : 0.85
% 13.65/6.97  Reduction            : 3.85
% 13.65/6.97  Demodulation         : 3.56
% 13.65/6.97  BG Simplification    : 0.11
% 13.65/6.97  Subsumption          : 0.84
% 13.65/6.97  Abstraction          : 0.17
% 13.65/6.97  MUC search           : 0.00
% 13.65/6.97  Cooper               : 0.00
% 13.65/6.97  Total                : 6.23
% 13.65/6.97  Index Insertion      : 0.00
% 13.65/6.97  Index Deletion       : 0.00
% 13.65/6.97  Index Matching       : 0.00
% 13.65/6.97  BG Taut test         : 0.00
%------------------------------------------------------------------------------
