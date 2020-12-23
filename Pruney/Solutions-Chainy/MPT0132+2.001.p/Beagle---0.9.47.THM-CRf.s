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
% DateTime   : Thu Dec  3 09:45:41 EST 2020

% Result     : Theorem 20.29s
% Output     : CNFRefutation 20.29s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 272 expanded)
%              Number of leaves         :   26 ( 104 expanded)
%              Depth                    :   12
%              Number of atoms          :   63 ( 255 expanded)
%              Number of equality atoms :   62 ( 254 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_49,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_tarski(A),k2_enumset1(B,C,D,E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_enumset1)).

tff(f_47,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_tarski(A),k1_enumset1(B,C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).

tff(f_31,axiom,(
    ! [A,B] : k2_xboole_0(A,k2_xboole_0(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k1_tarski(A),k2_tarski(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_enumset1(A,B,C),k2_tarski(D,E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l57_enumset1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_45,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k2_tarski(A,B),k1_tarski(C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_enumset1)).

tff(f_52,negated_conjecture,(
    ~ ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k2_tarski(A,B),k1_enumset1(C,D,E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_enumset1)).

tff(c_24,plain,(
    ! [A_31,C_33,B_32,E_35,D_34] : k2_xboole_0(k1_tarski(A_31),k2_enumset1(B_32,C_33,D_34,E_35)) = k3_enumset1(A_31,B_32,C_33,D_34,E_35) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_22,plain,(
    ! [A_27,B_28,C_29,D_30] : k2_xboole_0(k1_tarski(A_27),k1_enumset1(B_28,C_29,D_30)) = k2_enumset1(A_27,B_28,C_29,D_30) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_494,plain,(
    ! [A_71,B_72,C_73,D_74] : k2_xboole_0(k1_tarski(A_71),k1_enumset1(B_72,C_73,D_74)) = k2_enumset1(A_71,B_72,C_73,D_74) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_6,plain,(
    ! [A_5,B_6] : k2_xboole_0(A_5,k2_xboole_0(A_5,B_6)) = k2_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_503,plain,(
    ! [A_71,B_72,C_73,D_74] : k2_xboole_0(k1_tarski(A_71),k2_enumset1(A_71,B_72,C_73,D_74)) = k2_xboole_0(k1_tarski(A_71),k1_enumset1(B_72,C_73,D_74)) ),
    inference(superposition,[status(thm),theory(equality)],[c_494,c_6])).

tff(c_3608,plain,(
    ! [A_169,B_170,C_171,D_172] : k2_xboole_0(k1_tarski(A_169),k2_enumset1(A_169,B_170,C_171,D_172)) = k2_enumset1(A_169,B_170,C_171,D_172) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_503])).

tff(c_3657,plain,(
    ! [B_32,C_33,D_34,E_35] : k3_enumset1(B_32,B_32,C_33,D_34,E_35) = k2_enumset1(B_32,C_33,D_34,E_35) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_3608])).

tff(c_16,plain,(
    ! [A_19,B_20] : k2_xboole_0(k1_tarski(A_19),k1_tarski(B_20)) = k2_tarski(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_92,plain,(
    ! [A_42,B_43] : k2_xboole_0(k1_tarski(A_42),k1_tarski(B_43)) = k2_tarski(A_42,B_43) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_98,plain,(
    ! [A_42,B_43] : k2_xboole_0(k1_tarski(A_42),k2_tarski(A_42,B_43)) = k2_xboole_0(k1_tarski(A_42),k1_tarski(B_43)) ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_6])).

tff(c_304,plain,(
    ! [A_57,B_58] : k2_xboole_0(k1_tarski(A_57),k2_tarski(A_57,B_58)) = k2_tarski(A_57,B_58) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_98])).

tff(c_18,plain,(
    ! [A_21,B_22,C_23] : k2_xboole_0(k1_tarski(A_21),k2_tarski(B_22,C_23)) = k1_enumset1(A_21,B_22,C_23) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_310,plain,(
    ! [A_57,B_58] : k1_enumset1(A_57,A_57,B_58) = k2_tarski(A_57,B_58) ),
    inference(superposition,[status(thm),theory(equality)],[c_304,c_18])).

tff(c_887,plain,(
    ! [C_104,D_103,A_106,B_105,E_102] : k2_xboole_0(k1_enumset1(A_106,B_105,C_104),k2_tarski(D_103,E_102)) = k3_enumset1(A_106,B_105,C_104,D_103,E_102) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_920,plain,(
    ! [A_57,B_58,D_103,E_102] : k3_enumset1(A_57,A_57,B_58,D_103,E_102) = k2_xboole_0(k2_tarski(A_57,B_58),k2_tarski(D_103,E_102)) ),
    inference(superposition,[status(thm),theory(equality)],[c_310,c_887])).

tff(c_24085,plain,(
    ! [A_57,B_58,D_103,E_102] : k2_xboole_0(k2_tarski(A_57,B_58),k2_tarski(D_103,E_102)) = k2_enumset1(A_57,B_58,D_103,E_102) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3657,c_920])).

tff(c_270,plain,(
    ! [A_54,B_55,C_56] : k2_xboole_0(k1_tarski(A_54),k2_tarski(B_55,C_56)) = k1_enumset1(A_54,B_55,C_56) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_279,plain,(
    ! [A_54,B_55,C_56] : k2_xboole_0(k1_tarski(A_54),k1_enumset1(A_54,B_55,C_56)) = k2_xboole_0(k1_tarski(A_54),k2_tarski(B_55,C_56)) ),
    inference(superposition,[status(thm),theory(equality)],[c_270,c_6])).

tff(c_1276,plain,(
    ! [A_111,B_112,C_113] : k2_xboole_0(k1_tarski(A_111),k1_enumset1(A_111,B_112,C_113)) = k1_enumset1(A_111,B_112,C_113) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_279])).

tff(c_1334,plain,(
    ! [A_114,B_115,C_116] : k2_enumset1(A_114,A_114,B_115,C_116) = k1_enumset1(A_114,B_115,C_116) ),
    inference(superposition,[status(thm),theory(equality)],[c_1276,c_22])).

tff(c_1344,plain,(
    ! [A_31,A_114,B_115,C_116] : k3_enumset1(A_31,A_114,A_114,B_115,C_116) = k2_xboole_0(k1_tarski(A_31),k1_enumset1(A_114,B_115,C_116)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1334,c_24])).

tff(c_1370,plain,(
    ! [A_31,A_114,B_115,C_116] : k3_enumset1(A_31,A_114,A_114,B_115,C_116) = k2_enumset1(A_31,A_114,B_115,C_116) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_1344])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_558,plain,(
    ! [B_81,C_82,A_83] : k2_xboole_0(k2_tarski(B_81,C_82),k1_tarski(A_83)) = k1_enumset1(A_83,B_81,C_82) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_270])).

tff(c_20,plain,(
    ! [A_24,B_25,C_26] : k2_xboole_0(k2_tarski(A_24,B_25),k1_tarski(C_26)) = k1_enumset1(A_24,B_25,C_26) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_604,plain,(
    ! [B_84,C_85,A_86] : k1_enumset1(B_84,C_85,A_86) = k1_enumset1(A_86,B_84,C_85) ),
    inference(superposition,[status(thm),theory(equality)],[c_558,c_20])).

tff(c_638,plain,(
    ! [A_86,C_85] : k1_enumset1(A_86,C_85,C_85) = k2_tarski(C_85,A_86) ),
    inference(superposition,[status(thm),theory(equality)],[c_604,c_310])).

tff(c_908,plain,(
    ! [A_86,C_85,D_103,E_102] : k3_enumset1(A_86,C_85,C_85,D_103,E_102) = k2_xboole_0(k2_tarski(C_85,A_86),k2_tarski(D_103,E_102)) ),
    inference(superposition,[status(thm),theory(equality)],[c_638,c_887])).

tff(c_30395,plain,(
    ! [C_585,A_586,D_587,E_588] : k2_enumset1(C_585,A_586,D_587,E_588) = k2_enumset1(A_586,C_585,D_587,E_588) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24085,c_1370,c_908])).

tff(c_55585,plain,(
    ! [D_756,C_753,A_755,A_754,E_757] : k2_xboole_0(k1_tarski(A_754),k2_enumset1(A_755,C_753,D_756,E_757)) = k3_enumset1(A_754,C_753,A_755,D_756,E_757) ),
    inference(superposition,[status(thm),theory(equality)],[c_30395,c_24])).

tff(c_55904,plain,(
    ! [A_31,C_33,B_32,E_35,D_34] : k3_enumset1(A_31,C_33,B_32,D_34,E_35) = k3_enumset1(A_31,B_32,C_33,D_34,E_35) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_55585])).

tff(c_564,plain,(
    ! [B_81,C_82,A_83] : k1_enumset1(B_81,C_82,A_83) = k1_enumset1(A_83,B_81,C_82) ),
    inference(superposition,[status(thm),theory(equality)],[c_558,c_20])).

tff(c_34675,plain,(
    ! [C_622,B_621,E_623,D_620,A_624] : k2_xboole_0(k1_enumset1(A_624,B_621,C_622),k2_tarski(D_620,E_623)) = k3_enumset1(B_621,C_622,A_624,D_620,E_623) ),
    inference(superposition,[status(thm),theory(equality)],[c_564,c_887])).

tff(c_14,plain,(
    ! [E_18,C_16,D_17,A_14,B_15] : k2_xboole_0(k1_enumset1(A_14,B_15,C_16),k2_tarski(D_17,E_18)) = k3_enumset1(A_14,B_15,C_16,D_17,E_18) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_34726,plain,(
    ! [C_622,B_621,E_623,D_620,A_624] : k3_enumset1(B_621,C_622,A_624,D_620,E_623) = k3_enumset1(A_624,B_621,C_622,D_620,E_623) ),
    inference(superposition,[status(thm),theory(equality)],[c_34675,c_14])).

tff(c_194,plain,(
    ! [B_50,A_51] : k2_xboole_0(k1_tarski(B_50),k1_tarski(A_51)) = k2_tarski(A_51,B_50) ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_2])).

tff(c_203,plain,(
    ! [B_50,A_51] : k2_tarski(B_50,A_51) = k2_tarski(A_51,B_50) ),
    inference(superposition,[status(thm),theory(equality)],[c_194,c_16])).

tff(c_33724,plain,(
    ! [A_611,B_608,B_609,C_610,A_607] : k2_xboole_0(k1_enumset1(A_611,B_609,C_610),k2_tarski(A_607,B_608)) = k3_enumset1(A_611,B_609,C_610,B_608,A_607) ),
    inference(superposition,[status(thm),theory(equality)],[c_203,c_887])).

tff(c_33817,plain,(
    ! [E_18,C_16,D_17,A_14,B_15] : k3_enumset1(A_14,B_15,C_16,E_18,D_17) = k3_enumset1(A_14,B_15,C_16,D_17,E_18) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_33724])).

tff(c_5283,plain,(
    ! [A_229,B_230,C_231,A_232] : k2_xboole_0(k1_tarski(A_229),k1_enumset1(B_230,C_231,A_232)) = k2_enumset1(A_229,A_232,B_230,C_231) ),
    inference(superposition,[status(thm),theory(equality)],[c_604,c_22])).

tff(c_5438,plain,(
    ! [A_233,D_234,B_235,C_236] : k2_enumset1(A_233,D_234,B_235,C_236) = k2_enumset1(A_233,B_235,C_236,D_234) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_5283])).

tff(c_61120,plain,(
    ! [D_797,B_800,A_798,A_796,C_799] : k2_xboole_0(k1_tarski(A_796),k2_enumset1(A_798,B_800,C_799,D_797)) = k3_enumset1(A_796,A_798,D_797,B_800,C_799) ),
    inference(superposition,[status(thm),theory(equality)],[c_5438,c_24])).

tff(c_61205,plain,(
    ! [D_797,B_800,A_798,A_796,C_799] : k3_enumset1(A_796,A_798,D_797,B_800,C_799) = k3_enumset1(A_796,A_798,B_800,C_799,D_797) ),
    inference(superposition,[status(thm),theory(equality)],[c_61120,c_24])).

tff(c_929,plain,(
    ! [C_104,D_103,A_106,B_105,E_102] : k2_xboole_0(k2_tarski(D_103,E_102),k1_enumset1(A_106,B_105,C_104)) = k3_enumset1(A_106,B_105,C_104,D_103,E_102) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_887])).

tff(c_300,plain,(
    ! [B_55,C_56,A_54] : k2_xboole_0(k2_tarski(B_55,C_56),k1_tarski(A_54)) = k1_enumset1(A_54,B_55,C_56) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_270])).

tff(c_1378,plain,(
    ! [A_117,B_118,A_119] : k2_xboole_0(k2_tarski(A_117,B_118),k1_tarski(A_119)) = k1_enumset1(A_119,B_118,A_117) ),
    inference(superposition,[status(thm),theory(equality)],[c_203,c_558])).

tff(c_1417,plain,(
    ! [A_54,C_56,B_55] : k1_enumset1(A_54,C_56,B_55) = k1_enumset1(A_54,B_55,C_56) ),
    inference(superposition,[status(thm),theory(equality)],[c_300,c_1378])).

tff(c_26,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_2'),k1_enumset1('#skF_3','#skF_4','#skF_5')) != k3_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_603,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_2'),k1_enumset1('#skF_4','#skF_5','#skF_3')) != k3_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_564,c_26])).

tff(c_1554,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_2'),k1_enumset1('#skF_4','#skF_3','#skF_5')) != k3_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1417,c_603])).

tff(c_3917,plain,(
    k3_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') != k3_enumset1('#skF_4','#skF_3','#skF_5','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_929,c_1554])).

tff(c_55986,plain,(
    k3_enumset1('#skF_1','#skF_3','#skF_2','#skF_4','#skF_5') != k3_enumset1('#skF_4','#skF_3','#skF_5','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_55904,c_3917])).

tff(c_62211,plain,(
    k3_enumset1('#skF_1','#skF_3','#skF_4','#skF_5','#skF_2') != k3_enumset1('#skF_4','#skF_3','#skF_1','#skF_2','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_61205,c_61205,c_55986])).

tff(c_62214,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_55904,c_34726,c_33817,c_62211])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:58:09 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 20.29/11.58  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 20.29/11.59  
% 20.29/11.59  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 20.29/11.59  %$ k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 20.29/11.59  
% 20.29/11.59  %Foreground sorts:
% 20.29/11.59  
% 20.29/11.59  
% 20.29/11.59  %Background operators:
% 20.29/11.59  
% 20.29/11.59  
% 20.29/11.59  %Foreground operators:
% 20.29/11.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 20.29/11.59  tff(k1_tarski, type, k1_tarski: $i > $i).
% 20.29/11.59  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 20.29/11.59  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 20.29/11.59  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 20.29/11.59  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 20.29/11.59  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 20.29/11.59  tff('#skF_5', type, '#skF_5': $i).
% 20.29/11.59  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 20.29/11.59  tff('#skF_2', type, '#skF_2': $i).
% 20.29/11.59  tff('#skF_3', type, '#skF_3': $i).
% 20.29/11.59  tff('#skF_1', type, '#skF_1': $i).
% 20.29/11.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 20.29/11.59  tff('#skF_4', type, '#skF_4': $i).
% 20.29/11.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 20.29/11.59  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 20.29/11.59  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 20.29/11.59  
% 20.29/11.61  tff(f_49, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_tarski(A), k2_enumset1(B, C, D, E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_enumset1)).
% 20.29/11.61  tff(f_47, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_tarski(A), k1_enumset1(B, C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_enumset1)).
% 20.29/11.61  tff(f_31, axiom, (![A, B]: (k2_xboole_0(A, k2_xboole_0(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_xboole_1)).
% 20.29/11.61  tff(f_41, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 20.29/11.61  tff(f_43, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k1_tarski(A), k2_tarski(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_enumset1)).
% 20.29/11.61  tff(f_39, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_enumset1(A, B, C), k2_tarski(D, E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l57_enumset1)).
% 20.29/11.61  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 20.29/11.61  tff(f_45, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k2_tarski(A, B), k1_tarski(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_enumset1)).
% 20.29/11.61  tff(f_52, negated_conjecture, ~(![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k2_tarski(A, B), k1_enumset1(C, D, E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_enumset1)).
% 20.29/11.61  tff(c_24, plain, (![A_31, C_33, B_32, E_35, D_34]: (k2_xboole_0(k1_tarski(A_31), k2_enumset1(B_32, C_33, D_34, E_35))=k3_enumset1(A_31, B_32, C_33, D_34, E_35))), inference(cnfTransformation, [status(thm)], [f_49])).
% 20.29/11.61  tff(c_22, plain, (![A_27, B_28, C_29, D_30]: (k2_xboole_0(k1_tarski(A_27), k1_enumset1(B_28, C_29, D_30))=k2_enumset1(A_27, B_28, C_29, D_30))), inference(cnfTransformation, [status(thm)], [f_47])).
% 20.29/11.61  tff(c_494, plain, (![A_71, B_72, C_73, D_74]: (k2_xboole_0(k1_tarski(A_71), k1_enumset1(B_72, C_73, D_74))=k2_enumset1(A_71, B_72, C_73, D_74))), inference(cnfTransformation, [status(thm)], [f_47])).
% 20.29/11.61  tff(c_6, plain, (![A_5, B_6]: (k2_xboole_0(A_5, k2_xboole_0(A_5, B_6))=k2_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 20.29/11.61  tff(c_503, plain, (![A_71, B_72, C_73, D_74]: (k2_xboole_0(k1_tarski(A_71), k2_enumset1(A_71, B_72, C_73, D_74))=k2_xboole_0(k1_tarski(A_71), k1_enumset1(B_72, C_73, D_74)))), inference(superposition, [status(thm), theory('equality')], [c_494, c_6])).
% 20.29/11.61  tff(c_3608, plain, (![A_169, B_170, C_171, D_172]: (k2_xboole_0(k1_tarski(A_169), k2_enumset1(A_169, B_170, C_171, D_172))=k2_enumset1(A_169, B_170, C_171, D_172))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_503])).
% 20.29/11.61  tff(c_3657, plain, (![B_32, C_33, D_34, E_35]: (k3_enumset1(B_32, B_32, C_33, D_34, E_35)=k2_enumset1(B_32, C_33, D_34, E_35))), inference(superposition, [status(thm), theory('equality')], [c_24, c_3608])).
% 20.29/11.61  tff(c_16, plain, (![A_19, B_20]: (k2_xboole_0(k1_tarski(A_19), k1_tarski(B_20))=k2_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_41])).
% 20.29/11.61  tff(c_92, plain, (![A_42, B_43]: (k2_xboole_0(k1_tarski(A_42), k1_tarski(B_43))=k2_tarski(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_41])).
% 20.29/11.61  tff(c_98, plain, (![A_42, B_43]: (k2_xboole_0(k1_tarski(A_42), k2_tarski(A_42, B_43))=k2_xboole_0(k1_tarski(A_42), k1_tarski(B_43)))), inference(superposition, [status(thm), theory('equality')], [c_92, c_6])).
% 20.29/11.61  tff(c_304, plain, (![A_57, B_58]: (k2_xboole_0(k1_tarski(A_57), k2_tarski(A_57, B_58))=k2_tarski(A_57, B_58))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_98])).
% 20.29/11.61  tff(c_18, plain, (![A_21, B_22, C_23]: (k2_xboole_0(k1_tarski(A_21), k2_tarski(B_22, C_23))=k1_enumset1(A_21, B_22, C_23))), inference(cnfTransformation, [status(thm)], [f_43])).
% 20.29/11.61  tff(c_310, plain, (![A_57, B_58]: (k1_enumset1(A_57, A_57, B_58)=k2_tarski(A_57, B_58))), inference(superposition, [status(thm), theory('equality')], [c_304, c_18])).
% 20.29/11.61  tff(c_887, plain, (![C_104, D_103, A_106, B_105, E_102]: (k2_xboole_0(k1_enumset1(A_106, B_105, C_104), k2_tarski(D_103, E_102))=k3_enumset1(A_106, B_105, C_104, D_103, E_102))), inference(cnfTransformation, [status(thm)], [f_39])).
% 20.29/11.61  tff(c_920, plain, (![A_57, B_58, D_103, E_102]: (k3_enumset1(A_57, A_57, B_58, D_103, E_102)=k2_xboole_0(k2_tarski(A_57, B_58), k2_tarski(D_103, E_102)))), inference(superposition, [status(thm), theory('equality')], [c_310, c_887])).
% 20.29/11.61  tff(c_24085, plain, (![A_57, B_58, D_103, E_102]: (k2_xboole_0(k2_tarski(A_57, B_58), k2_tarski(D_103, E_102))=k2_enumset1(A_57, B_58, D_103, E_102))), inference(demodulation, [status(thm), theory('equality')], [c_3657, c_920])).
% 20.29/11.61  tff(c_270, plain, (![A_54, B_55, C_56]: (k2_xboole_0(k1_tarski(A_54), k2_tarski(B_55, C_56))=k1_enumset1(A_54, B_55, C_56))), inference(cnfTransformation, [status(thm)], [f_43])).
% 20.29/11.61  tff(c_279, plain, (![A_54, B_55, C_56]: (k2_xboole_0(k1_tarski(A_54), k1_enumset1(A_54, B_55, C_56))=k2_xboole_0(k1_tarski(A_54), k2_tarski(B_55, C_56)))), inference(superposition, [status(thm), theory('equality')], [c_270, c_6])).
% 20.29/11.61  tff(c_1276, plain, (![A_111, B_112, C_113]: (k2_xboole_0(k1_tarski(A_111), k1_enumset1(A_111, B_112, C_113))=k1_enumset1(A_111, B_112, C_113))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_279])).
% 20.29/11.61  tff(c_1334, plain, (![A_114, B_115, C_116]: (k2_enumset1(A_114, A_114, B_115, C_116)=k1_enumset1(A_114, B_115, C_116))), inference(superposition, [status(thm), theory('equality')], [c_1276, c_22])).
% 20.29/11.61  tff(c_1344, plain, (![A_31, A_114, B_115, C_116]: (k3_enumset1(A_31, A_114, A_114, B_115, C_116)=k2_xboole_0(k1_tarski(A_31), k1_enumset1(A_114, B_115, C_116)))), inference(superposition, [status(thm), theory('equality')], [c_1334, c_24])).
% 20.29/11.61  tff(c_1370, plain, (![A_31, A_114, B_115, C_116]: (k3_enumset1(A_31, A_114, A_114, B_115, C_116)=k2_enumset1(A_31, A_114, B_115, C_116))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_1344])).
% 20.29/11.61  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 20.29/11.61  tff(c_558, plain, (![B_81, C_82, A_83]: (k2_xboole_0(k2_tarski(B_81, C_82), k1_tarski(A_83))=k1_enumset1(A_83, B_81, C_82))), inference(superposition, [status(thm), theory('equality')], [c_2, c_270])).
% 20.29/11.61  tff(c_20, plain, (![A_24, B_25, C_26]: (k2_xboole_0(k2_tarski(A_24, B_25), k1_tarski(C_26))=k1_enumset1(A_24, B_25, C_26))), inference(cnfTransformation, [status(thm)], [f_45])).
% 20.29/11.61  tff(c_604, plain, (![B_84, C_85, A_86]: (k1_enumset1(B_84, C_85, A_86)=k1_enumset1(A_86, B_84, C_85))), inference(superposition, [status(thm), theory('equality')], [c_558, c_20])).
% 20.29/11.61  tff(c_638, plain, (![A_86, C_85]: (k1_enumset1(A_86, C_85, C_85)=k2_tarski(C_85, A_86))), inference(superposition, [status(thm), theory('equality')], [c_604, c_310])).
% 20.29/11.61  tff(c_908, plain, (![A_86, C_85, D_103, E_102]: (k3_enumset1(A_86, C_85, C_85, D_103, E_102)=k2_xboole_0(k2_tarski(C_85, A_86), k2_tarski(D_103, E_102)))), inference(superposition, [status(thm), theory('equality')], [c_638, c_887])).
% 20.29/11.61  tff(c_30395, plain, (![C_585, A_586, D_587, E_588]: (k2_enumset1(C_585, A_586, D_587, E_588)=k2_enumset1(A_586, C_585, D_587, E_588))), inference(demodulation, [status(thm), theory('equality')], [c_24085, c_1370, c_908])).
% 20.29/11.61  tff(c_55585, plain, (![D_756, C_753, A_755, A_754, E_757]: (k2_xboole_0(k1_tarski(A_754), k2_enumset1(A_755, C_753, D_756, E_757))=k3_enumset1(A_754, C_753, A_755, D_756, E_757))), inference(superposition, [status(thm), theory('equality')], [c_30395, c_24])).
% 20.29/11.61  tff(c_55904, plain, (![A_31, C_33, B_32, E_35, D_34]: (k3_enumset1(A_31, C_33, B_32, D_34, E_35)=k3_enumset1(A_31, B_32, C_33, D_34, E_35))), inference(superposition, [status(thm), theory('equality')], [c_24, c_55585])).
% 20.29/11.61  tff(c_564, plain, (![B_81, C_82, A_83]: (k1_enumset1(B_81, C_82, A_83)=k1_enumset1(A_83, B_81, C_82))), inference(superposition, [status(thm), theory('equality')], [c_558, c_20])).
% 20.29/11.61  tff(c_34675, plain, (![C_622, B_621, E_623, D_620, A_624]: (k2_xboole_0(k1_enumset1(A_624, B_621, C_622), k2_tarski(D_620, E_623))=k3_enumset1(B_621, C_622, A_624, D_620, E_623))), inference(superposition, [status(thm), theory('equality')], [c_564, c_887])).
% 20.29/11.61  tff(c_14, plain, (![E_18, C_16, D_17, A_14, B_15]: (k2_xboole_0(k1_enumset1(A_14, B_15, C_16), k2_tarski(D_17, E_18))=k3_enumset1(A_14, B_15, C_16, D_17, E_18))), inference(cnfTransformation, [status(thm)], [f_39])).
% 20.29/11.61  tff(c_34726, plain, (![C_622, B_621, E_623, D_620, A_624]: (k3_enumset1(B_621, C_622, A_624, D_620, E_623)=k3_enumset1(A_624, B_621, C_622, D_620, E_623))), inference(superposition, [status(thm), theory('equality')], [c_34675, c_14])).
% 20.29/11.61  tff(c_194, plain, (![B_50, A_51]: (k2_xboole_0(k1_tarski(B_50), k1_tarski(A_51))=k2_tarski(A_51, B_50))), inference(superposition, [status(thm), theory('equality')], [c_92, c_2])).
% 20.29/11.61  tff(c_203, plain, (![B_50, A_51]: (k2_tarski(B_50, A_51)=k2_tarski(A_51, B_50))), inference(superposition, [status(thm), theory('equality')], [c_194, c_16])).
% 20.29/11.61  tff(c_33724, plain, (![A_611, B_608, B_609, C_610, A_607]: (k2_xboole_0(k1_enumset1(A_611, B_609, C_610), k2_tarski(A_607, B_608))=k3_enumset1(A_611, B_609, C_610, B_608, A_607))), inference(superposition, [status(thm), theory('equality')], [c_203, c_887])).
% 20.29/11.61  tff(c_33817, plain, (![E_18, C_16, D_17, A_14, B_15]: (k3_enumset1(A_14, B_15, C_16, E_18, D_17)=k3_enumset1(A_14, B_15, C_16, D_17, E_18))), inference(superposition, [status(thm), theory('equality')], [c_14, c_33724])).
% 20.29/11.61  tff(c_5283, plain, (![A_229, B_230, C_231, A_232]: (k2_xboole_0(k1_tarski(A_229), k1_enumset1(B_230, C_231, A_232))=k2_enumset1(A_229, A_232, B_230, C_231))), inference(superposition, [status(thm), theory('equality')], [c_604, c_22])).
% 20.29/11.61  tff(c_5438, plain, (![A_233, D_234, B_235, C_236]: (k2_enumset1(A_233, D_234, B_235, C_236)=k2_enumset1(A_233, B_235, C_236, D_234))), inference(superposition, [status(thm), theory('equality')], [c_22, c_5283])).
% 20.29/11.61  tff(c_61120, plain, (![D_797, B_800, A_798, A_796, C_799]: (k2_xboole_0(k1_tarski(A_796), k2_enumset1(A_798, B_800, C_799, D_797))=k3_enumset1(A_796, A_798, D_797, B_800, C_799))), inference(superposition, [status(thm), theory('equality')], [c_5438, c_24])).
% 20.29/11.61  tff(c_61205, plain, (![D_797, B_800, A_798, A_796, C_799]: (k3_enumset1(A_796, A_798, D_797, B_800, C_799)=k3_enumset1(A_796, A_798, B_800, C_799, D_797))), inference(superposition, [status(thm), theory('equality')], [c_61120, c_24])).
% 20.29/11.61  tff(c_929, plain, (![C_104, D_103, A_106, B_105, E_102]: (k2_xboole_0(k2_tarski(D_103, E_102), k1_enumset1(A_106, B_105, C_104))=k3_enumset1(A_106, B_105, C_104, D_103, E_102))), inference(superposition, [status(thm), theory('equality')], [c_2, c_887])).
% 20.29/11.61  tff(c_300, plain, (![B_55, C_56, A_54]: (k2_xboole_0(k2_tarski(B_55, C_56), k1_tarski(A_54))=k1_enumset1(A_54, B_55, C_56))), inference(superposition, [status(thm), theory('equality')], [c_2, c_270])).
% 20.29/11.61  tff(c_1378, plain, (![A_117, B_118, A_119]: (k2_xboole_0(k2_tarski(A_117, B_118), k1_tarski(A_119))=k1_enumset1(A_119, B_118, A_117))), inference(superposition, [status(thm), theory('equality')], [c_203, c_558])).
% 20.29/11.61  tff(c_1417, plain, (![A_54, C_56, B_55]: (k1_enumset1(A_54, C_56, B_55)=k1_enumset1(A_54, B_55, C_56))), inference(superposition, [status(thm), theory('equality')], [c_300, c_1378])).
% 20.29/11.61  tff(c_26, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), k1_enumset1('#skF_3', '#skF_4', '#skF_5'))!=k3_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_52])).
% 20.29/11.61  tff(c_603, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), k1_enumset1('#skF_4', '#skF_5', '#skF_3'))!=k3_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_564, c_26])).
% 20.29/11.61  tff(c_1554, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), k1_enumset1('#skF_4', '#skF_3', '#skF_5'))!=k3_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1417, c_603])).
% 20.29/11.61  tff(c_3917, plain, (k3_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')!=k3_enumset1('#skF_4', '#skF_3', '#skF_5', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_929, c_1554])).
% 20.29/11.61  tff(c_55986, plain, (k3_enumset1('#skF_1', '#skF_3', '#skF_2', '#skF_4', '#skF_5')!=k3_enumset1('#skF_4', '#skF_3', '#skF_5', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_55904, c_3917])).
% 20.29/11.61  tff(c_62211, plain, (k3_enumset1('#skF_1', '#skF_3', '#skF_4', '#skF_5', '#skF_2')!=k3_enumset1('#skF_4', '#skF_3', '#skF_1', '#skF_2', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_61205, c_61205, c_55986])).
% 20.29/11.61  tff(c_62214, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_55904, c_34726, c_33817, c_62211])).
% 20.29/11.61  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 20.29/11.61  
% 20.29/11.61  Inference rules
% 20.29/11.61  ----------------------
% 20.29/11.61  #Ref     : 0
% 20.29/11.61  #Sup     : 14892
% 20.29/11.61  #Fact    : 0
% 20.29/11.61  #Define  : 0
% 20.29/11.61  #Split   : 0
% 20.29/11.61  #Chain   : 0
% 20.29/11.61  #Close   : 0
% 20.29/11.61  
% 20.29/11.61  Ordering : KBO
% 20.29/11.61  
% 20.29/11.61  Simplification rules
% 20.29/11.61  ----------------------
% 20.29/11.61  #Subsume      : 2316
% 20.29/11.61  #Demod        : 17006
% 20.29/11.61  #Tautology    : 8562
% 20.29/11.61  #SimpNegUnit  : 0
% 20.29/11.61  #BackRed      : 5
% 20.29/11.61  
% 20.29/11.61  #Partial instantiations: 0
% 20.29/11.61  #Strategies tried      : 1
% 20.29/11.61  
% 20.29/11.61  Timing (in seconds)
% 20.29/11.61  ----------------------
% 20.29/11.61  Preprocessing        : 0.28
% 20.29/11.61  Parsing              : 0.16
% 20.29/11.61  CNF conversion       : 0.02
% 20.29/11.61  Main loop            : 10.57
% 20.29/11.61  Inferencing          : 1.69
% 20.29/11.61  Reduction            : 7.18
% 20.29/11.61  Demodulation         : 6.75
% 20.29/11.61  BG Simplification    : 0.21
% 20.29/11.61  Subsumption          : 1.21
% 20.29/11.61  Abstraction          : 0.43
% 20.29/11.61  MUC search           : 0.00
% 20.29/11.61  Cooper               : 0.00
% 20.29/11.61  Total                : 10.89
% 20.29/11.61  Index Insertion      : 0.00
% 20.29/11.61  Index Deletion       : 0.00
% 20.29/11.61  Index Matching       : 0.00
% 20.29/11.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
