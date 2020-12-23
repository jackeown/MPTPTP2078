%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:22 EST 2020

% Result     : Theorem 15.30s
% Output     : CNFRefutation 15.45s
% Verified   : 
% Statistics : Number of formulae       :  125 (1236 expanded)
%              Number of leaves         :   35 ( 440 expanded)
%              Depth                    :   19
%              Number of atoms          :  136 (1300 expanded)
%              Number of equality atoms :   92 (1160 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(f_109,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k3_xboole_0(k2_tarski(A,B),C) = k1_tarski(A)
          & r2_hidden(B,C)
          & A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_50,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_79,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_100,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_60,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_44,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_48,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_52,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_62,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_58,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_46,axiom,(
    ! [A,B,C] : k5_xboole_0(k3_xboole_0(A,B),k3_xboole_0(C,B)) = k3_xboole_0(k5_xboole_0(A,C),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_xboole_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ( k4_xboole_0(k2_tarski(A,B),C) = k1_tarski(A)
    <=> ( ~ r2_hidden(A,C)
        & ( r2_hidden(B,C)
          | A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l38_zfmisc_1)).

tff(c_88,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_92,plain,(
    k3_xboole_0(k2_tarski('#skF_3','#skF_4'),'#skF_5') = k1_tarski('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_141,plain,(
    ! [B_67,A_68] : k3_xboole_0(B_67,A_68) = k3_xboole_0(A_68,B_67) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_30,plain,(
    ! [A_18,B_19] : r1_tarski(k3_xboole_0(A_18,B_19),A_18) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_192,plain,(
    ! [B_69,A_70] : r1_tarski(k3_xboole_0(B_69,A_70),A_70) ),
    inference(superposition,[status(thm),theory(equality)],[c_141,c_30])).

tff(c_201,plain,(
    r1_tarski(k1_tarski('#skF_3'),'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_192])).

tff(c_66,plain,(
    ! [A_38] : k2_tarski(A_38,A_38) = k1_tarski(A_38) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_306,plain,(
    ! [A_85,C_86,B_87] :
      ( r2_hidden(A_85,C_86)
      | ~ r1_tarski(k2_tarski(A_85,B_87),C_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_337,plain,(
    ! [A_88,C_89] :
      ( r2_hidden(A_88,C_89)
      | ~ r1_tarski(k1_tarski(A_88),C_89) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_306])).

tff(c_355,plain,(
    r2_hidden('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_201,c_337])).

tff(c_90,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_2456,plain,(
    ! [A_165,B_166,C_167] :
      ( r1_tarski(k2_tarski(A_165,B_166),C_167)
      | ~ r2_hidden(B_166,C_167)
      | ~ r2_hidden(A_165,C_167) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_34,plain,(
    ! [A_22,B_23] :
      ( k3_xboole_0(A_22,B_23) = A_22
      | ~ r1_tarski(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_48069,plain,(
    ! [A_674,B_675,C_676] :
      ( k3_xboole_0(k2_tarski(A_674,B_675),C_676) = k2_tarski(A_674,B_675)
      | ~ r2_hidden(B_675,C_676)
      | ~ r2_hidden(A_674,C_676) ) ),
    inference(resolution,[status(thm)],[c_2456,c_34])).

tff(c_48548,plain,
    ( k2_tarski('#skF_3','#skF_4') = k1_tarski('#skF_3')
    | ~ r2_hidden('#skF_4','#skF_5')
    | ~ r2_hidden('#skF_3','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_48069,c_92])).

tff(c_48705,plain,(
    k2_tarski('#skF_3','#skF_4') = k1_tarski('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_355,c_90,c_48548])).

tff(c_2088,plain,(
    ! [A_147,B_148,C_149] : k4_xboole_0(k3_xboole_0(A_147,B_148),C_149) = k3_xboole_0(A_147,k4_xboole_0(B_148,C_149)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_2172,plain,(
    ! [C_149] : k3_xboole_0(k2_tarski('#skF_3','#skF_4'),k4_xboole_0('#skF_5',C_149)) = k4_xboole_0(k1_tarski('#skF_3'),C_149) ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_2088])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_24,plain,(
    ! [A_10,B_11] : k5_xboole_0(A_10,k3_xboole_0(A_10,B_11)) = k4_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_255,plain,(
    ! [A_83,B_84] :
      ( k3_xboole_0(A_83,B_84) = A_83
      | ~ r1_tarski(A_83,B_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_279,plain,(
    ! [A_18,B_19] : k3_xboole_0(k3_xboole_0(A_18,B_19),A_18) = k3_xboole_0(A_18,B_19) ),
    inference(resolution,[status(thm)],[c_30,c_255])).

tff(c_430,plain,(
    ! [A_105,B_106] : k5_xboole_0(A_105,k3_xboole_0(A_105,B_106)) = k4_xboole_0(A_105,B_106) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_590,plain,(
    ! [B_114,A_115] : k5_xboole_0(B_114,k3_xboole_0(A_115,B_114)) = k4_xboole_0(B_114,A_115) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_430])).

tff(c_603,plain,(
    ! [A_18,B_19] : k5_xboole_0(A_18,k3_xboole_0(A_18,B_19)) = k4_xboole_0(A_18,k3_xboole_0(A_18,B_19)) ),
    inference(superposition,[status(thm),theory(equality)],[c_279,c_590])).

tff(c_638,plain,(
    ! [A_18,B_19] : k4_xboole_0(A_18,k3_xboole_0(A_18,B_19)) = k4_xboole_0(A_18,B_19) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_603])).

tff(c_28,plain,(
    ! [A_15,B_16,C_17] : k3_xboole_0(k3_xboole_0(A_15,B_16),C_17) = k3_xboole_0(A_15,k3_xboole_0(B_16,C_17)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_4,plain,(
    ! [A_3] : k3_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_463,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k4_xboole_0(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_430])).

tff(c_32,plain,(
    ! [A_20,B_21] : k3_xboole_0(A_20,k2_xboole_0(A_20,B_21)) = A_20 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_460,plain,(
    ! [A_20,B_21] : k4_xboole_0(A_20,k2_xboole_0(A_20,B_21)) = k5_xboole_0(A_20,A_20) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_430])).

tff(c_569,plain,(
    ! [A_20,B_21] : k4_xboole_0(A_20,k2_xboole_0(A_20,B_21)) = k4_xboole_0(A_20,A_20) ),
    inference(demodulation,[status(thm),theory(equality)],[c_463,c_460])).

tff(c_40,plain,(
    ! [A_29,B_30] : k5_xboole_0(A_29,k4_xboole_0(B_30,A_29)) = k2_xboole_0(A_29,B_30) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_36,plain,(
    ! [A_24,B_25] : k4_xboole_0(A_24,k4_xboole_0(A_24,B_25)) = k3_xboole_0(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_2477,plain,(
    ! [A_168,C_169] : k3_xboole_0(A_168,k4_xboole_0(A_168,C_169)) = k4_xboole_0(A_168,C_169) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_2088])).

tff(c_2540,plain,(
    ! [A_168,C_169] : k5_xboole_0(A_168,k4_xboole_0(A_168,C_169)) = k4_xboole_0(A_168,k4_xboole_0(A_168,C_169)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2477,c_24])).

tff(c_2584,plain,(
    ! [A_168,C_169] : k5_xboole_0(A_168,k4_xboole_0(A_168,C_169)) = k3_xboole_0(A_168,C_169) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_2540])).

tff(c_454,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_430])).

tff(c_5396,plain,(
    ! [A_239,B_240,C_241] : k5_xboole_0(k3_xboole_0(A_239,B_240),k3_xboole_0(C_241,B_240)) = k3_xboole_0(k5_xboole_0(A_239,C_241),B_240) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_5577,plain,(
    ! [A_3,C_241] : k5_xboole_0(A_3,k3_xboole_0(C_241,A_3)) = k3_xboole_0(k5_xboole_0(A_3,C_241),A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_5396])).

tff(c_5615,plain,(
    ! [A_242,C_243] : k3_xboole_0(A_242,k5_xboole_0(A_242,C_243)) = k4_xboole_0(A_242,C_243) ),
    inference(demodulation,[status(thm),theory(equality)],[c_454,c_2,c_5577])).

tff(c_5724,plain,(
    ! [A_242,C_243] : k5_xboole_0(A_242,k4_xboole_0(A_242,C_243)) = k4_xboole_0(A_242,k5_xboole_0(A_242,C_243)) ),
    inference(superposition,[status(thm),theory(equality)],[c_5615,c_24])).

tff(c_6016,plain,(
    ! [A_248,C_249] : k4_xboole_0(A_248,k5_xboole_0(A_248,C_249)) = k3_xboole_0(A_248,C_249) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2584,c_5724])).

tff(c_6134,plain,(
    ! [A_29,B_30] : k4_xboole_0(A_29,k2_xboole_0(A_29,B_30)) = k3_xboole_0(A_29,k4_xboole_0(B_30,A_29)) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_6016])).

tff(c_6160,plain,(
    ! [A_29,B_30] : k3_xboole_0(A_29,k4_xboole_0(B_30,A_29)) = k4_xboole_0(A_29,A_29) ),
    inference(demodulation,[status(thm),theory(equality)],[c_569,c_6134])).

tff(c_1138,plain,(
    ! [A_129,B_130] : k4_xboole_0(A_129,k3_xboole_0(A_129,B_130)) = k4_xboole_0(A_129,B_130) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_603])).

tff(c_1183,plain,(
    ! [B_2,A_1] : k4_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1138])).

tff(c_38,plain,(
    ! [A_26,B_27,C_28] : k4_xboole_0(k3_xboole_0(A_26,B_27),C_28) = k3_xboole_0(A_26,k4_xboole_0(B_27,C_28)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_6162,plain,(
    ! [A_250,B_251] : k3_xboole_0(A_250,k4_xboole_0(B_251,A_250)) = k4_xboole_0(A_250,A_250) ),
    inference(demodulation,[status(thm),theory(equality)],[c_569,c_6134])).

tff(c_6327,plain,(
    ! [A_18,B_19] : k4_xboole_0(k3_xboole_0(A_18,B_19),k3_xboole_0(A_18,B_19)) = k3_xboole_0(k3_xboole_0(A_18,B_19),k4_xboole_0(A_18,B_19)) ),
    inference(superposition,[status(thm),theory(equality)],[c_638,c_6162])).

tff(c_7623,plain,(
    ! [A_278,B_279] : k4_xboole_0(A_278,A_278) = k3_xboole_0(A_278,k4_xboole_0(B_279,B_279)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6160,c_6160,c_1183,c_38,c_28,c_6327])).

tff(c_5761,plain,(
    ! [A_29,B_30] : k4_xboole_0(A_29,k4_xboole_0(B_30,A_29)) = k3_xboole_0(A_29,k2_xboole_0(A_29,B_30)) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_5615])).

tff(c_5796,plain,(
    ! [A_244,B_245] : k4_xboole_0(A_244,k4_xboole_0(B_245,A_244)) = A_244 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_5761])).

tff(c_6896,plain,(
    ! [C_262,A_263,B_264] : k4_xboole_0(C_262,k3_xboole_0(A_263,k4_xboole_0(B_264,C_262))) = C_262 ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_5796])).

tff(c_7101,plain,(
    ! [C_262,B_264,A_1] : k4_xboole_0(C_262,k3_xboole_0(k4_xboole_0(B_264,C_262),A_1)) = C_262 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_6896])).

tff(c_7641,plain,(
    ! [A_278,B_279,A_1] : k4_xboole_0(A_278,k3_xboole_0(k3_xboole_0(A_278,k4_xboole_0(B_279,B_279)),A_1)) = A_278 ),
    inference(superposition,[status(thm),theory(equality)],[c_7623,c_7101])).

tff(c_13291,plain,(
    ! [A_362,B_363,A_364] : k4_xboole_0(A_362,k3_xboole_0(k4_xboole_0(B_363,B_363),A_364)) = A_362 ),
    inference(demodulation,[status(thm),theory(equality)],[c_638,c_28,c_7641])).

tff(c_13947,plain,(
    ! [A_370,A_371,B_372] : k4_xboole_0(A_370,k3_xboole_0(A_371,k4_xboole_0(B_372,B_372))) = A_370 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_13291])).

tff(c_14265,plain,(
    ! [A_370] : k4_xboole_0(A_370,k4_xboole_0(k1_tarski('#skF_3'),'#skF_5')) = A_370 ),
    inference(superposition,[status(thm),theory(equality)],[c_2172,c_13947])).

tff(c_493,plain,(
    ! [A_110,B_111] : k3_xboole_0(k3_xboole_0(A_110,B_111),A_110) = k3_xboole_0(A_110,B_111) ),
    inference(resolution,[status(thm)],[c_30,c_255])).

tff(c_542,plain,(
    ! [A_1,B_2] : k3_xboole_0(k3_xboole_0(A_1,B_2),B_2) = k3_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_493])).

tff(c_1456,plain,(
    ! [A_135,B_136,C_137] : k3_xboole_0(k3_xboole_0(A_135,B_136),C_137) = k3_xboole_0(A_135,k3_xboole_0(B_136,C_137)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_162,plain,(
    ! [B_67,A_68] : r1_tarski(k3_xboole_0(B_67,A_68),A_68) ),
    inference(superposition,[status(thm),theory(equality)],[c_141,c_30])).

tff(c_1645,plain,(
    ! [A_138,B_139,C_140] : r1_tarski(k3_xboole_0(A_138,k3_xboole_0(B_139,C_140)),C_140) ),
    inference(superposition,[status(thm),theory(equality)],[c_1456,c_162])).

tff(c_1689,plain,(
    ! [A_138,B_2,A_1] : r1_tarski(k3_xboole_0(A_138,k3_xboole_0(B_2,A_1)),B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_542,c_1645])).

tff(c_2492,plain,(
    ! [A_138,A_168,C_169] : r1_tarski(k3_xboole_0(A_138,k4_xboole_0(A_168,C_169)),A_168) ),
    inference(superposition,[status(thm),theory(equality)],[c_2477,c_1689])).

tff(c_6218,plain,(
    ! [A_250,B_251] : r1_tarski(k4_xboole_0(A_250,A_250),B_251) ),
    inference(superposition,[status(thm),theory(equality)],[c_6162,c_2492])).

tff(c_407,plain,(
    ! [B_103,A_104] :
      ( B_103 = A_104
      | ~ r1_tarski(B_103,A_104)
      | ~ r1_tarski(A_104,B_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_13727,plain,(
    ! [A_365,B_366] :
      ( k3_xboole_0(A_365,B_366) = A_365
      | ~ r1_tarski(A_365,k3_xboole_0(A_365,B_366)) ) ),
    inference(resolution,[status(thm)],[c_30,c_407])).

tff(c_14996,plain,(
    ! [A_376,B_377] : k3_xboole_0(k4_xboole_0(A_376,A_376),B_377) = k4_xboole_0(A_376,A_376) ),
    inference(resolution,[status(thm)],[c_6218,c_13727])).

tff(c_7861,plain,(
    ! [A_278,B_279] : k4_xboole_0(A_278,A_278) = k3_xboole_0(k4_xboole_0(B_279,B_279),A_278) ),
    inference(superposition,[status(thm),theory(equality)],[c_7623,c_2])).

tff(c_16359,plain,(
    ! [B_386,A_387] : k4_xboole_0(B_386,B_386) = k4_xboole_0(A_387,A_387) ),
    inference(superposition,[status(thm),theory(equality)],[c_14996,c_7861])).

tff(c_18912,plain,(
    ! [A_415] : k4_xboole_0(k1_tarski('#skF_3'),'#skF_5') = k4_xboole_0(A_415,A_415) ),
    inference(superposition,[status(thm),theory(equality)],[c_14265,c_16359])).

tff(c_6366,plain,(
    ! [A_18,B_19] : k4_xboole_0(A_18,A_18) = k3_xboole_0(A_18,k4_xboole_0(B_19,B_19)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6160,c_6160,c_1183,c_38,c_28,c_6327])).

tff(c_2607,plain,(
    ! [A_171,C_172] : r1_tarski(k4_xboole_0(A_171,C_172),A_171) ),
    inference(superposition,[status(thm),theory(equality)],[c_2477,c_30])).

tff(c_2632,plain,(
    ! [A_171,C_172] : k3_xboole_0(k4_xboole_0(A_171,C_172),A_171) = k4_xboole_0(A_171,C_172) ),
    inference(resolution,[status(thm)],[c_2607,c_34])).

tff(c_8758,plain,(
    ! [C_303,B_304,C_305] : k4_xboole_0(C_303,k4_xboole_0(k4_xboole_0(B_304,C_303),C_305)) = C_303 ),
    inference(superposition,[status(thm),theory(equality)],[c_2632,c_6896])).

tff(c_8907,plain,(
    ! [A_18,B_19,C_305] : k4_xboole_0(A_18,k4_xboole_0(k3_xboole_0(A_18,k4_xboole_0(B_19,B_19)),C_305)) = A_18 ),
    inference(superposition,[status(thm),theory(equality)],[c_6366,c_8758])).

tff(c_9047,plain,(
    ! [A_18,B_19,C_305] : k4_xboole_0(A_18,k4_xboole_0(k4_xboole_0(B_19,B_19),C_305)) = A_18 ),
    inference(demodulation,[status(thm),theory(equality)],[c_638,c_38,c_8907])).

tff(c_2282,plain,(
    ! [A_155,C_156,B_157] :
      ( ~ r2_hidden(A_155,C_156)
      | k4_xboole_0(k2_tarski(A_155,B_157),C_156) != k1_tarski(A_155) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_16924,plain,(
    ! [A_388,C_389] :
      ( ~ r2_hidden(A_388,C_389)
      | k4_xboole_0(k1_tarski(A_388),C_389) != k1_tarski(A_388) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_2282])).

tff(c_17011,plain,(
    ! [A_388,B_19,C_305] : ~ r2_hidden(A_388,k4_xboole_0(k4_xboole_0(B_19,B_19),C_305)) ),
    inference(superposition,[status(thm),theory(equality)],[c_9047,c_16924])).

tff(c_18927,plain,(
    ! [A_388] : ~ r2_hidden(A_388,k4_xboole_0(k1_tarski('#skF_3'),'#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_18912,c_17011])).

tff(c_7031,plain,(
    ! [C_262,B_264,C_172] : k4_xboole_0(C_262,k4_xboole_0(k4_xboole_0(B_264,C_262),C_172)) = C_262 ),
    inference(superposition,[status(thm),theory(equality)],[c_2632,c_6896])).

tff(c_21313,plain,(
    ! [C_427] : k4_xboole_0(C_427,k4_xboole_0(k1_tarski('#skF_3'),'#skF_5')) = C_427 ),
    inference(superposition,[status(thm),theory(equality)],[c_18912,c_7031])).

tff(c_74,plain,(
    ! [B_49,A_48,C_50] :
      ( B_49 = A_48
      | r2_hidden(B_49,C_50)
      | k4_xboole_0(k2_tarski(A_48,B_49),C_50) != k1_tarski(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_21483,plain,(
    ! [B_49,A_48] :
      ( B_49 = A_48
      | r2_hidden(B_49,k4_xboole_0(k1_tarski('#skF_3'),'#skF_5'))
      | k2_tarski(A_48,B_49) != k1_tarski(A_48) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_21313,c_74])).

tff(c_21638,plain,(
    ! [B_49,A_48] :
      ( B_49 = A_48
      | k2_tarski(A_48,B_49) != k1_tarski(A_48) ) ),
    inference(negUnitSimplification,[status(thm)],[c_18927,c_21483])).

tff(c_48799,plain,(
    '#skF_3' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_48705,c_21638])).

tff(c_48836,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_48799])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:09:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 15.30/7.80  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.30/7.81  
% 15.30/7.81  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.38/7.81  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 15.38/7.81  
% 15.38/7.81  %Foreground sorts:
% 15.38/7.81  
% 15.38/7.81  
% 15.38/7.81  %Background operators:
% 15.38/7.81  
% 15.38/7.81  
% 15.38/7.81  %Foreground operators:
% 15.38/7.81  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 15.38/7.81  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 15.38/7.81  tff(k1_tarski, type, k1_tarski: $i > $i).
% 15.38/7.81  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 15.38/7.81  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 15.38/7.81  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 15.38/7.81  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 15.38/7.81  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 15.38/7.81  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 15.38/7.81  tff('#skF_5', type, '#skF_5': $i).
% 15.38/7.81  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 15.38/7.81  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 15.38/7.81  tff('#skF_3', type, '#skF_3': $i).
% 15.38/7.81  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 15.38/7.81  tff('#skF_4', type, '#skF_4': $i).
% 15.38/7.81  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 15.38/7.81  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 15.38/7.81  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 15.38/7.81  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 15.38/7.81  
% 15.45/7.84  tff(f_109, negated_conjecture, ~(![A, B, C]: ~(((k3_xboole_0(k2_tarski(A, B), C) = k1_tarski(A)) & r2_hidden(B, C)) & ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_zfmisc_1)).
% 15.45/7.84  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 15.45/7.84  tff(f_50, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 15.45/7.84  tff(f_79, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 15.45/7.84  tff(f_100, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 15.45/7.84  tff(f_56, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 15.45/7.84  tff(f_60, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 15.45/7.84  tff(f_44, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 15.45/7.84  tff(f_48, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_xboole_1)).
% 15.45/7.84  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 15.45/7.84  tff(f_52, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_xboole_1)).
% 15.45/7.84  tff(f_62, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 15.45/7.84  tff(f_58, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 15.45/7.84  tff(f_46, axiom, (![A, B, C]: (k5_xboole_0(k3_xboole_0(A, B), k3_xboole_0(C, B)) = k3_xboole_0(k5_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t112_xboole_1)).
% 15.45/7.84  tff(f_42, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 15.45/7.84  tff(f_94, axiom, (![A, B, C]: ((k4_xboole_0(k2_tarski(A, B), C) = k1_tarski(A)) <=> (~r2_hidden(A, C) & (r2_hidden(B, C) | (A = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l38_zfmisc_1)).
% 15.45/7.84  tff(c_88, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_109])).
% 15.45/7.84  tff(c_92, plain, (k3_xboole_0(k2_tarski('#skF_3', '#skF_4'), '#skF_5')=k1_tarski('#skF_3')), inference(cnfTransformation, [status(thm)], [f_109])).
% 15.45/7.84  tff(c_141, plain, (![B_67, A_68]: (k3_xboole_0(B_67, A_68)=k3_xboole_0(A_68, B_67))), inference(cnfTransformation, [status(thm)], [f_27])).
% 15.45/7.84  tff(c_30, plain, (![A_18, B_19]: (r1_tarski(k3_xboole_0(A_18, B_19), A_18))), inference(cnfTransformation, [status(thm)], [f_50])).
% 15.45/7.84  tff(c_192, plain, (![B_69, A_70]: (r1_tarski(k3_xboole_0(B_69, A_70), A_70))), inference(superposition, [status(thm), theory('equality')], [c_141, c_30])).
% 15.45/7.84  tff(c_201, plain, (r1_tarski(k1_tarski('#skF_3'), '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_92, c_192])).
% 15.45/7.84  tff(c_66, plain, (![A_38]: (k2_tarski(A_38, A_38)=k1_tarski(A_38))), inference(cnfTransformation, [status(thm)], [f_79])).
% 15.45/7.84  tff(c_306, plain, (![A_85, C_86, B_87]: (r2_hidden(A_85, C_86) | ~r1_tarski(k2_tarski(A_85, B_87), C_86))), inference(cnfTransformation, [status(thm)], [f_100])).
% 15.45/7.84  tff(c_337, plain, (![A_88, C_89]: (r2_hidden(A_88, C_89) | ~r1_tarski(k1_tarski(A_88), C_89))), inference(superposition, [status(thm), theory('equality')], [c_66, c_306])).
% 15.45/7.84  tff(c_355, plain, (r2_hidden('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_201, c_337])).
% 15.45/7.84  tff(c_90, plain, (r2_hidden('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_109])).
% 15.45/7.84  tff(c_2456, plain, (![A_165, B_166, C_167]: (r1_tarski(k2_tarski(A_165, B_166), C_167) | ~r2_hidden(B_166, C_167) | ~r2_hidden(A_165, C_167))), inference(cnfTransformation, [status(thm)], [f_100])).
% 15.45/7.84  tff(c_34, plain, (![A_22, B_23]: (k3_xboole_0(A_22, B_23)=A_22 | ~r1_tarski(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_56])).
% 15.45/7.84  tff(c_48069, plain, (![A_674, B_675, C_676]: (k3_xboole_0(k2_tarski(A_674, B_675), C_676)=k2_tarski(A_674, B_675) | ~r2_hidden(B_675, C_676) | ~r2_hidden(A_674, C_676))), inference(resolution, [status(thm)], [c_2456, c_34])).
% 15.45/7.84  tff(c_48548, plain, (k2_tarski('#skF_3', '#skF_4')=k1_tarski('#skF_3') | ~r2_hidden('#skF_4', '#skF_5') | ~r2_hidden('#skF_3', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_48069, c_92])).
% 15.45/7.84  tff(c_48705, plain, (k2_tarski('#skF_3', '#skF_4')=k1_tarski('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_355, c_90, c_48548])).
% 15.45/7.84  tff(c_2088, plain, (![A_147, B_148, C_149]: (k4_xboole_0(k3_xboole_0(A_147, B_148), C_149)=k3_xboole_0(A_147, k4_xboole_0(B_148, C_149)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 15.45/7.84  tff(c_2172, plain, (![C_149]: (k3_xboole_0(k2_tarski('#skF_3', '#skF_4'), k4_xboole_0('#skF_5', C_149))=k4_xboole_0(k1_tarski('#skF_3'), C_149))), inference(superposition, [status(thm), theory('equality')], [c_92, c_2088])).
% 15.45/7.84  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 15.45/7.84  tff(c_24, plain, (![A_10, B_11]: (k5_xboole_0(A_10, k3_xboole_0(A_10, B_11))=k4_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_44])).
% 15.45/7.84  tff(c_255, plain, (![A_83, B_84]: (k3_xboole_0(A_83, B_84)=A_83 | ~r1_tarski(A_83, B_84))), inference(cnfTransformation, [status(thm)], [f_56])).
% 15.45/7.84  tff(c_279, plain, (![A_18, B_19]: (k3_xboole_0(k3_xboole_0(A_18, B_19), A_18)=k3_xboole_0(A_18, B_19))), inference(resolution, [status(thm)], [c_30, c_255])).
% 15.45/7.84  tff(c_430, plain, (![A_105, B_106]: (k5_xboole_0(A_105, k3_xboole_0(A_105, B_106))=k4_xboole_0(A_105, B_106))), inference(cnfTransformation, [status(thm)], [f_44])).
% 15.45/7.84  tff(c_590, plain, (![B_114, A_115]: (k5_xboole_0(B_114, k3_xboole_0(A_115, B_114))=k4_xboole_0(B_114, A_115))), inference(superposition, [status(thm), theory('equality')], [c_2, c_430])).
% 15.45/7.84  tff(c_603, plain, (![A_18, B_19]: (k5_xboole_0(A_18, k3_xboole_0(A_18, B_19))=k4_xboole_0(A_18, k3_xboole_0(A_18, B_19)))), inference(superposition, [status(thm), theory('equality')], [c_279, c_590])).
% 15.45/7.84  tff(c_638, plain, (![A_18, B_19]: (k4_xboole_0(A_18, k3_xboole_0(A_18, B_19))=k4_xboole_0(A_18, B_19))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_603])).
% 15.45/7.84  tff(c_28, plain, (![A_15, B_16, C_17]: (k3_xboole_0(k3_xboole_0(A_15, B_16), C_17)=k3_xboole_0(A_15, k3_xboole_0(B_16, C_17)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 15.45/7.84  tff(c_4, plain, (![A_3]: (k3_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 15.45/7.84  tff(c_463, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k4_xboole_0(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_430])).
% 15.45/7.84  tff(c_32, plain, (![A_20, B_21]: (k3_xboole_0(A_20, k2_xboole_0(A_20, B_21))=A_20)), inference(cnfTransformation, [status(thm)], [f_52])).
% 15.45/7.84  tff(c_460, plain, (![A_20, B_21]: (k4_xboole_0(A_20, k2_xboole_0(A_20, B_21))=k5_xboole_0(A_20, A_20))), inference(superposition, [status(thm), theory('equality')], [c_32, c_430])).
% 15.45/7.84  tff(c_569, plain, (![A_20, B_21]: (k4_xboole_0(A_20, k2_xboole_0(A_20, B_21))=k4_xboole_0(A_20, A_20))), inference(demodulation, [status(thm), theory('equality')], [c_463, c_460])).
% 15.45/7.84  tff(c_40, plain, (![A_29, B_30]: (k5_xboole_0(A_29, k4_xboole_0(B_30, A_29))=k2_xboole_0(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_62])).
% 15.45/7.84  tff(c_36, plain, (![A_24, B_25]: (k4_xboole_0(A_24, k4_xboole_0(A_24, B_25))=k3_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_58])).
% 15.45/7.84  tff(c_2477, plain, (![A_168, C_169]: (k3_xboole_0(A_168, k4_xboole_0(A_168, C_169))=k4_xboole_0(A_168, C_169))), inference(superposition, [status(thm), theory('equality')], [c_4, c_2088])).
% 15.45/7.84  tff(c_2540, plain, (![A_168, C_169]: (k5_xboole_0(A_168, k4_xboole_0(A_168, C_169))=k4_xboole_0(A_168, k4_xboole_0(A_168, C_169)))), inference(superposition, [status(thm), theory('equality')], [c_2477, c_24])).
% 15.45/7.84  tff(c_2584, plain, (![A_168, C_169]: (k5_xboole_0(A_168, k4_xboole_0(A_168, C_169))=k3_xboole_0(A_168, C_169))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_2540])).
% 15.45/7.84  tff(c_454, plain, (![B_2, A_1]: (k5_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_430])).
% 15.45/7.84  tff(c_5396, plain, (![A_239, B_240, C_241]: (k5_xboole_0(k3_xboole_0(A_239, B_240), k3_xboole_0(C_241, B_240))=k3_xboole_0(k5_xboole_0(A_239, C_241), B_240))), inference(cnfTransformation, [status(thm)], [f_46])).
% 15.45/7.84  tff(c_5577, plain, (![A_3, C_241]: (k5_xboole_0(A_3, k3_xboole_0(C_241, A_3))=k3_xboole_0(k5_xboole_0(A_3, C_241), A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_5396])).
% 15.45/7.84  tff(c_5615, plain, (![A_242, C_243]: (k3_xboole_0(A_242, k5_xboole_0(A_242, C_243))=k4_xboole_0(A_242, C_243))), inference(demodulation, [status(thm), theory('equality')], [c_454, c_2, c_5577])).
% 15.45/7.84  tff(c_5724, plain, (![A_242, C_243]: (k5_xboole_0(A_242, k4_xboole_0(A_242, C_243))=k4_xboole_0(A_242, k5_xboole_0(A_242, C_243)))), inference(superposition, [status(thm), theory('equality')], [c_5615, c_24])).
% 15.45/7.84  tff(c_6016, plain, (![A_248, C_249]: (k4_xboole_0(A_248, k5_xboole_0(A_248, C_249))=k3_xboole_0(A_248, C_249))), inference(demodulation, [status(thm), theory('equality')], [c_2584, c_5724])).
% 15.45/7.84  tff(c_6134, plain, (![A_29, B_30]: (k4_xboole_0(A_29, k2_xboole_0(A_29, B_30))=k3_xboole_0(A_29, k4_xboole_0(B_30, A_29)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_6016])).
% 15.45/7.84  tff(c_6160, plain, (![A_29, B_30]: (k3_xboole_0(A_29, k4_xboole_0(B_30, A_29))=k4_xboole_0(A_29, A_29))), inference(demodulation, [status(thm), theory('equality')], [c_569, c_6134])).
% 15.45/7.84  tff(c_1138, plain, (![A_129, B_130]: (k4_xboole_0(A_129, k3_xboole_0(A_129, B_130))=k4_xboole_0(A_129, B_130))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_603])).
% 15.45/7.84  tff(c_1183, plain, (![B_2, A_1]: (k4_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1138])).
% 15.45/7.84  tff(c_38, plain, (![A_26, B_27, C_28]: (k4_xboole_0(k3_xboole_0(A_26, B_27), C_28)=k3_xboole_0(A_26, k4_xboole_0(B_27, C_28)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 15.45/7.84  tff(c_6162, plain, (![A_250, B_251]: (k3_xboole_0(A_250, k4_xboole_0(B_251, A_250))=k4_xboole_0(A_250, A_250))), inference(demodulation, [status(thm), theory('equality')], [c_569, c_6134])).
% 15.45/7.84  tff(c_6327, plain, (![A_18, B_19]: (k4_xboole_0(k3_xboole_0(A_18, B_19), k3_xboole_0(A_18, B_19))=k3_xboole_0(k3_xboole_0(A_18, B_19), k4_xboole_0(A_18, B_19)))), inference(superposition, [status(thm), theory('equality')], [c_638, c_6162])).
% 15.45/7.84  tff(c_7623, plain, (![A_278, B_279]: (k4_xboole_0(A_278, A_278)=k3_xboole_0(A_278, k4_xboole_0(B_279, B_279)))), inference(demodulation, [status(thm), theory('equality')], [c_6160, c_6160, c_1183, c_38, c_28, c_6327])).
% 15.45/7.84  tff(c_5761, plain, (![A_29, B_30]: (k4_xboole_0(A_29, k4_xboole_0(B_30, A_29))=k3_xboole_0(A_29, k2_xboole_0(A_29, B_30)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_5615])).
% 15.45/7.84  tff(c_5796, plain, (![A_244, B_245]: (k4_xboole_0(A_244, k4_xboole_0(B_245, A_244))=A_244)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_5761])).
% 15.45/7.84  tff(c_6896, plain, (![C_262, A_263, B_264]: (k4_xboole_0(C_262, k3_xboole_0(A_263, k4_xboole_0(B_264, C_262)))=C_262)), inference(superposition, [status(thm), theory('equality')], [c_38, c_5796])).
% 15.45/7.84  tff(c_7101, plain, (![C_262, B_264, A_1]: (k4_xboole_0(C_262, k3_xboole_0(k4_xboole_0(B_264, C_262), A_1))=C_262)), inference(superposition, [status(thm), theory('equality')], [c_2, c_6896])).
% 15.45/7.84  tff(c_7641, plain, (![A_278, B_279, A_1]: (k4_xboole_0(A_278, k3_xboole_0(k3_xboole_0(A_278, k4_xboole_0(B_279, B_279)), A_1))=A_278)), inference(superposition, [status(thm), theory('equality')], [c_7623, c_7101])).
% 15.45/7.84  tff(c_13291, plain, (![A_362, B_363, A_364]: (k4_xboole_0(A_362, k3_xboole_0(k4_xboole_0(B_363, B_363), A_364))=A_362)), inference(demodulation, [status(thm), theory('equality')], [c_638, c_28, c_7641])).
% 15.45/7.84  tff(c_13947, plain, (![A_370, A_371, B_372]: (k4_xboole_0(A_370, k3_xboole_0(A_371, k4_xboole_0(B_372, B_372)))=A_370)), inference(superposition, [status(thm), theory('equality')], [c_2, c_13291])).
% 15.45/7.84  tff(c_14265, plain, (![A_370]: (k4_xboole_0(A_370, k4_xboole_0(k1_tarski('#skF_3'), '#skF_5'))=A_370)), inference(superposition, [status(thm), theory('equality')], [c_2172, c_13947])).
% 15.45/7.84  tff(c_493, plain, (![A_110, B_111]: (k3_xboole_0(k3_xboole_0(A_110, B_111), A_110)=k3_xboole_0(A_110, B_111))), inference(resolution, [status(thm)], [c_30, c_255])).
% 15.45/7.84  tff(c_542, plain, (![A_1, B_2]: (k3_xboole_0(k3_xboole_0(A_1, B_2), B_2)=k3_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_493])).
% 15.45/7.84  tff(c_1456, plain, (![A_135, B_136, C_137]: (k3_xboole_0(k3_xboole_0(A_135, B_136), C_137)=k3_xboole_0(A_135, k3_xboole_0(B_136, C_137)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 15.45/7.84  tff(c_162, plain, (![B_67, A_68]: (r1_tarski(k3_xboole_0(B_67, A_68), A_68))), inference(superposition, [status(thm), theory('equality')], [c_141, c_30])).
% 15.45/7.84  tff(c_1645, plain, (![A_138, B_139, C_140]: (r1_tarski(k3_xboole_0(A_138, k3_xboole_0(B_139, C_140)), C_140))), inference(superposition, [status(thm), theory('equality')], [c_1456, c_162])).
% 15.45/7.84  tff(c_1689, plain, (![A_138, B_2, A_1]: (r1_tarski(k3_xboole_0(A_138, k3_xboole_0(B_2, A_1)), B_2))), inference(superposition, [status(thm), theory('equality')], [c_542, c_1645])).
% 15.45/7.84  tff(c_2492, plain, (![A_138, A_168, C_169]: (r1_tarski(k3_xboole_0(A_138, k4_xboole_0(A_168, C_169)), A_168))), inference(superposition, [status(thm), theory('equality')], [c_2477, c_1689])).
% 15.45/7.84  tff(c_6218, plain, (![A_250, B_251]: (r1_tarski(k4_xboole_0(A_250, A_250), B_251))), inference(superposition, [status(thm), theory('equality')], [c_6162, c_2492])).
% 15.45/7.84  tff(c_407, plain, (![B_103, A_104]: (B_103=A_104 | ~r1_tarski(B_103, A_104) | ~r1_tarski(A_104, B_103))), inference(cnfTransformation, [status(thm)], [f_42])).
% 15.45/7.84  tff(c_13727, plain, (![A_365, B_366]: (k3_xboole_0(A_365, B_366)=A_365 | ~r1_tarski(A_365, k3_xboole_0(A_365, B_366)))), inference(resolution, [status(thm)], [c_30, c_407])).
% 15.45/7.84  tff(c_14996, plain, (![A_376, B_377]: (k3_xboole_0(k4_xboole_0(A_376, A_376), B_377)=k4_xboole_0(A_376, A_376))), inference(resolution, [status(thm)], [c_6218, c_13727])).
% 15.45/7.84  tff(c_7861, plain, (![A_278, B_279]: (k4_xboole_0(A_278, A_278)=k3_xboole_0(k4_xboole_0(B_279, B_279), A_278))), inference(superposition, [status(thm), theory('equality')], [c_7623, c_2])).
% 15.45/7.84  tff(c_16359, plain, (![B_386, A_387]: (k4_xboole_0(B_386, B_386)=k4_xboole_0(A_387, A_387))), inference(superposition, [status(thm), theory('equality')], [c_14996, c_7861])).
% 15.45/7.84  tff(c_18912, plain, (![A_415]: (k4_xboole_0(k1_tarski('#skF_3'), '#skF_5')=k4_xboole_0(A_415, A_415))), inference(superposition, [status(thm), theory('equality')], [c_14265, c_16359])).
% 15.45/7.84  tff(c_6366, plain, (![A_18, B_19]: (k4_xboole_0(A_18, A_18)=k3_xboole_0(A_18, k4_xboole_0(B_19, B_19)))), inference(demodulation, [status(thm), theory('equality')], [c_6160, c_6160, c_1183, c_38, c_28, c_6327])).
% 15.45/7.84  tff(c_2607, plain, (![A_171, C_172]: (r1_tarski(k4_xboole_0(A_171, C_172), A_171))), inference(superposition, [status(thm), theory('equality')], [c_2477, c_30])).
% 15.45/7.84  tff(c_2632, plain, (![A_171, C_172]: (k3_xboole_0(k4_xboole_0(A_171, C_172), A_171)=k4_xboole_0(A_171, C_172))), inference(resolution, [status(thm)], [c_2607, c_34])).
% 15.45/7.84  tff(c_8758, plain, (![C_303, B_304, C_305]: (k4_xboole_0(C_303, k4_xboole_0(k4_xboole_0(B_304, C_303), C_305))=C_303)), inference(superposition, [status(thm), theory('equality')], [c_2632, c_6896])).
% 15.45/7.84  tff(c_8907, plain, (![A_18, B_19, C_305]: (k4_xboole_0(A_18, k4_xboole_0(k3_xboole_0(A_18, k4_xboole_0(B_19, B_19)), C_305))=A_18)), inference(superposition, [status(thm), theory('equality')], [c_6366, c_8758])).
% 15.45/7.84  tff(c_9047, plain, (![A_18, B_19, C_305]: (k4_xboole_0(A_18, k4_xboole_0(k4_xboole_0(B_19, B_19), C_305))=A_18)), inference(demodulation, [status(thm), theory('equality')], [c_638, c_38, c_8907])).
% 15.45/7.84  tff(c_2282, plain, (![A_155, C_156, B_157]: (~r2_hidden(A_155, C_156) | k4_xboole_0(k2_tarski(A_155, B_157), C_156)!=k1_tarski(A_155))), inference(cnfTransformation, [status(thm)], [f_94])).
% 15.45/7.84  tff(c_16924, plain, (![A_388, C_389]: (~r2_hidden(A_388, C_389) | k4_xboole_0(k1_tarski(A_388), C_389)!=k1_tarski(A_388))), inference(superposition, [status(thm), theory('equality')], [c_66, c_2282])).
% 15.45/7.84  tff(c_17011, plain, (![A_388, B_19, C_305]: (~r2_hidden(A_388, k4_xboole_0(k4_xboole_0(B_19, B_19), C_305)))), inference(superposition, [status(thm), theory('equality')], [c_9047, c_16924])).
% 15.45/7.84  tff(c_18927, plain, (![A_388]: (~r2_hidden(A_388, k4_xboole_0(k1_tarski('#skF_3'), '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_18912, c_17011])).
% 15.45/7.84  tff(c_7031, plain, (![C_262, B_264, C_172]: (k4_xboole_0(C_262, k4_xboole_0(k4_xboole_0(B_264, C_262), C_172))=C_262)), inference(superposition, [status(thm), theory('equality')], [c_2632, c_6896])).
% 15.45/7.84  tff(c_21313, plain, (![C_427]: (k4_xboole_0(C_427, k4_xboole_0(k1_tarski('#skF_3'), '#skF_5'))=C_427)), inference(superposition, [status(thm), theory('equality')], [c_18912, c_7031])).
% 15.45/7.84  tff(c_74, plain, (![B_49, A_48, C_50]: (B_49=A_48 | r2_hidden(B_49, C_50) | k4_xboole_0(k2_tarski(A_48, B_49), C_50)!=k1_tarski(A_48))), inference(cnfTransformation, [status(thm)], [f_94])).
% 15.45/7.84  tff(c_21483, plain, (![B_49, A_48]: (B_49=A_48 | r2_hidden(B_49, k4_xboole_0(k1_tarski('#skF_3'), '#skF_5')) | k2_tarski(A_48, B_49)!=k1_tarski(A_48))), inference(superposition, [status(thm), theory('equality')], [c_21313, c_74])).
% 15.45/7.84  tff(c_21638, plain, (![B_49, A_48]: (B_49=A_48 | k2_tarski(A_48, B_49)!=k1_tarski(A_48))), inference(negUnitSimplification, [status(thm)], [c_18927, c_21483])).
% 15.45/7.84  tff(c_48799, plain, ('#skF_3'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_48705, c_21638])).
% 15.45/7.84  tff(c_48836, plain, $false, inference(negUnitSimplification, [status(thm)], [c_88, c_48799])).
% 15.45/7.84  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.45/7.84  
% 15.45/7.84  Inference rules
% 15.45/7.84  ----------------------
% 15.45/7.84  #Ref     : 0
% 15.45/7.84  #Sup     : 11895
% 15.45/7.84  #Fact    : 0
% 15.45/7.84  #Define  : 0
% 15.45/7.84  #Split   : 1
% 15.45/7.84  #Chain   : 0
% 15.45/7.84  #Close   : 0
% 15.45/7.84  
% 15.45/7.84  Ordering : KBO
% 15.45/7.84  
% 15.45/7.84  Simplification rules
% 15.45/7.84  ----------------------
% 15.45/7.84  #Subsume      : 1430
% 15.45/7.84  #Demod        : 9890
% 15.45/7.84  #Tautology    : 5924
% 15.45/7.84  #SimpNegUnit  : 166
% 15.45/7.84  #BackRed      : 55
% 15.45/7.84  
% 15.45/7.84  #Partial instantiations: 0
% 15.45/7.84  #Strategies tried      : 1
% 15.45/7.84  
% 15.45/7.84  Timing (in seconds)
% 15.45/7.84  ----------------------
% 15.45/7.84  Preprocessing        : 0.38
% 15.45/7.84  Parsing              : 0.19
% 15.45/7.84  CNF conversion       : 0.03
% 15.45/7.84  Main loop            : 6.65
% 15.45/7.84  Inferencing          : 1.00
% 15.45/7.84  Reduction            : 4.04
% 15.45/7.84  Demodulation         : 3.56
% 15.45/7.84  BG Simplification    : 0.14
% 15.45/7.84  Subsumption          : 1.15
% 15.45/7.84  Abstraction          : 0.20
% 15.45/7.84  MUC search           : 0.00
% 15.45/7.84  Cooper               : 0.00
% 15.45/7.84  Total                : 7.08
% 15.45/7.84  Index Insertion      : 0.00
% 15.45/7.84  Index Deletion       : 0.00
% 15.45/7.84  Index Matching       : 0.00
% 15.45/7.84  BG Taut test         : 0.00
%------------------------------------------------------------------------------
