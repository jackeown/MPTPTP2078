%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:50 EST 2020

% Result     : Theorem 7.21s
% Output     : CNFRefutation 7.21s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 907 expanded)
%              Number of leaves         :   29 ( 318 expanded)
%              Depth                    :   21
%              Number of atoms          :  136 (1176 expanded)
%              Number of equality atoms :   90 ( 717 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_79,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,C) )
       => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_xboole_1)).

tff(f_64,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_62,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_70,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_68,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_58,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_72,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_66,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_60,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(c_36,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_26,plain,(
    ! [A_22,B_23] : k4_xboole_0(k2_xboole_0(A_22,B_23),B_23) = k4_xboole_0(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_354,plain,(
    ! [A_62,B_63] :
      ( r2_hidden('#skF_1'(A_62,B_63),A_62)
      | r1_tarski(A_62,B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_24,plain,(
    ! [A_21] : k4_xboole_0(A_21,k1_xboole_0) = A_21 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_32,plain,(
    ! [A_29] : r1_xboole_0(A_29,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_147,plain,(
    ! [A_44,B_45] :
      ( k3_xboole_0(A_44,B_45) = k1_xboole_0
      | ~ r1_xboole_0(A_44,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_154,plain,(
    ! [A_29] : k3_xboole_0(A_29,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32,c_147])).

tff(c_258,plain,(
    ! [A_54,B_55] : k4_xboole_0(A_54,k4_xboole_0(A_54,B_55)) = k3_xboole_0(A_54,B_55) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_273,plain,(
    ! [A_21] : k4_xboole_0(A_21,A_21) = k3_xboole_0(A_21,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_258])).

tff(c_277,plain,(
    ! [A_56] : k4_xboole_0(A_56,A_56) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_273])).

tff(c_30,plain,(
    ! [A_27,B_28] : k4_xboole_0(A_27,k4_xboole_0(A_27,B_28)) = k3_xboole_0(A_27,B_28) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_282,plain,(
    ! [A_56] : k4_xboole_0(A_56,k1_xboole_0) = k3_xboole_0(A_56,A_56) ),
    inference(superposition,[status(thm),theory(equality)],[c_277,c_30])).

tff(c_294,plain,(
    ! [A_56] : k3_xboole_0(A_56,A_56) = A_56 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_282])).

tff(c_14,plain,(
    ! [A_10,B_11] :
      ( r1_xboole_0(A_10,B_11)
      | k3_xboole_0(A_10,B_11) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_298,plain,(
    ! [A_57] : k3_xboole_0(A_57,A_57) = A_57 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_282])).

tff(c_18,plain,(
    ! [A_12,B_13,C_16] :
      ( ~ r1_xboole_0(A_12,B_13)
      | ~ r2_hidden(C_16,k3_xboole_0(A_12,B_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_330,plain,(
    ! [A_58,C_59] :
      ( ~ r1_xboole_0(A_58,A_58)
      | ~ r2_hidden(C_59,A_58) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_298,c_18])).

tff(c_333,plain,(
    ! [C_59,B_11] :
      ( ~ r2_hidden(C_59,B_11)
      | k3_xboole_0(B_11,B_11) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_14,c_330])).

tff(c_338,plain,(
    ! [C_59,B_11] :
      ( ~ r2_hidden(C_59,B_11)
      | k1_xboole_0 != B_11 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_294,c_333])).

tff(c_535,plain,(
    ! [A_71,B_72] :
      ( k1_xboole_0 != A_71
      | r1_tarski(A_71,B_72) ) ),
    inference(resolution,[status(thm)],[c_354,c_338])).

tff(c_20,plain,(
    ! [A_17,B_18] :
      ( k2_xboole_0(A_17,B_18) = B_18
      | ~ r1_tarski(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_542,plain,(
    ! [A_71,B_72] :
      ( k2_xboole_0(A_71,B_72) = B_72
      | k1_xboole_0 != A_71 ) ),
    inference(resolution,[status(thm)],[c_535,c_20])).

tff(c_547,plain,(
    ! [A_73,B_74] :
      ( k2_xboole_0(A_73,B_74) = B_74
      | k1_xboole_0 != A_73 ) ),
    inference(resolution,[status(thm)],[c_535,c_20])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_618,plain,(
    ! [B_74] : k2_xboole_0(B_74,k1_xboole_0) = B_74 ),
    inference(superposition,[status(thm),theory(equality)],[c_547,c_2])).

tff(c_38,plain,(
    r1_xboole_0('#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_155,plain,(
    k3_xboole_0('#skF_3','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_38,c_147])).

tff(c_237,plain,(
    ! [A_50,B_51,C_52] :
      ( ~ r1_xboole_0(A_50,B_51)
      | ~ r2_hidden(C_52,k3_xboole_0(A_50,B_51)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_243,plain,(
    ! [C_52] :
      ( ~ r1_xboole_0('#skF_3','#skF_5')
      | ~ r2_hidden(C_52,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_155,c_237])).

tff(c_254,plain,(
    ! [C_52] : ~ r2_hidden(C_52,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_243])).

tff(c_369,plain,(
    ! [B_64] : r1_tarski(k1_xboole_0,B_64) ),
    inference(resolution,[status(thm)],[c_354,c_254])).

tff(c_374,plain,(
    ! [B_65] : k2_xboole_0(k1_xboole_0,B_65) = B_65 ),
    inference(resolution,[status(thm)],[c_369,c_20])).

tff(c_52,plain,(
    ! [B_36,A_37] : k2_xboole_0(B_36,A_37) = k2_xboole_0(A_37,B_36) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_34,plain,(
    ! [A_30,B_31] : r1_tarski(A_30,k2_xboole_0(A_30,B_31)) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_67,plain,(
    ! [A_37,B_36] : r1_tarski(A_37,k2_xboole_0(B_36,A_37)) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_34])).

tff(c_405,plain,(
    ! [B_66] : r1_tarski(B_66,B_66) ),
    inference(superposition,[status(thm),theory(equality)],[c_374,c_67])).

tff(c_409,plain,(
    ! [B_66] : k2_xboole_0(B_66,B_66) = B_66 ),
    inference(resolution,[status(thm)],[c_405,c_20])).

tff(c_28,plain,(
    ! [A_24,B_25,C_26] : k4_xboole_0(k4_xboole_0(A_24,B_25),C_26) = k4_xboole_0(A_24,k2_xboole_0(B_25,C_26)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_22,plain,(
    ! [A_19,B_20] : k2_xboole_0(A_19,k4_xboole_0(B_20,A_19)) = k2_xboole_0(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1304,plain,(
    ! [A_110,B_111,C_112] : k4_xboole_0(k4_xboole_0(A_110,B_111),C_112) = k4_xboole_0(A_110,k2_xboole_0(B_111,C_112)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_276,plain,(
    ! [A_21] : k4_xboole_0(A_21,A_21) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_273])).

tff(c_1332,plain,(
    ! [A_110,B_111] : k4_xboole_0(A_110,k2_xboole_0(B_111,k4_xboole_0(A_110,B_111))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1304,c_276])).

tff(c_1399,plain,(
    ! [A_113,B_114] : k4_xboole_0(A_113,k2_xboole_0(B_114,A_113)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_1332])).

tff(c_1450,plain,(
    ! [B_20,A_19] : k4_xboole_0(k4_xboole_0(B_20,A_19),k2_xboole_0(A_19,B_20)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_1399])).

tff(c_5423,plain,(
    ! [C_194,A_195,B_196] : k2_xboole_0(C_194,k4_xboole_0(A_195,k2_xboole_0(B_196,C_194))) = k2_xboole_0(C_194,k4_xboole_0(A_195,B_196)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1304,c_22])).

tff(c_5548,plain,(
    ! [B_20,A_19] : k2_xboole_0(B_20,k4_xboole_0(k4_xboole_0(B_20,A_19),A_19)) = k2_xboole_0(B_20,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1450,c_5423])).

tff(c_5673,plain,(
    ! [B_197,A_198] : k2_xboole_0(B_197,k4_xboole_0(B_197,A_198)) = B_197 ),
    inference(demodulation,[status(thm),theory(equality)],[c_618,c_409,c_28,c_5548])).

tff(c_7446,plain,(
    ! [A_213,A_214] :
      ( k4_xboole_0(A_213,A_214) = A_213
      | k1_xboole_0 != A_213 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_542,c_5673])).

tff(c_1429,plain,(
    ! [A_113,B_114] : k3_xboole_0(A_113,k2_xboole_0(B_114,A_113)) = k4_xboole_0(A_113,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1399,c_30])).

tff(c_1475,plain,(
    ! [A_115,B_116] : k3_xboole_0(A_115,k2_xboole_0(B_116,A_115)) = A_115 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_1429])).

tff(c_1536,plain,(
    ! [A_1,B_2] : k3_xboole_0(A_1,k2_xboole_0(A_1,B_2)) = A_1 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1475])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_689,plain,(
    ! [A_81,B_82] : k4_xboole_0(k2_xboole_0(A_81,B_82),B_82) = k4_xboole_0(A_81,B_82) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1735,plain,(
    ! [A_121,B_122] : k4_xboole_0(k2_xboole_0(A_121,B_122),A_121) = k4_xboole_0(B_122,A_121) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_689])).

tff(c_1766,plain,(
    ! [A_121,B_122] : k4_xboole_0(k2_xboole_0(A_121,B_122),k4_xboole_0(B_122,A_121)) = k3_xboole_0(k2_xboole_0(A_121,B_122),A_121) ),
    inference(superposition,[status(thm),theory(equality)],[c_1735,c_30])).

tff(c_1813,plain,(
    ! [A_121,B_122] : k4_xboole_0(k2_xboole_0(A_121,B_122),k4_xboole_0(B_122,A_121)) = A_121 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1536,c_4,c_1766])).

tff(c_7501,plain,(
    ! [A_214,A_213] :
      ( k4_xboole_0(k2_xboole_0(A_214,A_213),A_213) = A_214
      | k1_xboole_0 != A_213 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7446,c_1813])).

tff(c_8435,plain,(
    ! [A_214] : k4_xboole_0(A_214,k1_xboole_0) = A_214 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_7501])).

tff(c_7017,plain,(
    ! [A_209,B_210] : k2_xboole_0(A_209,k3_xboole_0(A_209,B_210)) = A_209 ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_5673])).

tff(c_7178,plain,(
    ! [B_4,A_3] : k2_xboole_0(B_4,k3_xboole_0(A_3,B_4)) = B_4 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_7017])).

tff(c_1456,plain,(
    ! [B_2,A_1] : k4_xboole_0(B_2,k2_xboole_0(B_2,A_1)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1399])).

tff(c_410,plain,(
    ! [A_67,B_68] : k2_xboole_0(A_67,k4_xboole_0(B_68,A_67)) = k2_xboole_0(A_67,B_68) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_436,plain,(
    ! [A_27,B_28] : k2_xboole_0(k4_xboole_0(A_27,B_28),k3_xboole_0(A_27,B_28)) = k2_xboole_0(k4_xboole_0(A_27,B_28),A_27) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_410])).

tff(c_4798,plain,(
    ! [A_187,B_188] : k2_xboole_0(k4_xboole_0(A_187,B_188),k3_xboole_0(A_187,B_188)) = k2_xboole_0(A_187,k4_xboole_0(A_187,B_188)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_436])).

tff(c_4996,plain,(
    k2_xboole_0(k4_xboole_0('#skF_3','#skF_5'),k1_xboole_0) = k2_xboole_0('#skF_3',k4_xboole_0('#skF_3','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_155,c_4798])).

tff(c_5053,plain,(
    k2_xboole_0('#skF_3',k4_xboole_0('#skF_3','#skF_5')) = k4_xboole_0('#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_618,c_4996])).

tff(c_5158,plain,(
    k4_xboole_0(k4_xboole_0('#skF_3','#skF_5'),k4_xboole_0(k4_xboole_0('#skF_3','#skF_5'),'#skF_3')) = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_5053,c_1813])).

tff(c_5260,plain,(
    k4_xboole_0('#skF_3','#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_618,c_1456,c_28,c_2,c_28,c_5158])).

tff(c_40,plain,(
    r1_tarski('#skF_3',k2_xboole_0('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_134,plain,(
    ! [A_42,B_43] :
      ( k2_xboole_0(A_42,B_43) = B_43
      | ~ r1_tarski(A_42,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_145,plain,(
    k2_xboole_0('#skF_3',k2_xboole_0('#skF_4','#skF_5')) = k2_xboole_0('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_134])).

tff(c_720,plain,(
    k4_xboole_0(k2_xboole_0('#skF_4','#skF_5'),k2_xboole_0('#skF_4','#skF_5')) = k4_xboole_0('#skF_3',k2_xboole_0('#skF_4','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_689])).

tff(c_739,plain,(
    k4_xboole_0('#skF_3',k2_xboole_0('#skF_4','#skF_5')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_276,c_720])).

tff(c_5587,plain,(
    k2_xboole_0('#skF_5',k4_xboole_0('#skF_3','#skF_4')) = k2_xboole_0('#skF_5',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_739,c_5423])).

tff(c_5658,plain,(
    k2_xboole_0('#skF_5',k4_xboole_0('#skF_3','#skF_4')) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_618,c_5587])).

tff(c_2966,plain,(
    ! [A_156,B_157] : k2_xboole_0(A_156,k2_xboole_0(B_157,A_156)) = k2_xboole_0(B_157,A_156) ),
    inference(resolution,[status(thm)],[c_67,c_134])).

tff(c_3096,plain,(
    ! [A_1,B_2] : k2_xboole_0(A_1,k2_xboole_0(A_1,B_2)) = k2_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_2966])).

tff(c_6526,plain,(
    k2_xboole_0(k4_xboole_0('#skF_3','#skF_4'),'#skF_5') = k2_xboole_0('#skF_5','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_5658,c_3096])).

tff(c_6614,plain,(
    k2_xboole_0(k4_xboole_0('#skF_3','#skF_4'),'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_409,c_6526])).

tff(c_9595,plain,(
    ! [A_236,B_237,C_238] : k4_xboole_0(A_236,k2_xboole_0(k4_xboole_0(A_236,B_237),C_238)) = k4_xboole_0(k3_xboole_0(A_236,B_237),C_238) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_1304])).

tff(c_9723,plain,(
    k4_xboole_0(k3_xboole_0('#skF_3','#skF_4'),'#skF_5') = k4_xboole_0('#skF_3','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_6614,c_9595])).

tff(c_9863,plain,(
    k4_xboole_0(k3_xboole_0('#skF_4','#skF_3'),'#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5260,c_4,c_9723])).

tff(c_1386,plain,(
    ! [A_110,B_111] : k4_xboole_0(A_110,k2_xboole_0(B_111,A_110)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_1332])).

tff(c_5757,plain,(
    ! [B_197,A_198] : k4_xboole_0(k4_xboole_0(B_197,A_198),B_197) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_5673,c_1386])).

tff(c_9918,plain,(
    k4_xboole_0('#skF_3',k3_xboole_0('#skF_4','#skF_3')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_9863,c_5757])).

tff(c_1468,plain,(
    ! [A_113,B_114] : k3_xboole_0(A_113,k2_xboole_0(B_114,A_113)) = A_113 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_1429])).

tff(c_698,plain,(
    ! [A_81,B_82] : k4_xboole_0(k2_xboole_0(A_81,B_82),k4_xboole_0(A_81,B_82)) = k3_xboole_0(k2_xboole_0(A_81,B_82),B_82) ),
    inference(superposition,[status(thm),theory(equality)],[c_689,c_30])).

tff(c_733,plain,(
    ! [A_81,B_82] : k4_xboole_0(k2_xboole_0(A_81,B_82),k4_xboole_0(A_81,B_82)) = k3_xboole_0(B_82,k2_xboole_0(A_81,B_82)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_698])).

tff(c_7216,plain,(
    ! [A_81,B_82] : k4_xboole_0(k2_xboole_0(A_81,B_82),k4_xboole_0(A_81,B_82)) = B_82 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1468,c_733])).

tff(c_11486,plain,(
    k4_xboole_0(k2_xboole_0('#skF_3',k3_xboole_0('#skF_4','#skF_3')),k1_xboole_0) = k3_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_9918,c_7216])).

tff(c_11556,plain,(
    k3_xboole_0('#skF_4','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8435,c_7178,c_11486])).

tff(c_1141,plain,(
    ! [B_102,A_103] : r1_tarski(k4_xboole_0(B_102,A_103),k2_xboole_0(A_103,B_102)) ),
    inference(superposition,[status(thm),theory(equality)],[c_410,c_67])).

tff(c_1177,plain,(
    ! [B_2,A_1] : r1_tarski(k4_xboole_0(B_2,A_1),k2_xboole_0(B_2,A_1)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1141])).

tff(c_5760,plain,(
    ! [B_197,A_198] : r1_tarski(k4_xboole_0(B_197,k4_xboole_0(B_197,A_198)),B_197) ),
    inference(superposition,[status(thm),theory(equality)],[c_5673,c_1177])).

tff(c_5879,plain,(
    ! [B_197,A_198] : r1_tarski(k3_xboole_0(B_197,A_198),B_197) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_5760])).

tff(c_11607,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_11556,c_5879])).

tff(c_11662,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_11607])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:23:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.21/2.82  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.21/2.83  
% 7.21/2.83  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.21/2.84  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 7.21/2.84  
% 7.21/2.84  %Foreground sorts:
% 7.21/2.84  
% 7.21/2.84  
% 7.21/2.84  %Background operators:
% 7.21/2.84  
% 7.21/2.84  
% 7.21/2.84  %Foreground operators:
% 7.21/2.84  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.21/2.84  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.21/2.84  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.21/2.84  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.21/2.84  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.21/2.84  tff('#skF_5', type, '#skF_5': $i).
% 7.21/2.84  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 7.21/2.84  tff('#skF_3', type, '#skF_3': $i).
% 7.21/2.84  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.21/2.84  tff('#skF_4', type, '#skF_4': $i).
% 7.21/2.84  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.21/2.84  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 7.21/2.84  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.21/2.84  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.21/2.84  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 7.21/2.84  
% 7.21/2.86  tff(f_79, negated_conjecture, ~(![A, B, C]: ((r1_tarski(A, k2_xboole_0(B, C)) & r1_xboole_0(A, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_xboole_1)).
% 7.21/2.86  tff(f_64, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 7.21/2.86  tff(f_36, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 7.21/2.86  tff(f_62, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 7.21/2.86  tff(f_70, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 7.21/2.86  tff(f_40, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 7.21/2.86  tff(f_68, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 7.21/2.86  tff(f_54, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 7.21/2.86  tff(f_58, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 7.21/2.86  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 7.21/2.86  tff(f_72, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 7.21/2.86  tff(f_66, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 7.21/2.86  tff(f_60, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 7.21/2.86  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 7.21/2.86  tff(c_36, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_79])).
% 7.21/2.86  tff(c_26, plain, (![A_22, B_23]: (k4_xboole_0(k2_xboole_0(A_22, B_23), B_23)=k4_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_64])).
% 7.21/2.86  tff(c_354, plain, (![A_62, B_63]: (r2_hidden('#skF_1'(A_62, B_63), A_62) | r1_tarski(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_36])).
% 7.21/2.86  tff(c_24, plain, (![A_21]: (k4_xboole_0(A_21, k1_xboole_0)=A_21)), inference(cnfTransformation, [status(thm)], [f_62])).
% 7.21/2.86  tff(c_32, plain, (![A_29]: (r1_xboole_0(A_29, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_70])).
% 7.21/2.86  tff(c_147, plain, (![A_44, B_45]: (k3_xboole_0(A_44, B_45)=k1_xboole_0 | ~r1_xboole_0(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_40])).
% 7.21/2.86  tff(c_154, plain, (![A_29]: (k3_xboole_0(A_29, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_32, c_147])).
% 7.21/2.86  tff(c_258, plain, (![A_54, B_55]: (k4_xboole_0(A_54, k4_xboole_0(A_54, B_55))=k3_xboole_0(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_68])).
% 7.21/2.86  tff(c_273, plain, (![A_21]: (k4_xboole_0(A_21, A_21)=k3_xboole_0(A_21, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_24, c_258])).
% 7.21/2.86  tff(c_277, plain, (![A_56]: (k4_xboole_0(A_56, A_56)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_154, c_273])).
% 7.21/2.86  tff(c_30, plain, (![A_27, B_28]: (k4_xboole_0(A_27, k4_xboole_0(A_27, B_28))=k3_xboole_0(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_68])).
% 7.21/2.86  tff(c_282, plain, (![A_56]: (k4_xboole_0(A_56, k1_xboole_0)=k3_xboole_0(A_56, A_56))), inference(superposition, [status(thm), theory('equality')], [c_277, c_30])).
% 7.21/2.86  tff(c_294, plain, (![A_56]: (k3_xboole_0(A_56, A_56)=A_56)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_282])).
% 7.21/2.86  tff(c_14, plain, (![A_10, B_11]: (r1_xboole_0(A_10, B_11) | k3_xboole_0(A_10, B_11)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 7.21/2.86  tff(c_298, plain, (![A_57]: (k3_xboole_0(A_57, A_57)=A_57)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_282])).
% 7.21/2.86  tff(c_18, plain, (![A_12, B_13, C_16]: (~r1_xboole_0(A_12, B_13) | ~r2_hidden(C_16, k3_xboole_0(A_12, B_13)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 7.21/2.86  tff(c_330, plain, (![A_58, C_59]: (~r1_xboole_0(A_58, A_58) | ~r2_hidden(C_59, A_58))), inference(superposition, [status(thm), theory('equality')], [c_298, c_18])).
% 7.21/2.86  tff(c_333, plain, (![C_59, B_11]: (~r2_hidden(C_59, B_11) | k3_xboole_0(B_11, B_11)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_330])).
% 7.21/2.86  tff(c_338, plain, (![C_59, B_11]: (~r2_hidden(C_59, B_11) | k1_xboole_0!=B_11)), inference(demodulation, [status(thm), theory('equality')], [c_294, c_333])).
% 7.21/2.86  tff(c_535, plain, (![A_71, B_72]: (k1_xboole_0!=A_71 | r1_tarski(A_71, B_72))), inference(resolution, [status(thm)], [c_354, c_338])).
% 7.21/2.86  tff(c_20, plain, (![A_17, B_18]: (k2_xboole_0(A_17, B_18)=B_18 | ~r1_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_58])).
% 7.21/2.86  tff(c_542, plain, (![A_71, B_72]: (k2_xboole_0(A_71, B_72)=B_72 | k1_xboole_0!=A_71)), inference(resolution, [status(thm)], [c_535, c_20])).
% 7.21/2.86  tff(c_547, plain, (![A_73, B_74]: (k2_xboole_0(A_73, B_74)=B_74 | k1_xboole_0!=A_73)), inference(resolution, [status(thm)], [c_535, c_20])).
% 7.21/2.86  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.21/2.86  tff(c_618, plain, (![B_74]: (k2_xboole_0(B_74, k1_xboole_0)=B_74)), inference(superposition, [status(thm), theory('equality')], [c_547, c_2])).
% 7.21/2.86  tff(c_38, plain, (r1_xboole_0('#skF_3', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_79])).
% 7.21/2.86  tff(c_155, plain, (k3_xboole_0('#skF_3', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_38, c_147])).
% 7.21/2.86  tff(c_237, plain, (![A_50, B_51, C_52]: (~r1_xboole_0(A_50, B_51) | ~r2_hidden(C_52, k3_xboole_0(A_50, B_51)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 7.21/2.86  tff(c_243, plain, (![C_52]: (~r1_xboole_0('#skF_3', '#skF_5') | ~r2_hidden(C_52, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_155, c_237])).
% 7.21/2.86  tff(c_254, plain, (![C_52]: (~r2_hidden(C_52, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_243])).
% 7.21/2.86  tff(c_369, plain, (![B_64]: (r1_tarski(k1_xboole_0, B_64))), inference(resolution, [status(thm)], [c_354, c_254])).
% 7.21/2.86  tff(c_374, plain, (![B_65]: (k2_xboole_0(k1_xboole_0, B_65)=B_65)), inference(resolution, [status(thm)], [c_369, c_20])).
% 7.21/2.86  tff(c_52, plain, (![B_36, A_37]: (k2_xboole_0(B_36, A_37)=k2_xboole_0(A_37, B_36))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.21/2.86  tff(c_34, plain, (![A_30, B_31]: (r1_tarski(A_30, k2_xboole_0(A_30, B_31)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.21/2.86  tff(c_67, plain, (![A_37, B_36]: (r1_tarski(A_37, k2_xboole_0(B_36, A_37)))), inference(superposition, [status(thm), theory('equality')], [c_52, c_34])).
% 7.21/2.86  tff(c_405, plain, (![B_66]: (r1_tarski(B_66, B_66))), inference(superposition, [status(thm), theory('equality')], [c_374, c_67])).
% 7.21/2.86  tff(c_409, plain, (![B_66]: (k2_xboole_0(B_66, B_66)=B_66)), inference(resolution, [status(thm)], [c_405, c_20])).
% 7.21/2.86  tff(c_28, plain, (![A_24, B_25, C_26]: (k4_xboole_0(k4_xboole_0(A_24, B_25), C_26)=k4_xboole_0(A_24, k2_xboole_0(B_25, C_26)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 7.21/2.86  tff(c_22, plain, (![A_19, B_20]: (k2_xboole_0(A_19, k4_xboole_0(B_20, A_19))=k2_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.21/2.86  tff(c_1304, plain, (![A_110, B_111, C_112]: (k4_xboole_0(k4_xboole_0(A_110, B_111), C_112)=k4_xboole_0(A_110, k2_xboole_0(B_111, C_112)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 7.21/2.86  tff(c_276, plain, (![A_21]: (k4_xboole_0(A_21, A_21)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_154, c_273])).
% 7.21/2.86  tff(c_1332, plain, (![A_110, B_111]: (k4_xboole_0(A_110, k2_xboole_0(B_111, k4_xboole_0(A_110, B_111)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1304, c_276])).
% 7.21/2.86  tff(c_1399, plain, (![A_113, B_114]: (k4_xboole_0(A_113, k2_xboole_0(B_114, A_113))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_1332])).
% 7.21/2.86  tff(c_1450, plain, (![B_20, A_19]: (k4_xboole_0(k4_xboole_0(B_20, A_19), k2_xboole_0(A_19, B_20))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_22, c_1399])).
% 7.21/2.86  tff(c_5423, plain, (![C_194, A_195, B_196]: (k2_xboole_0(C_194, k4_xboole_0(A_195, k2_xboole_0(B_196, C_194)))=k2_xboole_0(C_194, k4_xboole_0(A_195, B_196)))), inference(superposition, [status(thm), theory('equality')], [c_1304, c_22])).
% 7.21/2.86  tff(c_5548, plain, (![B_20, A_19]: (k2_xboole_0(B_20, k4_xboole_0(k4_xboole_0(B_20, A_19), A_19))=k2_xboole_0(B_20, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1450, c_5423])).
% 7.21/2.86  tff(c_5673, plain, (![B_197, A_198]: (k2_xboole_0(B_197, k4_xboole_0(B_197, A_198))=B_197)), inference(demodulation, [status(thm), theory('equality')], [c_618, c_409, c_28, c_5548])).
% 7.21/2.86  tff(c_7446, plain, (![A_213, A_214]: (k4_xboole_0(A_213, A_214)=A_213 | k1_xboole_0!=A_213)), inference(superposition, [status(thm), theory('equality')], [c_542, c_5673])).
% 7.21/2.86  tff(c_1429, plain, (![A_113, B_114]: (k3_xboole_0(A_113, k2_xboole_0(B_114, A_113))=k4_xboole_0(A_113, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1399, c_30])).
% 7.21/2.86  tff(c_1475, plain, (![A_115, B_116]: (k3_xboole_0(A_115, k2_xboole_0(B_116, A_115))=A_115)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_1429])).
% 7.21/2.86  tff(c_1536, plain, (![A_1, B_2]: (k3_xboole_0(A_1, k2_xboole_0(A_1, B_2))=A_1)), inference(superposition, [status(thm), theory('equality')], [c_2, c_1475])).
% 7.21/2.86  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.21/2.86  tff(c_689, plain, (![A_81, B_82]: (k4_xboole_0(k2_xboole_0(A_81, B_82), B_82)=k4_xboole_0(A_81, B_82))), inference(cnfTransformation, [status(thm)], [f_64])).
% 7.21/2.86  tff(c_1735, plain, (![A_121, B_122]: (k4_xboole_0(k2_xboole_0(A_121, B_122), A_121)=k4_xboole_0(B_122, A_121))), inference(superposition, [status(thm), theory('equality')], [c_2, c_689])).
% 7.21/2.86  tff(c_1766, plain, (![A_121, B_122]: (k4_xboole_0(k2_xboole_0(A_121, B_122), k4_xboole_0(B_122, A_121))=k3_xboole_0(k2_xboole_0(A_121, B_122), A_121))), inference(superposition, [status(thm), theory('equality')], [c_1735, c_30])).
% 7.21/2.86  tff(c_1813, plain, (![A_121, B_122]: (k4_xboole_0(k2_xboole_0(A_121, B_122), k4_xboole_0(B_122, A_121))=A_121)), inference(demodulation, [status(thm), theory('equality')], [c_1536, c_4, c_1766])).
% 7.21/2.86  tff(c_7501, plain, (![A_214, A_213]: (k4_xboole_0(k2_xboole_0(A_214, A_213), A_213)=A_214 | k1_xboole_0!=A_213)), inference(superposition, [status(thm), theory('equality')], [c_7446, c_1813])).
% 7.21/2.86  tff(c_8435, plain, (![A_214]: (k4_xboole_0(A_214, k1_xboole_0)=A_214)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_7501])).
% 7.21/2.86  tff(c_7017, plain, (![A_209, B_210]: (k2_xboole_0(A_209, k3_xboole_0(A_209, B_210))=A_209)), inference(superposition, [status(thm), theory('equality')], [c_30, c_5673])).
% 7.21/2.86  tff(c_7178, plain, (![B_4, A_3]: (k2_xboole_0(B_4, k3_xboole_0(A_3, B_4))=B_4)), inference(superposition, [status(thm), theory('equality')], [c_4, c_7017])).
% 7.21/2.86  tff(c_1456, plain, (![B_2, A_1]: (k4_xboole_0(B_2, k2_xboole_0(B_2, A_1))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_1399])).
% 7.21/2.86  tff(c_410, plain, (![A_67, B_68]: (k2_xboole_0(A_67, k4_xboole_0(B_68, A_67))=k2_xboole_0(A_67, B_68))), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.21/2.86  tff(c_436, plain, (![A_27, B_28]: (k2_xboole_0(k4_xboole_0(A_27, B_28), k3_xboole_0(A_27, B_28))=k2_xboole_0(k4_xboole_0(A_27, B_28), A_27))), inference(superposition, [status(thm), theory('equality')], [c_30, c_410])).
% 7.21/2.86  tff(c_4798, plain, (![A_187, B_188]: (k2_xboole_0(k4_xboole_0(A_187, B_188), k3_xboole_0(A_187, B_188))=k2_xboole_0(A_187, k4_xboole_0(A_187, B_188)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_436])).
% 7.21/2.86  tff(c_4996, plain, (k2_xboole_0(k4_xboole_0('#skF_3', '#skF_5'), k1_xboole_0)=k2_xboole_0('#skF_3', k4_xboole_0('#skF_3', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_155, c_4798])).
% 7.21/2.86  tff(c_5053, plain, (k2_xboole_0('#skF_3', k4_xboole_0('#skF_3', '#skF_5'))=k4_xboole_0('#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_618, c_4996])).
% 7.21/2.86  tff(c_5158, plain, (k4_xboole_0(k4_xboole_0('#skF_3', '#skF_5'), k4_xboole_0(k4_xboole_0('#skF_3', '#skF_5'), '#skF_3'))='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_5053, c_1813])).
% 7.21/2.86  tff(c_5260, plain, (k4_xboole_0('#skF_3', '#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_618, c_1456, c_28, c_2, c_28, c_5158])).
% 7.21/2.86  tff(c_40, plain, (r1_tarski('#skF_3', k2_xboole_0('#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_79])).
% 7.21/2.86  tff(c_134, plain, (![A_42, B_43]: (k2_xboole_0(A_42, B_43)=B_43 | ~r1_tarski(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_58])).
% 7.21/2.86  tff(c_145, plain, (k2_xboole_0('#skF_3', k2_xboole_0('#skF_4', '#skF_5'))=k2_xboole_0('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_40, c_134])).
% 7.21/2.86  tff(c_720, plain, (k4_xboole_0(k2_xboole_0('#skF_4', '#skF_5'), k2_xboole_0('#skF_4', '#skF_5'))=k4_xboole_0('#skF_3', k2_xboole_0('#skF_4', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_145, c_689])).
% 7.21/2.86  tff(c_739, plain, (k4_xboole_0('#skF_3', k2_xboole_0('#skF_4', '#skF_5'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_276, c_720])).
% 7.21/2.86  tff(c_5587, plain, (k2_xboole_0('#skF_5', k4_xboole_0('#skF_3', '#skF_4'))=k2_xboole_0('#skF_5', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_739, c_5423])).
% 7.21/2.86  tff(c_5658, plain, (k2_xboole_0('#skF_5', k4_xboole_0('#skF_3', '#skF_4'))='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_618, c_5587])).
% 7.21/2.86  tff(c_2966, plain, (![A_156, B_157]: (k2_xboole_0(A_156, k2_xboole_0(B_157, A_156))=k2_xboole_0(B_157, A_156))), inference(resolution, [status(thm)], [c_67, c_134])).
% 7.21/2.86  tff(c_3096, plain, (![A_1, B_2]: (k2_xboole_0(A_1, k2_xboole_0(A_1, B_2))=k2_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_2966])).
% 7.21/2.86  tff(c_6526, plain, (k2_xboole_0(k4_xboole_0('#skF_3', '#skF_4'), '#skF_5')=k2_xboole_0('#skF_5', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_5658, c_3096])).
% 7.21/2.86  tff(c_6614, plain, (k2_xboole_0(k4_xboole_0('#skF_3', '#skF_4'), '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_409, c_6526])).
% 7.21/2.86  tff(c_9595, plain, (![A_236, B_237, C_238]: (k4_xboole_0(A_236, k2_xboole_0(k4_xboole_0(A_236, B_237), C_238))=k4_xboole_0(k3_xboole_0(A_236, B_237), C_238))), inference(superposition, [status(thm), theory('equality')], [c_30, c_1304])).
% 7.21/2.86  tff(c_9723, plain, (k4_xboole_0(k3_xboole_0('#skF_3', '#skF_4'), '#skF_5')=k4_xboole_0('#skF_3', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_6614, c_9595])).
% 7.21/2.86  tff(c_9863, plain, (k4_xboole_0(k3_xboole_0('#skF_4', '#skF_3'), '#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_5260, c_4, c_9723])).
% 7.21/2.86  tff(c_1386, plain, (![A_110, B_111]: (k4_xboole_0(A_110, k2_xboole_0(B_111, A_110))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_1332])).
% 7.21/2.86  tff(c_5757, plain, (![B_197, A_198]: (k4_xboole_0(k4_xboole_0(B_197, A_198), B_197)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_5673, c_1386])).
% 7.21/2.86  tff(c_9918, plain, (k4_xboole_0('#skF_3', k3_xboole_0('#skF_4', '#skF_3'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_9863, c_5757])).
% 7.21/2.86  tff(c_1468, plain, (![A_113, B_114]: (k3_xboole_0(A_113, k2_xboole_0(B_114, A_113))=A_113)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_1429])).
% 7.21/2.86  tff(c_698, plain, (![A_81, B_82]: (k4_xboole_0(k2_xboole_0(A_81, B_82), k4_xboole_0(A_81, B_82))=k3_xboole_0(k2_xboole_0(A_81, B_82), B_82))), inference(superposition, [status(thm), theory('equality')], [c_689, c_30])).
% 7.21/2.86  tff(c_733, plain, (![A_81, B_82]: (k4_xboole_0(k2_xboole_0(A_81, B_82), k4_xboole_0(A_81, B_82))=k3_xboole_0(B_82, k2_xboole_0(A_81, B_82)))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_698])).
% 7.21/2.86  tff(c_7216, plain, (![A_81, B_82]: (k4_xboole_0(k2_xboole_0(A_81, B_82), k4_xboole_0(A_81, B_82))=B_82)), inference(demodulation, [status(thm), theory('equality')], [c_1468, c_733])).
% 7.21/2.86  tff(c_11486, plain, (k4_xboole_0(k2_xboole_0('#skF_3', k3_xboole_0('#skF_4', '#skF_3')), k1_xboole_0)=k3_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_9918, c_7216])).
% 7.21/2.86  tff(c_11556, plain, (k3_xboole_0('#skF_4', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_8435, c_7178, c_11486])).
% 7.21/2.86  tff(c_1141, plain, (![B_102, A_103]: (r1_tarski(k4_xboole_0(B_102, A_103), k2_xboole_0(A_103, B_102)))), inference(superposition, [status(thm), theory('equality')], [c_410, c_67])).
% 7.21/2.86  tff(c_1177, plain, (![B_2, A_1]: (r1_tarski(k4_xboole_0(B_2, A_1), k2_xboole_0(B_2, A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1141])).
% 7.21/2.86  tff(c_5760, plain, (![B_197, A_198]: (r1_tarski(k4_xboole_0(B_197, k4_xboole_0(B_197, A_198)), B_197))), inference(superposition, [status(thm), theory('equality')], [c_5673, c_1177])).
% 7.21/2.86  tff(c_5879, plain, (![B_197, A_198]: (r1_tarski(k3_xboole_0(B_197, A_198), B_197))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_5760])).
% 7.21/2.86  tff(c_11607, plain, (r1_tarski('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_11556, c_5879])).
% 7.21/2.86  tff(c_11662, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_11607])).
% 7.21/2.86  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.21/2.86  
% 7.21/2.86  Inference rules
% 7.21/2.86  ----------------------
% 7.21/2.86  #Ref     : 1
% 7.21/2.86  #Sup     : 3078
% 7.21/2.86  #Fact    : 0
% 7.21/2.86  #Define  : 0
% 7.21/2.86  #Split   : 5
% 7.21/2.86  #Chain   : 0
% 7.21/2.86  #Close   : 0
% 7.21/2.86  
% 7.21/2.86  Ordering : KBO
% 7.21/2.86  
% 7.21/2.86  Simplification rules
% 7.21/2.86  ----------------------
% 7.21/2.86  #Subsume      : 620
% 7.21/2.86  #Demod        : 2459
% 7.21/2.86  #Tautology    : 1623
% 7.21/2.86  #SimpNegUnit  : 92
% 7.21/2.86  #BackRed      : 13
% 7.21/2.86  
% 7.21/2.86  #Partial instantiations: 0
% 7.21/2.86  #Strategies tried      : 1
% 7.21/2.86  
% 7.21/2.86  Timing (in seconds)
% 7.21/2.86  ----------------------
% 7.52/2.86  Preprocessing        : 0.29
% 7.52/2.86  Parsing              : 0.15
% 7.52/2.86  CNF conversion       : 0.02
% 7.52/2.86  Main loop            : 1.71
% 7.52/2.86  Inferencing          : 0.43
% 7.52/2.86  Reduction            : 0.87
% 7.52/2.86  Demodulation         : 0.73
% 7.52/2.86  BG Simplification    : 0.05
% 7.52/2.86  Subsumption          : 0.28
% 7.52/2.86  Abstraction          : 0.07
% 7.52/2.86  MUC search           : 0.00
% 7.52/2.86  Cooper               : 0.00
% 7.52/2.86  Total                : 2.06
% 7.52/2.86  Index Insertion      : 0.00
% 7.52/2.86  Index Deletion       : 0.00
% 7.52/2.86  Index Matching       : 0.00
% 7.52/2.86  BG Taut test         : 0.00
%------------------------------------------------------------------------------
