%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:21 EST 2020

% Result     : Theorem 13.37s
% Output     : CNFRefutation 13.47s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 179 expanded)
%              Number of leaves         :   32 (  73 expanded)
%              Depth                    :   12
%              Number of atoms          :   55 ( 162 expanded)
%              Number of equality atoms :   54 ( 161 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1

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

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_53,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,C,B,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t104_enumset1)).

tff(f_55,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_51,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_57,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_47,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k2_enumset1(A,B,C,D),k2_tarski(E,F)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_enumset1)).

tff(f_49,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k2_enumset1(A,B,C,D),k1_tarski(E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_enumset1)).

tff(f_35,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_31,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,D,C,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t107_enumset1)).

tff(f_62,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(B,A),k2_tarski(C,A)) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_enumset1)).

tff(c_28,plain,(
    ! [A_42,B_43,C_44] : k2_enumset1(A_42,A_42,B_43,C_44) = k1_enumset1(A_42,B_43,C_44) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_12,plain,(
    ! [A_12,C_14,B_13,D_15] : k2_enumset1(A_12,C_14,B_13,D_15) = k2_enumset1(A_12,B_13,C_14,D_15) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_30,plain,(
    ! [A_45,B_46,C_47,D_48] : k3_enumset1(A_45,A_45,B_46,C_47,D_48) = k2_enumset1(A_45,B_46,C_47,D_48) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_26,plain,(
    ! [A_40,B_41] : k1_enumset1(A_40,A_40,B_41) = k2_tarski(A_40,B_41) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_32,plain,(
    ! [D_52,C_51,B_50,A_49,E_53] : k4_enumset1(A_49,A_49,B_50,C_51,D_52,E_53) = k3_enumset1(A_49,B_50,C_51,D_52,E_53) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1819,plain,(
    ! [F_150,E_148,B_152,D_151,C_149,A_147] : k2_xboole_0(k2_enumset1(A_147,B_152,C_149,D_151),k2_tarski(E_148,F_150)) = k4_enumset1(A_147,B_152,C_149,D_151,E_148,F_150) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1879,plain,(
    ! [B_43,A_42,F_150,E_148,C_44] : k4_enumset1(A_42,A_42,B_43,C_44,E_148,F_150) = k2_xboole_0(k1_enumset1(A_42,B_43,C_44),k2_tarski(E_148,F_150)) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_1819])).

tff(c_9820,plain,(
    ! [F_249,B_247,A_248,E_250,C_251] : k2_xboole_0(k1_enumset1(A_248,B_247,C_251),k2_tarski(E_250,F_249)) = k3_enumset1(A_248,B_247,C_251,E_250,F_249) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1879])).

tff(c_9856,plain,(
    ! [A_40,B_41,E_250,F_249] : k3_enumset1(A_40,A_40,B_41,E_250,F_249) = k2_xboole_0(k2_tarski(A_40,B_41),k2_tarski(E_250,F_249)) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_9820])).

tff(c_9862,plain,(
    ! [A_40,B_41,E_250,F_249] : k2_xboole_0(k2_tarski(A_40,B_41),k2_tarski(E_250,F_249)) = k2_enumset1(A_40,B_41,E_250,F_249) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_9856])).

tff(c_24,plain,(
    ! [A_39] : k2_tarski(A_39,A_39) = k1_tarski(A_39) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1452,plain,(
    ! [B_133,C_132,E_130,D_134,A_131] : k2_xboole_0(k2_enumset1(A_131,B_133,C_132,D_134),k1_tarski(E_130)) = k3_enumset1(A_131,B_133,C_132,D_134,E_130) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1506,plain,(
    ! [A_42,B_43,C_44,E_130] : k3_enumset1(A_42,A_42,B_43,C_44,E_130) = k2_xboole_0(k1_enumset1(A_42,B_43,C_44),k1_tarski(E_130)) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_1452])).

tff(c_8059,plain,(
    ! [A_222,B_223,C_224,E_225] : k2_xboole_0(k1_enumset1(A_222,B_223,C_224),k1_tarski(E_225)) = k2_enumset1(A_222,B_223,C_224,E_225) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1506])).

tff(c_8095,plain,(
    ! [A_40,B_41,E_225] : k2_xboole_0(k2_tarski(A_40,B_41),k1_tarski(E_225)) = k2_enumset1(A_40,A_40,B_41,E_225) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_8059])).

tff(c_10774,plain,(
    ! [A_267,B_268,E_269] : k2_xboole_0(k2_tarski(A_267,B_268),k1_tarski(E_269)) = k1_enumset1(A_267,B_268,E_269) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_8095])).

tff(c_10798,plain,(
    ! [A_39,E_269] : k2_xboole_0(k1_tarski(A_39),k1_tarski(E_269)) = k1_enumset1(A_39,A_39,E_269) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_10774])).

tff(c_10802,plain,(
    ! [A_270,E_271] : k2_xboole_0(k1_tarski(A_270),k1_tarski(E_271)) = k2_tarski(A_270,E_271) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_10798])).

tff(c_10,plain,(
    ! [A_10,B_11] : k5_xboole_0(A_10,k4_xboole_0(B_11,A_10)) = k2_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_4,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,A_1) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_115,plain,(
    ! [A_72,B_73] : k5_xboole_0(k5_xboole_0(A_72,B_73),k3_xboole_0(A_72,B_73)) = k2_xboole_0(A_72,B_73) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2623,plain,(
    ! [B_165,A_166] : k5_xboole_0(k5_xboole_0(B_165,A_166),k3_xboole_0(A_166,B_165)) = k2_xboole_0(A_166,B_165) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_115])).

tff(c_6,plain,(
    ! [A_5,B_6,C_7] : k5_xboole_0(k5_xboole_0(A_5,B_6),C_7) = k5_xboole_0(A_5,k5_xboole_0(B_6,C_7)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2638,plain,(
    ! [B_165,A_166] : k5_xboole_0(B_165,k5_xboole_0(A_166,k3_xboole_0(A_166,B_165))) = k2_xboole_0(A_166,B_165) ),
    inference(superposition,[status(thm),theory(equality)],[c_2623,c_6])).

tff(c_2694,plain,(
    ! [B_165,A_166] : k2_xboole_0(B_165,A_166) = k2_xboole_0(A_166,B_165) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_4,c_2638])).

tff(c_11016,plain,(
    ! [E_277,A_278] : k2_xboole_0(k1_tarski(E_277),k1_tarski(A_278)) = k2_tarski(A_278,E_277) ),
    inference(superposition,[status(thm),theory(equality)],[c_10802,c_2694])).

tff(c_10801,plain,(
    ! [A_39,E_269] : k2_xboole_0(k1_tarski(A_39),k1_tarski(E_269)) = k2_tarski(A_39,E_269) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_10798])).

tff(c_11022,plain,(
    ! [E_277,A_278] : k2_tarski(E_277,A_278) = k2_tarski(A_278,E_277) ),
    inference(superposition,[status(thm),theory(equality)],[c_11016,c_10801])).

tff(c_241,plain,(
    ! [A_81,D_82,C_83,B_84] : k2_enumset1(A_81,D_82,C_83,B_84) = k2_enumset1(A_81,B_84,C_83,D_82) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_326,plain,(
    ! [B_85,D_86,C_87] : k2_enumset1(B_85,D_86,C_87,B_85) = k1_enumset1(B_85,C_87,D_86) ),
    inference(superposition,[status(thm),theory(equality)],[c_241,c_28])).

tff(c_1000,plain,(
    ! [D_113,B_114,C_115] : k2_enumset1(D_113,B_114,C_115,D_113) = k1_enumset1(D_113,B_114,C_115) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_326])).

tff(c_277,plain,(
    ! [B_84,D_82,C_83] : k2_enumset1(B_84,D_82,C_83,B_84) = k1_enumset1(B_84,C_83,D_82) ),
    inference(superposition,[status(thm),theory(equality)],[c_241,c_28])).

tff(c_1026,plain,(
    ! [D_113,C_115,B_114] : k1_enumset1(D_113,C_115,B_114) = k1_enumset1(D_113,B_114,C_115) ),
    inference(superposition,[status(thm),theory(equality)],[c_1000,c_277])).

tff(c_36,plain,(
    k2_xboole_0(k2_tarski('#skF_2','#skF_1'),k2_tarski('#skF_3','#skF_1')) != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1119,plain,(
    k2_xboole_0(k2_tarski('#skF_2','#skF_1'),k2_tarski('#skF_3','#skF_1')) != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1026,c_36])).

tff(c_2701,plain,(
    k2_xboole_0(k2_tarski('#skF_3','#skF_1'),k2_tarski('#skF_2','#skF_1')) != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2694,c_1119])).

tff(c_11050,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_3'),k2_tarski('#skF_1','#skF_2')) != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11022,c_11022,c_2701])).

tff(c_23814,plain,(
    k2_enumset1('#skF_1','#skF_3','#skF_1','#skF_2') != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9862,c_11050])).

tff(c_23817,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_12,c_23814])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:57:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.37/5.90  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.47/5.91  
% 13.47/5.91  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.47/5.91  %$ k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 13.47/5.91  
% 13.47/5.91  %Foreground sorts:
% 13.47/5.91  
% 13.47/5.91  
% 13.47/5.91  %Background operators:
% 13.47/5.91  
% 13.47/5.91  
% 13.47/5.91  %Foreground operators:
% 13.47/5.91  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.47/5.91  tff(k1_tarski, type, k1_tarski: $i > $i).
% 13.47/5.91  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 13.47/5.91  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 13.47/5.91  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 13.47/5.91  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 13.47/5.91  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 13.47/5.91  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 13.47/5.91  tff('#skF_2', type, '#skF_2': $i).
% 13.47/5.91  tff('#skF_3', type, '#skF_3': $i).
% 13.47/5.91  tff('#skF_1', type, '#skF_1': $i).
% 13.47/5.91  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 13.47/5.91  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.47/5.91  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.47/5.91  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 13.47/5.91  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 13.47/5.91  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 13.47/5.91  
% 13.47/5.93  tff(f_53, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 13.47/5.93  tff(f_37, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, C, B, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t104_enumset1)).
% 13.47/5.93  tff(f_55, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 13.47/5.93  tff(f_51, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 13.47/5.93  tff(f_57, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 13.47/5.93  tff(f_47, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k2_enumset1(A, B, C, D), k2_tarski(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t54_enumset1)).
% 13.47/5.93  tff(f_49, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 13.47/5.93  tff(f_45, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k2_enumset1(A, B, C, D), k1_tarski(E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_enumset1)).
% 13.47/5.93  tff(f_35, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 13.47/5.93  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 13.47/5.93  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 13.47/5.93  tff(f_33, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_xboole_1)).
% 13.47/5.93  tff(f_31, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 13.47/5.93  tff(f_39, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, D, C, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t107_enumset1)).
% 13.47/5.93  tff(f_62, negated_conjecture, ~(![A, B, C]: (k2_xboole_0(k2_tarski(B, A), k2_tarski(C, A)) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t137_enumset1)).
% 13.47/5.93  tff(c_28, plain, (![A_42, B_43, C_44]: (k2_enumset1(A_42, A_42, B_43, C_44)=k1_enumset1(A_42, B_43, C_44))), inference(cnfTransformation, [status(thm)], [f_53])).
% 13.47/5.93  tff(c_12, plain, (![A_12, C_14, B_13, D_15]: (k2_enumset1(A_12, C_14, B_13, D_15)=k2_enumset1(A_12, B_13, C_14, D_15))), inference(cnfTransformation, [status(thm)], [f_37])).
% 13.47/5.93  tff(c_30, plain, (![A_45, B_46, C_47, D_48]: (k3_enumset1(A_45, A_45, B_46, C_47, D_48)=k2_enumset1(A_45, B_46, C_47, D_48))), inference(cnfTransformation, [status(thm)], [f_55])).
% 13.47/5.93  tff(c_26, plain, (![A_40, B_41]: (k1_enumset1(A_40, A_40, B_41)=k2_tarski(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_51])).
% 13.47/5.93  tff(c_32, plain, (![D_52, C_51, B_50, A_49, E_53]: (k4_enumset1(A_49, A_49, B_50, C_51, D_52, E_53)=k3_enumset1(A_49, B_50, C_51, D_52, E_53))), inference(cnfTransformation, [status(thm)], [f_57])).
% 13.47/5.93  tff(c_1819, plain, (![F_150, E_148, B_152, D_151, C_149, A_147]: (k2_xboole_0(k2_enumset1(A_147, B_152, C_149, D_151), k2_tarski(E_148, F_150))=k4_enumset1(A_147, B_152, C_149, D_151, E_148, F_150))), inference(cnfTransformation, [status(thm)], [f_47])).
% 13.47/5.93  tff(c_1879, plain, (![B_43, A_42, F_150, E_148, C_44]: (k4_enumset1(A_42, A_42, B_43, C_44, E_148, F_150)=k2_xboole_0(k1_enumset1(A_42, B_43, C_44), k2_tarski(E_148, F_150)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_1819])).
% 13.47/5.93  tff(c_9820, plain, (![F_249, B_247, A_248, E_250, C_251]: (k2_xboole_0(k1_enumset1(A_248, B_247, C_251), k2_tarski(E_250, F_249))=k3_enumset1(A_248, B_247, C_251, E_250, F_249))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_1879])).
% 13.47/5.93  tff(c_9856, plain, (![A_40, B_41, E_250, F_249]: (k3_enumset1(A_40, A_40, B_41, E_250, F_249)=k2_xboole_0(k2_tarski(A_40, B_41), k2_tarski(E_250, F_249)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_9820])).
% 13.47/5.93  tff(c_9862, plain, (![A_40, B_41, E_250, F_249]: (k2_xboole_0(k2_tarski(A_40, B_41), k2_tarski(E_250, F_249))=k2_enumset1(A_40, B_41, E_250, F_249))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_9856])).
% 13.47/5.93  tff(c_24, plain, (![A_39]: (k2_tarski(A_39, A_39)=k1_tarski(A_39))), inference(cnfTransformation, [status(thm)], [f_49])).
% 13.47/5.93  tff(c_1452, plain, (![B_133, C_132, E_130, D_134, A_131]: (k2_xboole_0(k2_enumset1(A_131, B_133, C_132, D_134), k1_tarski(E_130))=k3_enumset1(A_131, B_133, C_132, D_134, E_130))), inference(cnfTransformation, [status(thm)], [f_45])).
% 13.47/5.93  tff(c_1506, plain, (![A_42, B_43, C_44, E_130]: (k3_enumset1(A_42, A_42, B_43, C_44, E_130)=k2_xboole_0(k1_enumset1(A_42, B_43, C_44), k1_tarski(E_130)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_1452])).
% 13.47/5.93  tff(c_8059, plain, (![A_222, B_223, C_224, E_225]: (k2_xboole_0(k1_enumset1(A_222, B_223, C_224), k1_tarski(E_225))=k2_enumset1(A_222, B_223, C_224, E_225))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_1506])).
% 13.47/5.93  tff(c_8095, plain, (![A_40, B_41, E_225]: (k2_xboole_0(k2_tarski(A_40, B_41), k1_tarski(E_225))=k2_enumset1(A_40, A_40, B_41, E_225))), inference(superposition, [status(thm), theory('equality')], [c_26, c_8059])).
% 13.47/5.93  tff(c_10774, plain, (![A_267, B_268, E_269]: (k2_xboole_0(k2_tarski(A_267, B_268), k1_tarski(E_269))=k1_enumset1(A_267, B_268, E_269))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_8095])).
% 13.47/5.93  tff(c_10798, plain, (![A_39, E_269]: (k2_xboole_0(k1_tarski(A_39), k1_tarski(E_269))=k1_enumset1(A_39, A_39, E_269))), inference(superposition, [status(thm), theory('equality')], [c_24, c_10774])).
% 13.47/5.93  tff(c_10802, plain, (![A_270, E_271]: (k2_xboole_0(k1_tarski(A_270), k1_tarski(E_271))=k2_tarski(A_270, E_271))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_10798])).
% 13.47/5.93  tff(c_10, plain, (![A_10, B_11]: (k5_xboole_0(A_10, k4_xboole_0(B_11, A_10))=k2_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_35])).
% 13.47/5.93  tff(c_4, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 13.47/5.93  tff(c_2, plain, (![B_2, A_1]: (k5_xboole_0(B_2, A_1)=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 13.47/5.93  tff(c_115, plain, (![A_72, B_73]: (k5_xboole_0(k5_xboole_0(A_72, B_73), k3_xboole_0(A_72, B_73))=k2_xboole_0(A_72, B_73))), inference(cnfTransformation, [status(thm)], [f_33])).
% 13.47/5.93  tff(c_2623, plain, (![B_165, A_166]: (k5_xboole_0(k5_xboole_0(B_165, A_166), k3_xboole_0(A_166, B_165))=k2_xboole_0(A_166, B_165))), inference(superposition, [status(thm), theory('equality')], [c_2, c_115])).
% 13.47/5.93  tff(c_6, plain, (![A_5, B_6, C_7]: (k5_xboole_0(k5_xboole_0(A_5, B_6), C_7)=k5_xboole_0(A_5, k5_xboole_0(B_6, C_7)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 13.47/5.93  tff(c_2638, plain, (![B_165, A_166]: (k5_xboole_0(B_165, k5_xboole_0(A_166, k3_xboole_0(A_166, B_165)))=k2_xboole_0(A_166, B_165))), inference(superposition, [status(thm), theory('equality')], [c_2623, c_6])).
% 13.47/5.93  tff(c_2694, plain, (![B_165, A_166]: (k2_xboole_0(B_165, A_166)=k2_xboole_0(A_166, B_165))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_4, c_2638])).
% 13.47/5.93  tff(c_11016, plain, (![E_277, A_278]: (k2_xboole_0(k1_tarski(E_277), k1_tarski(A_278))=k2_tarski(A_278, E_277))), inference(superposition, [status(thm), theory('equality')], [c_10802, c_2694])).
% 13.47/5.93  tff(c_10801, plain, (![A_39, E_269]: (k2_xboole_0(k1_tarski(A_39), k1_tarski(E_269))=k2_tarski(A_39, E_269))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_10798])).
% 13.47/5.93  tff(c_11022, plain, (![E_277, A_278]: (k2_tarski(E_277, A_278)=k2_tarski(A_278, E_277))), inference(superposition, [status(thm), theory('equality')], [c_11016, c_10801])).
% 13.47/5.93  tff(c_241, plain, (![A_81, D_82, C_83, B_84]: (k2_enumset1(A_81, D_82, C_83, B_84)=k2_enumset1(A_81, B_84, C_83, D_82))), inference(cnfTransformation, [status(thm)], [f_39])).
% 13.47/5.93  tff(c_326, plain, (![B_85, D_86, C_87]: (k2_enumset1(B_85, D_86, C_87, B_85)=k1_enumset1(B_85, C_87, D_86))), inference(superposition, [status(thm), theory('equality')], [c_241, c_28])).
% 13.47/5.93  tff(c_1000, plain, (![D_113, B_114, C_115]: (k2_enumset1(D_113, B_114, C_115, D_113)=k1_enumset1(D_113, B_114, C_115))), inference(superposition, [status(thm), theory('equality')], [c_12, c_326])).
% 13.47/5.93  tff(c_277, plain, (![B_84, D_82, C_83]: (k2_enumset1(B_84, D_82, C_83, B_84)=k1_enumset1(B_84, C_83, D_82))), inference(superposition, [status(thm), theory('equality')], [c_241, c_28])).
% 13.47/5.93  tff(c_1026, plain, (![D_113, C_115, B_114]: (k1_enumset1(D_113, C_115, B_114)=k1_enumset1(D_113, B_114, C_115))), inference(superposition, [status(thm), theory('equality')], [c_1000, c_277])).
% 13.47/5.93  tff(c_36, plain, (k2_xboole_0(k2_tarski('#skF_2', '#skF_1'), k2_tarski('#skF_3', '#skF_1'))!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_62])).
% 13.47/5.93  tff(c_1119, plain, (k2_xboole_0(k2_tarski('#skF_2', '#skF_1'), k2_tarski('#skF_3', '#skF_1'))!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1026, c_36])).
% 13.47/5.93  tff(c_2701, plain, (k2_xboole_0(k2_tarski('#skF_3', '#skF_1'), k2_tarski('#skF_2', '#skF_1'))!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2694, c_1119])).
% 13.47/5.93  tff(c_11050, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_3'), k2_tarski('#skF_1', '#skF_2'))!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_11022, c_11022, c_2701])).
% 13.47/5.93  tff(c_23814, plain, (k2_enumset1('#skF_1', '#skF_3', '#skF_1', '#skF_2')!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_9862, c_11050])).
% 13.47/5.93  tff(c_23817, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_12, c_23814])).
% 13.47/5.93  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.47/5.93  
% 13.47/5.93  Inference rules
% 13.47/5.93  ----------------------
% 13.47/5.93  #Ref     : 0
% 13.47/5.93  #Sup     : 6326
% 13.47/5.93  #Fact    : 0
% 13.47/5.93  #Define  : 0
% 13.47/5.93  #Split   : 0
% 13.47/5.93  #Chain   : 0
% 13.47/5.93  #Close   : 0
% 13.47/5.93  
% 13.47/5.93  Ordering : KBO
% 13.47/5.93  
% 13.47/5.93  Simplification rules
% 13.47/5.93  ----------------------
% 13.47/5.93  #Subsume      : 1550
% 13.47/5.93  #Demod        : 3773
% 13.47/5.93  #Tautology    : 1931
% 13.47/5.93  #SimpNegUnit  : 0
% 13.47/5.93  #BackRed      : 5
% 13.47/5.93  
% 13.47/5.93  #Partial instantiations: 0
% 13.47/5.93  #Strategies tried      : 1
% 13.47/5.93  
% 13.47/5.93  Timing (in seconds)
% 13.47/5.93  ----------------------
% 13.47/5.93  Preprocessing        : 0.34
% 13.47/5.93  Parsing              : 0.18
% 13.47/5.93  CNF conversion       : 0.02
% 13.47/5.93  Main loop            : 4.77
% 13.47/5.93  Inferencing          : 0.89
% 13.47/5.93  Reduction            : 3.08
% 13.47/5.93  Demodulation         : 2.91
% 13.47/5.93  BG Simplification    : 0.14
% 13.47/5.93  Subsumption          : 0.48
% 13.47/5.93  Abstraction          : 0.20
% 13.47/5.93  MUC search           : 0.00
% 13.47/5.93  Cooper               : 0.00
% 13.47/5.93  Total                : 5.14
% 13.47/5.93  Index Insertion      : 0.00
% 13.47/5.93  Index Deletion       : 0.00
% 13.47/5.93  Index Matching       : 0.00
% 13.47/5.93  BG Taut test         : 0.00
%------------------------------------------------------------------------------
