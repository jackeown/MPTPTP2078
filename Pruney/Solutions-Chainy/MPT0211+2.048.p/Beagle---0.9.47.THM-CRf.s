%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:21 EST 2020

% Result     : Theorem 7.08s
% Output     : CNFRefutation 7.30s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 164 expanded)
%              Number of leaves         :   30 (  68 expanded)
%              Depth                    :   10
%              Number of atoms          :   52 ( 148 expanded)
%              Number of equality atoms :   51 ( 147 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k7_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1

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

tff(k7_enumset1,type,(
    k7_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_43,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(C,D,B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t119_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,D,C,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_enumset1)).

tff(f_57,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_59,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_55,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_enumset1(A,B,C),k2_tarski(D,E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l57_enumset1)).

tff(f_53,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_49,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_35,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_31,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_62,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(B,A),k2_tarski(C,A)) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_enumset1)).

tff(c_202,plain,(
    ! [C_80,D_81,B_82,A_83] : k2_enumset1(C_80,D_81,B_82,A_83) = k2_enumset1(A_83,B_82,C_80,D_81) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_115,plain,(
    ! [A_73,D_74,C_75,B_76] : k2_enumset1(A_73,D_74,C_75,B_76) = k2_enumset1(A_73,B_76,C_75,D_74) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_32,plain,(
    ! [A_54,B_55,C_56] : k2_enumset1(A_54,A_54,B_55,C_56) = k1_enumset1(A_54,B_55,C_56) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_131,plain,(
    ! [B_76,D_74,C_75] : k2_enumset1(B_76,D_74,C_75,B_76) = k1_enumset1(B_76,C_75,D_74) ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_32])).

tff(c_222,plain,(
    ! [A_83,B_82,D_81] : k2_enumset1(A_83,B_82,A_83,D_81) = k1_enumset1(A_83,B_82,D_81) ),
    inference(superposition,[status(thm),theory(equality)],[c_202,c_131])).

tff(c_34,plain,(
    ! [A_57,B_58,C_59,D_60] : k3_enumset1(A_57,A_57,B_58,C_59,D_60) = k2_enumset1(A_57,B_58,C_59,D_60) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_30,plain,(
    ! [A_52,B_53] : k1_enumset1(A_52,A_52,B_53) = k2_tarski(A_52,B_53) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1940,plain,(
    ! [C_143,D_142,E_141,B_139,A_140] : k2_xboole_0(k1_enumset1(A_140,B_139,C_143),k2_tarski(D_142,E_141)) = k3_enumset1(A_140,B_139,C_143,D_142,E_141) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1964,plain,(
    ! [A_52,B_53,D_142,E_141] : k3_enumset1(A_52,A_52,B_53,D_142,E_141) = k2_xboole_0(k2_tarski(A_52,B_53),k2_tarski(D_142,E_141)) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_1940])).

tff(c_1970,plain,(
    ! [A_52,B_53,D_142,E_141] : k2_xboole_0(k2_tarski(A_52,B_53),k2_tarski(D_142,E_141)) = k2_enumset1(A_52,B_53,D_142,E_141) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1964])).

tff(c_28,plain,(
    ! [A_51] : k2_tarski(A_51,A_51) = k1_tarski(A_51) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1906,plain,(
    ! [A_135,B_136,C_137,D_138] : k2_xboole_0(k1_enumset1(A_135,B_136,C_137),k1_tarski(D_138)) = k2_enumset1(A_135,B_136,C_137,D_138) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1930,plain,(
    ! [A_52,B_53,D_138] : k2_xboole_0(k2_tarski(A_52,B_53),k1_tarski(D_138)) = k2_enumset1(A_52,A_52,B_53,D_138) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_1906])).

tff(c_7174,plain,(
    ! [A_212,B_213,D_214] : k2_xboole_0(k2_tarski(A_212,B_213),k1_tarski(D_214)) = k1_enumset1(A_212,B_213,D_214) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1930])).

tff(c_7195,plain,(
    ! [A_51,D_214] : k2_xboole_0(k1_tarski(A_51),k1_tarski(D_214)) = k1_enumset1(A_51,A_51,D_214) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_7174])).

tff(c_7199,plain,(
    ! [A_215,D_216] : k2_xboole_0(k1_tarski(A_215),k1_tarski(D_216)) = k2_tarski(A_215,D_216) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_7195])).

tff(c_10,plain,(
    ! [A_10,B_11] : k5_xboole_0(A_10,k4_xboole_0(B_11,A_10)) = k2_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_4,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,A_1) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_1215,plain,(
    ! [A_117,B_118] : k5_xboole_0(k5_xboole_0(A_117,B_118),k3_xboole_0(A_117,B_118)) = k2_xboole_0(A_117,B_118) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_6,plain,(
    ! [A_5,B_6,C_7] : k5_xboole_0(k5_xboole_0(A_5,B_6),C_7) = k5_xboole_0(A_5,k5_xboole_0(B_6,C_7)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4424,plain,(
    ! [A_184,B_185] : k5_xboole_0(A_184,k5_xboole_0(B_185,k3_xboole_0(A_184,B_185))) = k2_xboole_0(A_184,B_185) ),
    inference(superposition,[status(thm),theory(equality)],[c_1215,c_6])).

tff(c_596,plain,(
    ! [A_98,B_99,C_100] : k5_xboole_0(k5_xboole_0(A_98,B_99),C_100) = k5_xboole_0(A_98,k5_xboole_0(B_99,C_100)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_650,plain,(
    ! [A_98,B_99,A_1] : k5_xboole_0(A_98,k5_xboole_0(B_99,A_1)) = k5_xboole_0(A_1,k5_xboole_0(A_98,B_99)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_596])).

tff(c_4436,plain,(
    ! [B_185,A_184] : k5_xboole_0(B_185,k5_xboole_0(k3_xboole_0(A_184,B_185),A_184)) = k2_xboole_0(A_184,B_185) ),
    inference(superposition,[status(thm),theory(equality)],[c_4424,c_650])).

tff(c_4468,plain,(
    ! [B_185,A_184] : k2_xboole_0(B_185,A_184) = k2_xboole_0(A_184,B_185) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_4,c_2,c_4436])).

tff(c_7807,plain,(
    ! [D_221,A_222] : k2_xboole_0(k1_tarski(D_221),k1_tarski(A_222)) = k2_tarski(A_222,D_221) ),
    inference(superposition,[status(thm),theory(equality)],[c_7199,c_4468])).

tff(c_7198,plain,(
    ! [A_51,D_214] : k2_xboole_0(k1_tarski(A_51),k1_tarski(D_214)) = k2_tarski(A_51,D_214) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_7195])).

tff(c_7813,plain,(
    ! [D_221,A_222] : k2_tarski(D_221,A_222) = k2_tarski(A_222,D_221) ),
    inference(superposition,[status(thm),theory(equality)],[c_7807,c_7198])).

tff(c_238,plain,(
    ! [C_80,D_81,B_82] : k2_enumset1(C_80,D_81,B_82,B_82) = k1_enumset1(B_82,C_80,D_81) ),
    inference(superposition,[status(thm),theory(equality)],[c_202,c_32])).

tff(c_496,plain,(
    ! [A_93,B_94,D_95] : k2_enumset1(A_93,B_94,D_95,D_95) = k1_enumset1(D_95,B_94,A_93) ),
    inference(superposition,[status(thm),theory(equality)],[c_202,c_32])).

tff(c_542,plain,(
    ! [B_82,D_81,C_80] : k1_enumset1(B_82,D_81,C_80) = k1_enumset1(B_82,C_80,D_81) ),
    inference(superposition,[status(thm),theory(equality)],[c_238,c_496])).

tff(c_36,plain,(
    k2_xboole_0(k2_tarski('#skF_2','#skF_1'),k2_tarski('#skF_3','#skF_1')) != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_656,plain,(
    k2_xboole_0(k2_tarski('#skF_2','#skF_1'),k2_tarski('#skF_3','#skF_1')) != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_542,c_36])).

tff(c_4547,plain,(
    k2_xboole_0(k2_tarski('#skF_3','#skF_1'),k2_tarski('#skF_2','#skF_1')) != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4468,c_656])).

tff(c_7838,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_3'),k2_tarski('#skF_1','#skF_2')) != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7813,c_7813,c_4547])).

tff(c_8344,plain,(
    k2_enumset1('#skF_1','#skF_3','#skF_1','#skF_2') != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1970,c_7838])).

tff(c_8347,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_222,c_8344])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:35:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.08/2.51  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.30/2.52  
% 7.30/2.52  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.30/2.52  %$ k7_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 7.30/2.52  
% 7.30/2.52  %Foreground sorts:
% 7.30/2.52  
% 7.30/2.52  
% 7.30/2.52  %Background operators:
% 7.30/2.52  
% 7.30/2.52  
% 7.30/2.52  %Foreground operators:
% 7.30/2.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.30/2.52  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.30/2.52  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.30/2.52  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 7.30/2.52  tff(k7_enumset1, type, k7_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 7.30/2.52  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 7.30/2.52  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 7.30/2.52  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.30/2.52  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.30/2.52  tff('#skF_2', type, '#skF_2': $i).
% 7.30/2.52  tff('#skF_3', type, '#skF_3': $i).
% 7.30/2.52  tff('#skF_1', type, '#skF_1': $i).
% 7.30/2.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.30/2.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.30/2.52  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.30/2.52  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.30/2.52  
% 7.30/2.53  tff(f_43, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(C, D, B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t119_enumset1)).
% 7.30/2.53  tff(f_39, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, D, C, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t107_enumset1)).
% 7.30/2.53  tff(f_57, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 7.30/2.53  tff(f_59, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 7.30/2.53  tff(f_55, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 7.30/2.53  tff(f_37, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_enumset1(A, B, C), k2_tarski(D, E)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l57_enumset1)).
% 7.30/2.53  tff(f_53, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 7.30/2.53  tff(f_49, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_enumset1)).
% 7.30/2.53  tff(f_35, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 7.30/2.53  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 7.30/2.53  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 7.30/2.53  tff(f_33, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_xboole_1)).
% 7.30/2.53  tff(f_31, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 7.30/2.53  tff(f_62, negated_conjecture, ~(![A, B, C]: (k2_xboole_0(k2_tarski(B, A), k2_tarski(C, A)) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t137_enumset1)).
% 7.30/2.53  tff(c_202, plain, (![C_80, D_81, B_82, A_83]: (k2_enumset1(C_80, D_81, B_82, A_83)=k2_enumset1(A_83, B_82, C_80, D_81))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.30/2.53  tff(c_115, plain, (![A_73, D_74, C_75, B_76]: (k2_enumset1(A_73, D_74, C_75, B_76)=k2_enumset1(A_73, B_76, C_75, D_74))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.30/2.53  tff(c_32, plain, (![A_54, B_55, C_56]: (k2_enumset1(A_54, A_54, B_55, C_56)=k1_enumset1(A_54, B_55, C_56))), inference(cnfTransformation, [status(thm)], [f_57])).
% 7.30/2.53  tff(c_131, plain, (![B_76, D_74, C_75]: (k2_enumset1(B_76, D_74, C_75, B_76)=k1_enumset1(B_76, C_75, D_74))), inference(superposition, [status(thm), theory('equality')], [c_115, c_32])).
% 7.30/2.53  tff(c_222, plain, (![A_83, B_82, D_81]: (k2_enumset1(A_83, B_82, A_83, D_81)=k1_enumset1(A_83, B_82, D_81))), inference(superposition, [status(thm), theory('equality')], [c_202, c_131])).
% 7.30/2.53  tff(c_34, plain, (![A_57, B_58, C_59, D_60]: (k3_enumset1(A_57, A_57, B_58, C_59, D_60)=k2_enumset1(A_57, B_58, C_59, D_60))), inference(cnfTransformation, [status(thm)], [f_59])).
% 7.30/2.53  tff(c_30, plain, (![A_52, B_53]: (k1_enumset1(A_52, A_52, B_53)=k2_tarski(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_55])).
% 7.30/2.53  tff(c_1940, plain, (![C_143, D_142, E_141, B_139, A_140]: (k2_xboole_0(k1_enumset1(A_140, B_139, C_143), k2_tarski(D_142, E_141))=k3_enumset1(A_140, B_139, C_143, D_142, E_141))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.30/2.53  tff(c_1964, plain, (![A_52, B_53, D_142, E_141]: (k3_enumset1(A_52, A_52, B_53, D_142, E_141)=k2_xboole_0(k2_tarski(A_52, B_53), k2_tarski(D_142, E_141)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_1940])).
% 7.30/2.53  tff(c_1970, plain, (![A_52, B_53, D_142, E_141]: (k2_xboole_0(k2_tarski(A_52, B_53), k2_tarski(D_142, E_141))=k2_enumset1(A_52, B_53, D_142, E_141))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_1964])).
% 7.30/2.53  tff(c_28, plain, (![A_51]: (k2_tarski(A_51, A_51)=k1_tarski(A_51))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.30/2.53  tff(c_1906, plain, (![A_135, B_136, C_137, D_138]: (k2_xboole_0(k1_enumset1(A_135, B_136, C_137), k1_tarski(D_138))=k2_enumset1(A_135, B_136, C_137, D_138))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.30/2.53  tff(c_1930, plain, (![A_52, B_53, D_138]: (k2_xboole_0(k2_tarski(A_52, B_53), k1_tarski(D_138))=k2_enumset1(A_52, A_52, B_53, D_138))), inference(superposition, [status(thm), theory('equality')], [c_30, c_1906])).
% 7.30/2.53  tff(c_7174, plain, (![A_212, B_213, D_214]: (k2_xboole_0(k2_tarski(A_212, B_213), k1_tarski(D_214))=k1_enumset1(A_212, B_213, D_214))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_1930])).
% 7.30/2.53  tff(c_7195, plain, (![A_51, D_214]: (k2_xboole_0(k1_tarski(A_51), k1_tarski(D_214))=k1_enumset1(A_51, A_51, D_214))), inference(superposition, [status(thm), theory('equality')], [c_28, c_7174])).
% 7.30/2.53  tff(c_7199, plain, (![A_215, D_216]: (k2_xboole_0(k1_tarski(A_215), k1_tarski(D_216))=k2_tarski(A_215, D_216))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_7195])).
% 7.30/2.53  tff(c_10, plain, (![A_10, B_11]: (k5_xboole_0(A_10, k4_xboole_0(B_11, A_10))=k2_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.30/2.53  tff(c_4, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.30/2.53  tff(c_2, plain, (![B_2, A_1]: (k5_xboole_0(B_2, A_1)=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.30/2.53  tff(c_1215, plain, (![A_117, B_118]: (k5_xboole_0(k5_xboole_0(A_117, B_118), k3_xboole_0(A_117, B_118))=k2_xboole_0(A_117, B_118))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.30/2.53  tff(c_6, plain, (![A_5, B_6, C_7]: (k5_xboole_0(k5_xboole_0(A_5, B_6), C_7)=k5_xboole_0(A_5, k5_xboole_0(B_6, C_7)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.30/2.53  tff(c_4424, plain, (![A_184, B_185]: (k5_xboole_0(A_184, k5_xboole_0(B_185, k3_xboole_0(A_184, B_185)))=k2_xboole_0(A_184, B_185))), inference(superposition, [status(thm), theory('equality')], [c_1215, c_6])).
% 7.30/2.53  tff(c_596, plain, (![A_98, B_99, C_100]: (k5_xboole_0(k5_xboole_0(A_98, B_99), C_100)=k5_xboole_0(A_98, k5_xboole_0(B_99, C_100)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.30/2.53  tff(c_650, plain, (![A_98, B_99, A_1]: (k5_xboole_0(A_98, k5_xboole_0(B_99, A_1))=k5_xboole_0(A_1, k5_xboole_0(A_98, B_99)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_596])).
% 7.30/2.53  tff(c_4436, plain, (![B_185, A_184]: (k5_xboole_0(B_185, k5_xboole_0(k3_xboole_0(A_184, B_185), A_184))=k2_xboole_0(A_184, B_185))), inference(superposition, [status(thm), theory('equality')], [c_4424, c_650])).
% 7.30/2.53  tff(c_4468, plain, (![B_185, A_184]: (k2_xboole_0(B_185, A_184)=k2_xboole_0(A_184, B_185))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_4, c_2, c_4436])).
% 7.30/2.53  tff(c_7807, plain, (![D_221, A_222]: (k2_xboole_0(k1_tarski(D_221), k1_tarski(A_222))=k2_tarski(A_222, D_221))), inference(superposition, [status(thm), theory('equality')], [c_7199, c_4468])).
% 7.30/2.53  tff(c_7198, plain, (![A_51, D_214]: (k2_xboole_0(k1_tarski(A_51), k1_tarski(D_214))=k2_tarski(A_51, D_214))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_7195])).
% 7.30/2.53  tff(c_7813, plain, (![D_221, A_222]: (k2_tarski(D_221, A_222)=k2_tarski(A_222, D_221))), inference(superposition, [status(thm), theory('equality')], [c_7807, c_7198])).
% 7.30/2.53  tff(c_238, plain, (![C_80, D_81, B_82]: (k2_enumset1(C_80, D_81, B_82, B_82)=k1_enumset1(B_82, C_80, D_81))), inference(superposition, [status(thm), theory('equality')], [c_202, c_32])).
% 7.30/2.53  tff(c_496, plain, (![A_93, B_94, D_95]: (k2_enumset1(A_93, B_94, D_95, D_95)=k1_enumset1(D_95, B_94, A_93))), inference(superposition, [status(thm), theory('equality')], [c_202, c_32])).
% 7.30/2.53  tff(c_542, plain, (![B_82, D_81, C_80]: (k1_enumset1(B_82, D_81, C_80)=k1_enumset1(B_82, C_80, D_81))), inference(superposition, [status(thm), theory('equality')], [c_238, c_496])).
% 7.30/2.53  tff(c_36, plain, (k2_xboole_0(k2_tarski('#skF_2', '#skF_1'), k2_tarski('#skF_3', '#skF_1'))!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_62])).
% 7.30/2.53  tff(c_656, plain, (k2_xboole_0(k2_tarski('#skF_2', '#skF_1'), k2_tarski('#skF_3', '#skF_1'))!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_542, c_36])).
% 7.30/2.53  tff(c_4547, plain, (k2_xboole_0(k2_tarski('#skF_3', '#skF_1'), k2_tarski('#skF_2', '#skF_1'))!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4468, c_656])).
% 7.30/2.53  tff(c_7838, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_3'), k2_tarski('#skF_1', '#skF_2'))!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_7813, c_7813, c_4547])).
% 7.30/2.53  tff(c_8344, plain, (k2_enumset1('#skF_1', '#skF_3', '#skF_1', '#skF_2')!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1970, c_7838])).
% 7.30/2.53  tff(c_8347, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_222, c_8344])).
% 7.30/2.53  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.30/2.53  
% 7.30/2.53  Inference rules
% 7.30/2.53  ----------------------
% 7.30/2.53  #Ref     : 0
% 7.30/2.53  #Sup     : 2213
% 7.30/2.53  #Fact    : 0
% 7.30/2.53  #Define  : 0
% 7.30/2.53  #Split   : 0
% 7.30/2.53  #Chain   : 0
% 7.30/2.53  #Close   : 0
% 7.30/2.53  
% 7.30/2.53  Ordering : KBO
% 7.30/2.53  
% 7.30/2.53  Simplification rules
% 7.30/2.53  ----------------------
% 7.30/2.53  #Subsume      : 673
% 7.30/2.53  #Demod        : 1018
% 7.30/2.53  #Tautology    : 1026
% 7.30/2.53  #SimpNegUnit  : 0
% 7.30/2.53  #BackRed      : 5
% 7.30/2.53  
% 7.30/2.53  #Partial instantiations: 0
% 7.30/2.53  #Strategies tried      : 1
% 7.30/2.53  
% 7.30/2.53  Timing (in seconds)
% 7.30/2.53  ----------------------
% 7.30/2.54  Preprocessing        : 0.30
% 7.30/2.54  Parsing              : 0.16
% 7.30/2.54  CNF conversion       : 0.02
% 7.30/2.54  Main loop            : 1.46
% 7.30/2.54  Inferencing          : 0.39
% 7.30/2.54  Reduction            : 0.81
% 7.30/2.54  Demodulation         : 0.74
% 7.30/2.54  BG Simplification    : 0.05
% 7.30/2.54  Subsumption          : 0.16
% 7.30/2.54  Abstraction          : 0.07
% 7.30/2.54  MUC search           : 0.00
% 7.30/2.54  Cooper               : 0.00
% 7.30/2.54  Total                : 1.79
% 7.30/2.54  Index Insertion      : 0.00
% 7.30/2.54  Index Deletion       : 0.00
% 7.30/2.54  Index Matching       : 0.00
% 7.30/2.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
