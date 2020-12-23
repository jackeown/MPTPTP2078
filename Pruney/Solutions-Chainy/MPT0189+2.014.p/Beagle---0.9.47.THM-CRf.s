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
% DateTime   : Thu Dec  3 09:46:52 EST 2020

% Result     : Theorem 10.06s
% Output     : CNFRefutation 10.06s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 197 expanded)
%              Number of leaves         :   31 (  83 expanded)
%              Depth                    :   10
%              Number of atoms          :   45 ( 178 expanded)
%              Number of equality atoms :   44 ( 177 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_35,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,C,B,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,B,D,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_enumset1)).

tff(f_59,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k2_tarski(A,B),k1_enumset1(C,D,E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_enumset1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_61,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_57,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_63,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k2_tarski(F,G)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k4_enumset1(A,B,C,D,E,F),k1_tarski(G)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_enumset1)).

tff(f_53,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_68,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,A,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_enumset1)).

tff(c_10,plain,(
    ! [A_11,C_13,B_12,D_14] : k2_enumset1(A_11,C_13,B_12,D_14) = k2_enumset1(A_11,B_12,C_13,D_14) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_8,plain,(
    ! [A_7,B_8,D_10,C_9] : k2_enumset1(A_7,B_8,D_10,C_9) = k2_enumset1(A_7,B_8,C_9,D_10) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_34,plain,(
    ! [A_80,B_81,C_82,D_83] : k3_enumset1(A_80,A_80,B_81,C_82,D_83) = k2_enumset1(A_80,B_81,C_82,D_83) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_611,plain,(
    ! [A_152,B_150,C_148,D_149,E_151] : k2_xboole_0(k2_tarski(A_152,B_150),k1_enumset1(C_148,D_149,E_151)) = k3_enumset1(A_152,B_150,C_148,D_149,E_151) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_620,plain,(
    ! [A_152,B_150,C_148,D_149,E_151] : k2_xboole_0(k1_enumset1(C_148,D_149,E_151),k2_tarski(A_152,B_150)) = k3_enumset1(A_152,B_150,C_148,D_149,E_151) ),
    inference(superposition,[status(thm),theory(equality)],[c_611,c_2])).

tff(c_36,plain,(
    ! [E_88,C_86,B_85,D_87,A_84] : k4_enumset1(A_84,A_84,B_85,C_86,D_87,E_88) = k3_enumset1(A_84,B_85,C_86,D_87,E_88) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_32,plain,(
    ! [A_77,B_78,C_79] : k2_enumset1(A_77,A_77,B_78,C_79) = k1_enumset1(A_77,B_78,C_79) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_208,plain,(
    ! [A_121,B_122,D_123,C_124] : k2_enumset1(A_121,B_122,D_123,C_124) = k2_enumset1(A_121,B_122,C_124,D_123) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_284,plain,(
    ! [A_77,C_79,B_78] : k2_enumset1(A_77,A_77,C_79,B_78) = k1_enumset1(A_77,B_78,C_79) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_208])).

tff(c_38,plain,(
    ! [D_92,C_91,F_94,A_89,B_90,E_93] : k5_enumset1(A_89,A_89,B_90,C_91,D_92,E_93,F_94) = k4_enumset1(A_89,B_90,C_91,D_92,E_93,F_94) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_980,plain,(
    ! [A_185,E_184,D_183,C_180,B_182,G_181,F_186] : k2_xboole_0(k3_enumset1(A_185,B_182,C_180,D_183,E_184),k2_tarski(F_186,G_181)) = k5_enumset1(A_185,B_182,C_180,D_183,E_184,F_186,G_181) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_995,plain,(
    ! [B_81,D_83,A_80,G_181,F_186,C_82] : k5_enumset1(A_80,A_80,B_81,C_82,D_83,F_186,G_181) = k2_xboole_0(k2_enumset1(A_80,B_81,C_82,D_83),k2_tarski(F_186,G_181)) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_980])).

tff(c_2878,plain,(
    ! [G_274,C_275,A_272,D_276,F_271,B_273] : k2_xboole_0(k2_enumset1(A_272,B_273,C_275,D_276),k2_tarski(F_271,G_274)) = k4_enumset1(A_272,B_273,C_275,D_276,F_271,G_274) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_995])).

tff(c_2944,plain,(
    ! [G_274,B_78,A_77,C_79,F_271] : k4_enumset1(A_77,A_77,C_79,B_78,F_271,G_274) = k2_xboole_0(k1_enumset1(A_77,B_78,C_79),k2_tarski(F_271,G_274)) ),
    inference(superposition,[status(thm),theory(equality)],[c_284,c_2878])).

tff(c_5824,plain,(
    ! [B_372,G_374,F_370,C_373,A_371] : k3_enumset1(F_370,G_374,A_371,B_372,C_373) = k3_enumset1(A_371,C_373,B_372,F_370,G_374) ),
    inference(demodulation,[status(thm),theory(equality)],[c_620,c_36,c_2944])).

tff(c_6009,plain,(
    ! [B_81,D_83,C_82,A_80] : k3_enumset1(B_81,D_83,C_82,A_80,A_80) = k2_enumset1(A_80,B_81,C_82,D_83) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_5824])).

tff(c_767,plain,(
    ! [C_170,D_171,A_175,B_173,G_174,F_169,E_172] : k2_xboole_0(k4_enumset1(A_175,B_173,C_170,D_171,E_172,F_169),k1_tarski(G_174)) = k5_enumset1(A_175,B_173,C_170,D_171,E_172,F_169,G_174) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_782,plain,(
    ! [E_88,C_86,B_85,D_87,A_84,G_174] : k5_enumset1(A_84,A_84,B_85,C_86,D_87,E_88,G_174) = k2_xboole_0(k3_enumset1(A_84,B_85,C_86,D_87,E_88),k1_tarski(G_174)) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_767])).

tff(c_791,plain,(
    ! [E_88,C_86,B_85,D_87,A_84,G_174] : k2_xboole_0(k3_enumset1(A_84,B_85,C_86,D_87,E_88),k1_tarski(G_174)) = k4_enumset1(A_84,B_85,C_86,D_87,E_88,G_174) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_782])).

tff(c_28,plain,(
    ! [A_74] : k2_tarski(A_74,A_74) = k1_tarski(A_74) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1004,plain,(
    ! [A_74,A_185,E_184,D_183,C_180,B_182] : k5_enumset1(A_185,B_182,C_180,D_183,E_184,A_74,A_74) = k2_xboole_0(k3_enumset1(A_185,B_182,C_180,D_183,E_184),k1_tarski(A_74)) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_980])).

tff(c_3602,plain,(
    ! [C_296,B_293,A_291,A_294,D_292,E_295] : k5_enumset1(A_291,B_293,C_296,D_292,E_295,A_294,A_294) = k4_enumset1(A_291,B_293,C_296,D_292,E_295,A_294) ),
    inference(demodulation,[status(thm),theory(equality)],[c_791,c_1004])).

tff(c_3615,plain,(
    ! [C_296,B_293,A_294,D_292,E_295] : k4_enumset1(B_293,C_296,D_292,E_295,A_294,A_294) = k4_enumset1(B_293,B_293,C_296,D_292,E_295,A_294) ),
    inference(superposition,[status(thm),theory(equality)],[c_3602,c_38])).

tff(c_21287,plain,(
    ! [D_601,A_599,C_598,B_600,E_602] : k4_enumset1(B_600,C_598,D_601,E_602,A_599,A_599) = k3_enumset1(B_600,C_598,D_601,E_602,A_599) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_3615])).

tff(c_21319,plain,(
    ! [C_598,D_601,E_602,A_599] : k3_enumset1(C_598,D_601,E_602,A_599,A_599) = k3_enumset1(C_598,C_598,D_601,E_602,A_599) ),
    inference(superposition,[status(thm),theory(equality)],[c_21287,c_36])).

tff(c_21339,plain,(
    ! [C_598,D_601,E_602,A_599] : k2_enumset1(C_598,D_601,E_602,A_599) = k2_enumset1(A_599,C_598,E_602,D_601) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6009,c_34,c_21319])).

tff(c_42,plain,(
    k2_enumset1('#skF_2','#skF_1','#skF_3','#skF_4') != k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_43,plain,(
    k2_enumset1('#skF_2','#skF_1','#skF_3','#skF_4') != k2_enumset1('#skF_1','#skF_3','#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_42])).

tff(c_44,plain,(
    k2_enumset1('#skF_2','#skF_1','#skF_4','#skF_3') != k2_enumset1('#skF_1','#skF_3','#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_8,c_43])).

tff(c_45,plain,(
    k2_enumset1('#skF_2','#skF_4','#skF_1','#skF_3') != k2_enumset1('#skF_1','#skF_4','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_10,c_44])).

tff(c_21345,plain,(
    k2_enumset1('#skF_4','#skF_2','#skF_3','#skF_1') != k2_enumset1('#skF_4','#skF_3','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_21339,c_21339,c_21339,c_45])).

tff(c_21348,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_8,c_10,c_10,c_21345])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n023.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 18:54:36 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.06/3.77  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.06/3.77  
% 10.06/3.77  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.06/3.77  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 10.06/3.77  
% 10.06/3.77  %Foreground sorts:
% 10.06/3.77  
% 10.06/3.77  
% 10.06/3.77  %Background operators:
% 10.06/3.77  
% 10.06/3.77  
% 10.06/3.77  %Foreground operators:
% 10.06/3.77  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.06/3.77  tff(k1_tarski, type, k1_tarski: $i > $i).
% 10.06/3.77  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 10.06/3.77  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 10.06/3.77  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 10.06/3.77  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 10.06/3.77  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 10.06/3.77  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 10.06/3.77  tff('#skF_2', type, '#skF_2': $i).
% 10.06/3.77  tff('#skF_3', type, '#skF_3': $i).
% 10.06/3.77  tff('#skF_1', type, '#skF_1': $i).
% 10.06/3.77  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 10.06/3.77  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 10.06/3.77  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.06/3.77  tff('#skF_4', type, '#skF_4': $i).
% 10.06/3.77  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.06/3.77  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 10.06/3.77  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 10.06/3.77  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 10.06/3.77  
% 10.06/3.79  tff(f_35, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, C, B, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t104_enumset1)).
% 10.06/3.79  tff(f_33, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, B, D, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t103_enumset1)).
% 10.06/3.79  tff(f_59, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 10.06/3.79  tff(f_37, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k2_tarski(A, B), k1_enumset1(C, D, E)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_enumset1)).
% 10.06/3.79  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 10.06/3.79  tff(f_61, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 10.06/3.79  tff(f_57, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 10.06/3.79  tff(f_63, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 10.06/3.79  tff(f_39, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k2_tarski(F, G)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_enumset1)).
% 10.06/3.79  tff(f_41, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k4_enumset1(A, B, C, D, E, F), k1_tarski(G)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_enumset1)).
% 10.06/3.79  tff(f_53, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 10.06/3.79  tff(f_68, negated_conjecture, ~(![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, A, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t108_enumset1)).
% 10.06/3.79  tff(c_10, plain, (![A_11, C_13, B_12, D_14]: (k2_enumset1(A_11, C_13, B_12, D_14)=k2_enumset1(A_11, B_12, C_13, D_14))), inference(cnfTransformation, [status(thm)], [f_35])).
% 10.06/3.79  tff(c_8, plain, (![A_7, B_8, D_10, C_9]: (k2_enumset1(A_7, B_8, D_10, C_9)=k2_enumset1(A_7, B_8, C_9, D_10))), inference(cnfTransformation, [status(thm)], [f_33])).
% 10.06/3.79  tff(c_34, plain, (![A_80, B_81, C_82, D_83]: (k3_enumset1(A_80, A_80, B_81, C_82, D_83)=k2_enumset1(A_80, B_81, C_82, D_83))), inference(cnfTransformation, [status(thm)], [f_59])).
% 10.06/3.79  tff(c_611, plain, (![A_152, B_150, C_148, D_149, E_151]: (k2_xboole_0(k2_tarski(A_152, B_150), k1_enumset1(C_148, D_149, E_151))=k3_enumset1(A_152, B_150, C_148, D_149, E_151))), inference(cnfTransformation, [status(thm)], [f_37])).
% 10.06/3.79  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 10.06/3.79  tff(c_620, plain, (![A_152, B_150, C_148, D_149, E_151]: (k2_xboole_0(k1_enumset1(C_148, D_149, E_151), k2_tarski(A_152, B_150))=k3_enumset1(A_152, B_150, C_148, D_149, E_151))), inference(superposition, [status(thm), theory('equality')], [c_611, c_2])).
% 10.06/3.79  tff(c_36, plain, (![E_88, C_86, B_85, D_87, A_84]: (k4_enumset1(A_84, A_84, B_85, C_86, D_87, E_88)=k3_enumset1(A_84, B_85, C_86, D_87, E_88))), inference(cnfTransformation, [status(thm)], [f_61])).
% 10.06/3.79  tff(c_32, plain, (![A_77, B_78, C_79]: (k2_enumset1(A_77, A_77, B_78, C_79)=k1_enumset1(A_77, B_78, C_79))), inference(cnfTransformation, [status(thm)], [f_57])).
% 10.06/3.79  tff(c_208, plain, (![A_121, B_122, D_123, C_124]: (k2_enumset1(A_121, B_122, D_123, C_124)=k2_enumset1(A_121, B_122, C_124, D_123))), inference(cnfTransformation, [status(thm)], [f_33])).
% 10.06/3.79  tff(c_284, plain, (![A_77, C_79, B_78]: (k2_enumset1(A_77, A_77, C_79, B_78)=k1_enumset1(A_77, B_78, C_79))), inference(superposition, [status(thm), theory('equality')], [c_32, c_208])).
% 10.06/3.79  tff(c_38, plain, (![D_92, C_91, F_94, A_89, B_90, E_93]: (k5_enumset1(A_89, A_89, B_90, C_91, D_92, E_93, F_94)=k4_enumset1(A_89, B_90, C_91, D_92, E_93, F_94))), inference(cnfTransformation, [status(thm)], [f_63])).
% 10.06/3.79  tff(c_980, plain, (![A_185, E_184, D_183, C_180, B_182, G_181, F_186]: (k2_xboole_0(k3_enumset1(A_185, B_182, C_180, D_183, E_184), k2_tarski(F_186, G_181))=k5_enumset1(A_185, B_182, C_180, D_183, E_184, F_186, G_181))), inference(cnfTransformation, [status(thm)], [f_39])).
% 10.06/3.79  tff(c_995, plain, (![B_81, D_83, A_80, G_181, F_186, C_82]: (k5_enumset1(A_80, A_80, B_81, C_82, D_83, F_186, G_181)=k2_xboole_0(k2_enumset1(A_80, B_81, C_82, D_83), k2_tarski(F_186, G_181)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_980])).
% 10.06/3.79  tff(c_2878, plain, (![G_274, C_275, A_272, D_276, F_271, B_273]: (k2_xboole_0(k2_enumset1(A_272, B_273, C_275, D_276), k2_tarski(F_271, G_274))=k4_enumset1(A_272, B_273, C_275, D_276, F_271, G_274))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_995])).
% 10.06/3.79  tff(c_2944, plain, (![G_274, B_78, A_77, C_79, F_271]: (k4_enumset1(A_77, A_77, C_79, B_78, F_271, G_274)=k2_xboole_0(k1_enumset1(A_77, B_78, C_79), k2_tarski(F_271, G_274)))), inference(superposition, [status(thm), theory('equality')], [c_284, c_2878])).
% 10.06/3.79  tff(c_5824, plain, (![B_372, G_374, F_370, C_373, A_371]: (k3_enumset1(F_370, G_374, A_371, B_372, C_373)=k3_enumset1(A_371, C_373, B_372, F_370, G_374))), inference(demodulation, [status(thm), theory('equality')], [c_620, c_36, c_2944])).
% 10.06/3.79  tff(c_6009, plain, (![B_81, D_83, C_82, A_80]: (k3_enumset1(B_81, D_83, C_82, A_80, A_80)=k2_enumset1(A_80, B_81, C_82, D_83))), inference(superposition, [status(thm), theory('equality')], [c_34, c_5824])).
% 10.06/3.79  tff(c_767, plain, (![C_170, D_171, A_175, B_173, G_174, F_169, E_172]: (k2_xboole_0(k4_enumset1(A_175, B_173, C_170, D_171, E_172, F_169), k1_tarski(G_174))=k5_enumset1(A_175, B_173, C_170, D_171, E_172, F_169, G_174))), inference(cnfTransformation, [status(thm)], [f_41])).
% 10.06/3.79  tff(c_782, plain, (![E_88, C_86, B_85, D_87, A_84, G_174]: (k5_enumset1(A_84, A_84, B_85, C_86, D_87, E_88, G_174)=k2_xboole_0(k3_enumset1(A_84, B_85, C_86, D_87, E_88), k1_tarski(G_174)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_767])).
% 10.06/3.79  tff(c_791, plain, (![E_88, C_86, B_85, D_87, A_84, G_174]: (k2_xboole_0(k3_enumset1(A_84, B_85, C_86, D_87, E_88), k1_tarski(G_174))=k4_enumset1(A_84, B_85, C_86, D_87, E_88, G_174))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_782])).
% 10.06/3.79  tff(c_28, plain, (![A_74]: (k2_tarski(A_74, A_74)=k1_tarski(A_74))), inference(cnfTransformation, [status(thm)], [f_53])).
% 10.06/3.79  tff(c_1004, plain, (![A_74, A_185, E_184, D_183, C_180, B_182]: (k5_enumset1(A_185, B_182, C_180, D_183, E_184, A_74, A_74)=k2_xboole_0(k3_enumset1(A_185, B_182, C_180, D_183, E_184), k1_tarski(A_74)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_980])).
% 10.06/3.79  tff(c_3602, plain, (![C_296, B_293, A_291, A_294, D_292, E_295]: (k5_enumset1(A_291, B_293, C_296, D_292, E_295, A_294, A_294)=k4_enumset1(A_291, B_293, C_296, D_292, E_295, A_294))), inference(demodulation, [status(thm), theory('equality')], [c_791, c_1004])).
% 10.06/3.79  tff(c_3615, plain, (![C_296, B_293, A_294, D_292, E_295]: (k4_enumset1(B_293, C_296, D_292, E_295, A_294, A_294)=k4_enumset1(B_293, B_293, C_296, D_292, E_295, A_294))), inference(superposition, [status(thm), theory('equality')], [c_3602, c_38])).
% 10.06/3.79  tff(c_21287, plain, (![D_601, A_599, C_598, B_600, E_602]: (k4_enumset1(B_600, C_598, D_601, E_602, A_599, A_599)=k3_enumset1(B_600, C_598, D_601, E_602, A_599))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_3615])).
% 10.06/3.79  tff(c_21319, plain, (![C_598, D_601, E_602, A_599]: (k3_enumset1(C_598, D_601, E_602, A_599, A_599)=k3_enumset1(C_598, C_598, D_601, E_602, A_599))), inference(superposition, [status(thm), theory('equality')], [c_21287, c_36])).
% 10.06/3.79  tff(c_21339, plain, (![C_598, D_601, E_602, A_599]: (k2_enumset1(C_598, D_601, E_602, A_599)=k2_enumset1(A_599, C_598, E_602, D_601))), inference(demodulation, [status(thm), theory('equality')], [c_6009, c_34, c_21319])).
% 10.06/3.79  tff(c_42, plain, (k2_enumset1('#skF_2', '#skF_1', '#skF_3', '#skF_4')!=k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_68])).
% 10.06/3.79  tff(c_43, plain, (k2_enumset1('#skF_2', '#skF_1', '#skF_3', '#skF_4')!=k2_enumset1('#skF_1', '#skF_3', '#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_42])).
% 10.06/3.79  tff(c_44, plain, (k2_enumset1('#skF_2', '#skF_1', '#skF_4', '#skF_3')!=k2_enumset1('#skF_1', '#skF_3', '#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_8, c_43])).
% 10.06/3.79  tff(c_45, plain, (k2_enumset1('#skF_2', '#skF_4', '#skF_1', '#skF_3')!=k2_enumset1('#skF_1', '#skF_4', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_10, c_44])).
% 10.06/3.79  tff(c_21345, plain, (k2_enumset1('#skF_4', '#skF_2', '#skF_3', '#skF_1')!=k2_enumset1('#skF_4', '#skF_3', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_21339, c_21339, c_21339, c_45])).
% 10.06/3.79  tff(c_21348, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_8, c_10, c_10, c_21345])).
% 10.06/3.79  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.06/3.79  
% 10.06/3.79  Inference rules
% 10.06/3.79  ----------------------
% 10.06/3.79  #Ref     : 0
% 10.06/3.79  #Sup     : 4855
% 10.06/3.79  #Fact    : 0
% 10.06/3.79  #Define  : 0
% 10.06/3.79  #Split   : 0
% 10.06/3.79  #Chain   : 0
% 10.06/3.79  #Close   : 0
% 10.06/3.79  
% 10.06/3.79  Ordering : KBO
% 10.06/3.79  
% 10.06/3.79  Simplification rules
% 10.06/3.79  ----------------------
% 10.06/3.79  #Subsume      : 626
% 10.06/3.79  #Demod        : 5672
% 10.06/3.79  #Tautology    : 3437
% 10.06/3.79  #SimpNegUnit  : 0
% 10.06/3.79  #BackRed      : 20
% 10.06/3.79  
% 10.06/3.79  #Partial instantiations: 0
% 10.06/3.79  #Strategies tried      : 1
% 10.06/3.79  
% 10.06/3.79  Timing (in seconds)
% 10.06/3.79  ----------------------
% 10.06/3.79  Preprocessing        : 0.34
% 10.06/3.79  Parsing              : 0.18
% 10.06/3.79  CNF conversion       : 0.02
% 10.06/3.79  Main loop            : 2.67
% 10.06/3.79  Inferencing          : 0.77
% 10.06/3.79  Reduction            : 1.41
% 10.06/3.79  Demodulation         : 1.25
% 10.06/3.79  BG Simplification    : 0.08
% 10.06/3.79  Subsumption          : 0.30
% 10.06/3.79  Abstraction          : 0.14
% 10.06/3.79  MUC search           : 0.00
% 10.06/3.79  Cooper               : 0.00
% 10.06/3.79  Total                : 3.05
% 10.06/3.79  Index Insertion      : 0.00
% 10.06/3.79  Index Deletion       : 0.00
% 10.06/3.79  Index Matching       : 0.00
% 10.06/3.79  BG Taut test         : 0.00
%------------------------------------------------------------------------------
