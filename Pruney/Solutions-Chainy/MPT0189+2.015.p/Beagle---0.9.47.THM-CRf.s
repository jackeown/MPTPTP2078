%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:52 EST 2020

% Result     : Theorem 11.06s
% Output     : CNFRefutation 11.06s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 137 expanded)
%              Number of leaves         :   31 (  61 expanded)
%              Depth                    :   10
%              Number of atoms          :   44 ( 118 expanded)
%              Number of equality atoms :   43 ( 117 expanded)
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
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,C,D,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_enumset1)).

tff(f_59,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_37,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k2_tarski(A,B),k1_enumset1(C,D,E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_enumset1)).

tff(f_61,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_57,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,B,D,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_enumset1)).

tff(f_63,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k2_tarski(F,G)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k4_enumset1(A,B,C,D,E,F),k1_tarski(G)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_enumset1)).

tff(f_53,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_68,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,A,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_enumset1)).

tff(c_10,plain,(
    ! [A_11,C_13,D_14,B_12] : k2_enumset1(A_11,C_13,D_14,B_12) = k2_enumset1(A_11,B_12,C_13,D_14) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_34,plain,(
    ! [A_80,B_81,C_82,D_83] : k3_enumset1(A_80,A_80,B_81,C_82,D_83) = k2_enumset1(A_80,B_81,C_82,D_83) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_696,plain,(
    ! [C_151,A_155,B_153,D_152,E_154] : k2_xboole_0(k2_tarski(A_155,B_153),k1_enumset1(C_151,D_152,E_154)) = k3_enumset1(A_155,B_153,C_151,D_152,E_154) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_726,plain,(
    ! [C_151,A_155,B_153,D_152,E_154] : k2_xboole_0(k1_enumset1(C_151,D_152,E_154),k2_tarski(A_155,B_153)) = k3_enumset1(A_155,B_153,C_151,D_152,E_154) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_696])).

tff(c_36,plain,(
    ! [E_88,C_86,B_85,D_87,A_84] : k4_enumset1(A_84,A_84,B_85,C_86,D_87,E_88) = k3_enumset1(A_84,B_85,C_86,D_87,E_88) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_32,plain,(
    ! [A_77,B_78,C_79] : k2_enumset1(A_77,A_77,B_78,C_79) = k1_enumset1(A_77,B_78,C_79) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_201,plain,(
    ! [A_121,B_122,D_123,C_124] : k2_enumset1(A_121,B_122,D_123,C_124) = k2_enumset1(A_121,B_122,C_124,D_123) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_274,plain,(
    ! [A_77,C_79,B_78] : k2_enumset1(A_77,A_77,C_79,B_78) = k1_enumset1(A_77,B_78,C_79) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_201])).

tff(c_38,plain,(
    ! [D_92,C_91,F_94,A_89,B_90,E_93] : k5_enumset1(A_89,A_89,B_90,C_91,D_92,E_93,F_94) = k4_enumset1(A_89,B_90,C_91,D_92,E_93,F_94) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1192,plain,(
    ! [E_188,F_190,D_187,C_184,B_186,A_189,G_185] : k2_xboole_0(k3_enumset1(A_189,B_186,C_184,D_187,E_188),k2_tarski(F_190,G_185)) = k5_enumset1(A_189,B_186,C_184,D_187,E_188,F_190,G_185) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1207,plain,(
    ! [F_190,B_81,D_83,A_80,G_185,C_82] : k5_enumset1(A_80,A_80,B_81,C_82,D_83,F_190,G_185) = k2_xboole_0(k2_enumset1(A_80,B_81,C_82,D_83),k2_tarski(F_190,G_185)) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_1192])).

tff(c_3230,plain,(
    ! [F_282,A_283,C_285,D_286,G_287,B_284] : k2_xboole_0(k2_enumset1(A_283,B_284,C_285,D_286),k2_tarski(F_282,G_287)) = k4_enumset1(A_283,B_284,C_285,D_286,F_282,G_287) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_1207])).

tff(c_3299,plain,(
    ! [F_282,B_78,A_77,C_79,G_287] : k4_enumset1(A_77,A_77,C_79,B_78,F_282,G_287) = k2_xboole_0(k1_enumset1(A_77,B_78,C_79),k2_tarski(F_282,G_287)) ),
    inference(superposition,[status(thm),theory(equality)],[c_274,c_3230])).

tff(c_4257,plain,(
    ! [G_328,F_326,C_327,B_325,A_324] : k3_enumset1(F_326,G_328,A_324,B_325,C_327) = k3_enumset1(A_324,C_327,B_325,F_326,G_328) ),
    inference(demodulation,[status(thm),theory(equality)],[c_726,c_36,c_3299])).

tff(c_4330,plain,(
    ! [B_81,D_83,C_82,A_80] : k3_enumset1(B_81,D_83,C_82,A_80,A_80) = k2_enumset1(A_80,B_81,C_82,D_83) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_4257])).

tff(c_762,plain,(
    ! [C_170,D_171,A_175,B_173,G_174,F_169,E_172] : k2_xboole_0(k4_enumset1(A_175,B_173,C_170,D_171,E_172,F_169),k1_tarski(G_174)) = k5_enumset1(A_175,B_173,C_170,D_171,E_172,F_169,G_174) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_777,plain,(
    ! [E_88,C_86,B_85,D_87,A_84,G_174] : k5_enumset1(A_84,A_84,B_85,C_86,D_87,E_88,G_174) = k2_xboole_0(k3_enumset1(A_84,B_85,C_86,D_87,E_88),k1_tarski(G_174)) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_762])).

tff(c_786,plain,(
    ! [E_88,C_86,B_85,D_87,A_84,G_174] : k2_xboole_0(k3_enumset1(A_84,B_85,C_86,D_87,E_88),k1_tarski(G_174)) = k4_enumset1(A_84,B_85,C_86,D_87,E_88,G_174) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_777])).

tff(c_28,plain,(
    ! [A_74] : k2_tarski(A_74,A_74) = k1_tarski(A_74) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1216,plain,(
    ! [E_188,A_74,D_187,C_184,B_186,A_189] : k5_enumset1(A_189,B_186,C_184,D_187,E_188,A_74,A_74) = k2_xboole_0(k3_enumset1(A_189,B_186,C_184,D_187,E_188),k1_tarski(A_74)) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_1192])).

tff(c_3601,plain,(
    ! [C_296,B_292,A_294,D_291,A_295,E_293] : k5_enumset1(A_295,B_292,C_296,D_291,E_293,A_294,A_294) = k4_enumset1(A_295,B_292,C_296,D_291,E_293,A_294) ),
    inference(demodulation,[status(thm),theory(equality)],[c_786,c_1216])).

tff(c_3621,plain,(
    ! [D_92,C_91,F_94,A_89,B_90] : k4_enumset1(A_89,B_90,C_91,D_92,F_94,F_94) = k4_enumset1(A_89,A_89,B_90,C_91,D_92,F_94) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_3601])).

tff(c_31937,plain,(
    ! [C_706,B_707,F_709,A_708,D_710] : k4_enumset1(A_708,B_707,C_706,D_710,F_709,F_709) = k3_enumset1(A_708,B_707,C_706,D_710,F_709) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_3621])).

tff(c_31988,plain,(
    ! [A_84,B_85,C_86,E_88] : k3_enumset1(A_84,B_85,C_86,E_88,E_88) = k3_enumset1(A_84,A_84,B_85,C_86,E_88) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_31937])).

tff(c_32002,plain,(
    ! [E_88,A_84,C_86,B_85] : k2_enumset1(E_88,A_84,C_86,B_85) = k2_enumset1(A_84,B_85,C_86,E_88) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4330,c_34,c_31988])).

tff(c_8,plain,(
    ! [A_7,B_8,D_10,C_9] : k2_enumset1(A_7,B_8,D_10,C_9) = k2_enumset1(A_7,B_8,C_9,D_10) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_42,plain,(
    k2_enumset1('#skF_2','#skF_1','#skF_3','#skF_4') != k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_43,plain,(
    k2_enumset1('#skF_2','#skF_4','#skF_1','#skF_3') != k2_enumset1('#skF_1','#skF_4','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_10,c_42])).

tff(c_44,plain,(
    k2_enumset1('#skF_2','#skF_4','#skF_1','#skF_3') != k2_enumset1('#skF_1','#skF_4','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_43])).

tff(c_34544,plain,(
    k2_enumset1('#skF_4','#skF_2','#skF_3','#skF_1') != k2_enumset1('#skF_4','#skF_3','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32002,c_32002,c_44])).

tff(c_34547,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_10,c_34544])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:20:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.06/4.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.06/4.30  
% 11.06/4.30  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.06/4.30  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 11.06/4.30  
% 11.06/4.30  %Foreground sorts:
% 11.06/4.30  
% 11.06/4.30  
% 11.06/4.30  %Background operators:
% 11.06/4.30  
% 11.06/4.30  
% 11.06/4.30  %Foreground operators:
% 11.06/4.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.06/4.30  tff(k1_tarski, type, k1_tarski: $i > $i).
% 11.06/4.30  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 11.06/4.30  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 11.06/4.30  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 11.06/4.30  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 11.06/4.30  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 11.06/4.30  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 11.06/4.30  tff('#skF_2', type, '#skF_2': $i).
% 11.06/4.30  tff('#skF_3', type, '#skF_3': $i).
% 11.06/4.30  tff('#skF_1', type, '#skF_1': $i).
% 11.06/4.30  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 11.06/4.30  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 11.06/4.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.06/4.30  tff('#skF_4', type, '#skF_4': $i).
% 11.06/4.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.06/4.30  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 11.06/4.30  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 11.06/4.30  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 11.06/4.30  
% 11.06/4.32  tff(f_35, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, C, D, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t105_enumset1)).
% 11.06/4.32  tff(f_59, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 11.06/4.32  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 11.06/4.32  tff(f_37, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k2_tarski(A, B), k1_enumset1(C, D, E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_enumset1)).
% 11.06/4.32  tff(f_61, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 11.06/4.32  tff(f_57, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 11.06/4.32  tff(f_33, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, B, D, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t103_enumset1)).
% 11.06/4.32  tff(f_63, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 11.06/4.32  tff(f_39, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k2_tarski(F, G)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_enumset1)).
% 11.06/4.32  tff(f_41, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k4_enumset1(A, B, C, D, E, F), k1_tarski(G)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_enumset1)).
% 11.06/4.32  tff(f_53, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 11.06/4.32  tff(f_68, negated_conjecture, ~(![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, A, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t108_enumset1)).
% 11.06/4.32  tff(c_10, plain, (![A_11, C_13, D_14, B_12]: (k2_enumset1(A_11, C_13, D_14, B_12)=k2_enumset1(A_11, B_12, C_13, D_14))), inference(cnfTransformation, [status(thm)], [f_35])).
% 11.06/4.32  tff(c_34, plain, (![A_80, B_81, C_82, D_83]: (k3_enumset1(A_80, A_80, B_81, C_82, D_83)=k2_enumset1(A_80, B_81, C_82, D_83))), inference(cnfTransformation, [status(thm)], [f_59])).
% 11.06/4.32  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 11.06/4.32  tff(c_696, plain, (![C_151, A_155, B_153, D_152, E_154]: (k2_xboole_0(k2_tarski(A_155, B_153), k1_enumset1(C_151, D_152, E_154))=k3_enumset1(A_155, B_153, C_151, D_152, E_154))), inference(cnfTransformation, [status(thm)], [f_37])).
% 11.06/4.32  tff(c_726, plain, (![C_151, A_155, B_153, D_152, E_154]: (k2_xboole_0(k1_enumset1(C_151, D_152, E_154), k2_tarski(A_155, B_153))=k3_enumset1(A_155, B_153, C_151, D_152, E_154))), inference(superposition, [status(thm), theory('equality')], [c_2, c_696])).
% 11.06/4.32  tff(c_36, plain, (![E_88, C_86, B_85, D_87, A_84]: (k4_enumset1(A_84, A_84, B_85, C_86, D_87, E_88)=k3_enumset1(A_84, B_85, C_86, D_87, E_88))), inference(cnfTransformation, [status(thm)], [f_61])).
% 11.06/4.32  tff(c_32, plain, (![A_77, B_78, C_79]: (k2_enumset1(A_77, A_77, B_78, C_79)=k1_enumset1(A_77, B_78, C_79))), inference(cnfTransformation, [status(thm)], [f_57])).
% 11.06/4.32  tff(c_201, plain, (![A_121, B_122, D_123, C_124]: (k2_enumset1(A_121, B_122, D_123, C_124)=k2_enumset1(A_121, B_122, C_124, D_123))), inference(cnfTransformation, [status(thm)], [f_33])).
% 11.06/4.32  tff(c_274, plain, (![A_77, C_79, B_78]: (k2_enumset1(A_77, A_77, C_79, B_78)=k1_enumset1(A_77, B_78, C_79))), inference(superposition, [status(thm), theory('equality')], [c_32, c_201])).
% 11.06/4.32  tff(c_38, plain, (![D_92, C_91, F_94, A_89, B_90, E_93]: (k5_enumset1(A_89, A_89, B_90, C_91, D_92, E_93, F_94)=k4_enumset1(A_89, B_90, C_91, D_92, E_93, F_94))), inference(cnfTransformation, [status(thm)], [f_63])).
% 11.06/4.32  tff(c_1192, plain, (![E_188, F_190, D_187, C_184, B_186, A_189, G_185]: (k2_xboole_0(k3_enumset1(A_189, B_186, C_184, D_187, E_188), k2_tarski(F_190, G_185))=k5_enumset1(A_189, B_186, C_184, D_187, E_188, F_190, G_185))), inference(cnfTransformation, [status(thm)], [f_39])).
% 11.06/4.32  tff(c_1207, plain, (![F_190, B_81, D_83, A_80, G_185, C_82]: (k5_enumset1(A_80, A_80, B_81, C_82, D_83, F_190, G_185)=k2_xboole_0(k2_enumset1(A_80, B_81, C_82, D_83), k2_tarski(F_190, G_185)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_1192])).
% 11.06/4.32  tff(c_3230, plain, (![F_282, A_283, C_285, D_286, G_287, B_284]: (k2_xboole_0(k2_enumset1(A_283, B_284, C_285, D_286), k2_tarski(F_282, G_287))=k4_enumset1(A_283, B_284, C_285, D_286, F_282, G_287))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_1207])).
% 11.06/4.32  tff(c_3299, plain, (![F_282, B_78, A_77, C_79, G_287]: (k4_enumset1(A_77, A_77, C_79, B_78, F_282, G_287)=k2_xboole_0(k1_enumset1(A_77, B_78, C_79), k2_tarski(F_282, G_287)))), inference(superposition, [status(thm), theory('equality')], [c_274, c_3230])).
% 11.06/4.32  tff(c_4257, plain, (![G_328, F_326, C_327, B_325, A_324]: (k3_enumset1(F_326, G_328, A_324, B_325, C_327)=k3_enumset1(A_324, C_327, B_325, F_326, G_328))), inference(demodulation, [status(thm), theory('equality')], [c_726, c_36, c_3299])).
% 11.06/4.32  tff(c_4330, plain, (![B_81, D_83, C_82, A_80]: (k3_enumset1(B_81, D_83, C_82, A_80, A_80)=k2_enumset1(A_80, B_81, C_82, D_83))), inference(superposition, [status(thm), theory('equality')], [c_34, c_4257])).
% 11.06/4.32  tff(c_762, plain, (![C_170, D_171, A_175, B_173, G_174, F_169, E_172]: (k2_xboole_0(k4_enumset1(A_175, B_173, C_170, D_171, E_172, F_169), k1_tarski(G_174))=k5_enumset1(A_175, B_173, C_170, D_171, E_172, F_169, G_174))), inference(cnfTransformation, [status(thm)], [f_41])).
% 11.06/4.32  tff(c_777, plain, (![E_88, C_86, B_85, D_87, A_84, G_174]: (k5_enumset1(A_84, A_84, B_85, C_86, D_87, E_88, G_174)=k2_xboole_0(k3_enumset1(A_84, B_85, C_86, D_87, E_88), k1_tarski(G_174)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_762])).
% 11.06/4.32  tff(c_786, plain, (![E_88, C_86, B_85, D_87, A_84, G_174]: (k2_xboole_0(k3_enumset1(A_84, B_85, C_86, D_87, E_88), k1_tarski(G_174))=k4_enumset1(A_84, B_85, C_86, D_87, E_88, G_174))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_777])).
% 11.06/4.32  tff(c_28, plain, (![A_74]: (k2_tarski(A_74, A_74)=k1_tarski(A_74))), inference(cnfTransformation, [status(thm)], [f_53])).
% 11.06/4.32  tff(c_1216, plain, (![E_188, A_74, D_187, C_184, B_186, A_189]: (k5_enumset1(A_189, B_186, C_184, D_187, E_188, A_74, A_74)=k2_xboole_0(k3_enumset1(A_189, B_186, C_184, D_187, E_188), k1_tarski(A_74)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_1192])).
% 11.06/4.32  tff(c_3601, plain, (![C_296, B_292, A_294, D_291, A_295, E_293]: (k5_enumset1(A_295, B_292, C_296, D_291, E_293, A_294, A_294)=k4_enumset1(A_295, B_292, C_296, D_291, E_293, A_294))), inference(demodulation, [status(thm), theory('equality')], [c_786, c_1216])).
% 11.06/4.32  tff(c_3621, plain, (![D_92, C_91, F_94, A_89, B_90]: (k4_enumset1(A_89, B_90, C_91, D_92, F_94, F_94)=k4_enumset1(A_89, A_89, B_90, C_91, D_92, F_94))), inference(superposition, [status(thm), theory('equality')], [c_38, c_3601])).
% 11.06/4.32  tff(c_31937, plain, (![C_706, B_707, F_709, A_708, D_710]: (k4_enumset1(A_708, B_707, C_706, D_710, F_709, F_709)=k3_enumset1(A_708, B_707, C_706, D_710, F_709))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_3621])).
% 11.06/4.32  tff(c_31988, plain, (![A_84, B_85, C_86, E_88]: (k3_enumset1(A_84, B_85, C_86, E_88, E_88)=k3_enumset1(A_84, A_84, B_85, C_86, E_88))), inference(superposition, [status(thm), theory('equality')], [c_36, c_31937])).
% 11.06/4.32  tff(c_32002, plain, (![E_88, A_84, C_86, B_85]: (k2_enumset1(E_88, A_84, C_86, B_85)=k2_enumset1(A_84, B_85, C_86, E_88))), inference(demodulation, [status(thm), theory('equality')], [c_4330, c_34, c_31988])).
% 11.06/4.32  tff(c_8, plain, (![A_7, B_8, D_10, C_9]: (k2_enumset1(A_7, B_8, D_10, C_9)=k2_enumset1(A_7, B_8, C_9, D_10))), inference(cnfTransformation, [status(thm)], [f_33])).
% 11.06/4.32  tff(c_42, plain, (k2_enumset1('#skF_2', '#skF_1', '#skF_3', '#skF_4')!=k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_68])).
% 11.06/4.32  tff(c_43, plain, (k2_enumset1('#skF_2', '#skF_4', '#skF_1', '#skF_3')!=k2_enumset1('#skF_1', '#skF_4', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_10, c_42])).
% 11.06/4.32  tff(c_44, plain, (k2_enumset1('#skF_2', '#skF_4', '#skF_1', '#skF_3')!=k2_enumset1('#skF_1', '#skF_4', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_43])).
% 11.06/4.32  tff(c_34544, plain, (k2_enumset1('#skF_4', '#skF_2', '#skF_3', '#skF_1')!=k2_enumset1('#skF_4', '#skF_3', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32002, c_32002, c_44])).
% 11.06/4.32  tff(c_34547, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_10, c_34544])).
% 11.06/4.32  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.06/4.32  
% 11.06/4.32  Inference rules
% 11.06/4.32  ----------------------
% 11.06/4.32  #Ref     : 0
% 11.06/4.32  #Sup     : 7581
% 11.06/4.32  #Fact    : 0
% 11.06/4.32  #Define  : 0
% 11.06/4.32  #Split   : 0
% 11.06/4.32  #Chain   : 0
% 11.06/4.32  #Close   : 0
% 11.06/4.32  
% 11.06/4.32  Ordering : KBO
% 11.06/4.32  
% 11.06/4.32  Simplification rules
% 11.06/4.32  ----------------------
% 11.06/4.32  #Subsume      : 742
% 11.06/4.32  #Demod        : 11100
% 11.06/4.32  #Tautology    : 5953
% 11.06/4.32  #SimpNegUnit  : 0
% 11.06/4.32  #BackRed      : 13
% 11.06/4.32  
% 11.06/4.32  #Partial instantiations: 0
% 11.06/4.32  #Strategies tried      : 1
% 11.06/4.32  
% 11.06/4.32  Timing (in seconds)
% 11.06/4.32  ----------------------
% 11.06/4.32  Preprocessing        : 0.34
% 11.06/4.32  Parsing              : 0.18
% 11.06/4.32  CNF conversion       : 0.02
% 11.06/4.32  Main loop            : 3.21
% 11.06/4.32  Inferencing          : 0.83
% 11.06/4.32  Reduction            : 1.77
% 11.06/4.32  Demodulation         : 1.58
% 11.06/4.32  BG Simplification    : 0.09
% 11.06/4.32  Subsumption          : 0.39
% 11.06/4.32  Abstraction          : 0.15
% 11.06/4.32  MUC search           : 0.00
% 11.06/4.32  Cooper               : 0.00
% 11.06/4.32  Total                : 3.58
% 11.06/4.32  Index Insertion      : 0.00
% 11.06/4.32  Index Deletion       : 0.00
% 11.06/4.32  Index Matching       : 0.00
% 11.06/4.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
