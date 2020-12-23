%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:09 EST 2020

% Result     : Theorem 3.25s
% Output     : CNFRefutation 3.25s
% Verified   : 
% Statistics : Number of formulae       :   52 (  70 expanded)
%              Number of leaves         :   25 (  35 expanded)
%              Depth                    :    8
%              Number of atoms          :   35 (  53 expanded)
%              Number of equality atoms :   34 (  52 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

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

tff(f_39,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k2_tarski(A,B),k1_tarski(C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_enumset1)).

tff(f_53,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_55,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k2_tarski(A,B),k1_enumset1(C,D,E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_tarski(A),k1_enumset1(B,C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_tarski(A),k2_enumset1(B,C,D,E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_enumset1(A,B,C),k2_tarski(D,E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l57_enumset1)).

tff(f_58,negated_conjecture,(
    ~ ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(c_14,plain,(
    ! [A_21,B_22,C_23] : k2_xboole_0(k2_tarski(A_21,B_22),k1_tarski(C_23)) = k1_enumset1(A_21,B_22,C_23) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_28,plain,(
    ! [A_58] : k2_tarski(A_58,A_58) = k1_tarski(A_58) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_30,plain,(
    ! [A_59,B_60] : k1_enumset1(A_59,A_59,B_60) = k2_tarski(A_59,B_60) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_548,plain,(
    ! [A_116,D_119,E_117,B_120,C_118] : k2_xboole_0(k2_tarski(A_116,B_120),k1_enumset1(C_118,D_119,E_117)) = k3_enumset1(A_116,B_120,C_118,D_119,E_117) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1066,plain,(
    ! [A_170,B_171,A_172,B_173] : k3_enumset1(A_170,B_171,A_172,A_172,B_173) = k2_xboole_0(k2_tarski(A_170,B_171),k2_tarski(A_172,B_173)) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_548])).

tff(c_1140,plain,(
    ! [A_170,B_171,A_58] : k3_enumset1(A_170,B_171,A_58,A_58,A_58) = k2_xboole_0(k2_tarski(A_170,B_171),k1_tarski(A_58)) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_1066])).

tff(c_1157,plain,(
    ! [A_170,B_171,A_58] : k3_enumset1(A_170,B_171,A_58,A_58,A_58) = k1_enumset1(A_170,B_171,A_58) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1140])).

tff(c_186,plain,(
    ! [A_75,B_76,C_77] : k2_xboole_0(k2_tarski(A_75,B_76),k1_tarski(C_77)) = k1_enumset1(A_75,B_76,C_77) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_195,plain,(
    ! [A_58,C_77] : k2_xboole_0(k1_tarski(A_58),k1_tarski(C_77)) = k1_enumset1(A_58,A_58,C_77) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_186])).

tff(c_198,plain,(
    ! [A_58,C_77] : k2_xboole_0(k1_tarski(A_58),k1_tarski(C_77)) = k2_tarski(A_58,C_77) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_195])).

tff(c_208,plain,(
    ! [A_80,B_81,C_82,D_83] : k2_xboole_0(k1_tarski(A_80),k1_enumset1(B_81,C_82,D_83)) = k2_enumset1(A_80,B_81,C_82,D_83) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_220,plain,(
    ! [A_84,A_85,B_86] : k2_xboole_0(k1_tarski(A_84),k2_tarski(A_85,B_86)) = k2_enumset1(A_84,A_85,A_85,B_86) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_208])).

tff(c_235,plain,(
    ! [A_84,A_58] : k2_xboole_0(k1_tarski(A_84),k1_tarski(A_58)) = k2_enumset1(A_84,A_58,A_58,A_58) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_220])).

tff(c_240,plain,(
    ! [A_84,A_58] : k2_enumset1(A_84,A_58,A_58,A_58) = k2_tarski(A_84,A_58) ),
    inference(demodulation,[status(thm),theory(equality)],[c_198,c_235])).

tff(c_446,plain,(
    ! [C_105,D_107,A_104,E_103,B_106] : k2_xboole_0(k1_tarski(A_104),k2_enumset1(B_106,C_105,D_107,E_103)) = k3_enumset1(A_104,B_106,C_105,D_107,E_103) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_455,plain,(
    ! [A_104,A_84,A_58] : k3_enumset1(A_104,A_84,A_58,A_58,A_58) = k2_xboole_0(k1_tarski(A_104),k2_tarski(A_84,A_58)) ),
    inference(superposition,[status(thm),theory(equality)],[c_240,c_446])).

tff(c_1308,plain,(
    ! [A_104,A_84,A_58] : k2_xboole_0(k1_tarski(A_104),k2_tarski(A_84,A_58)) = k1_enumset1(A_104,A_84,A_58) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1157,c_455])).

tff(c_16,plain,(
    ! [A_24,B_25,C_26,D_27] : k2_xboole_0(k1_tarski(A_24),k1_enumset1(B_25,C_26,D_27)) = k2_enumset1(A_24,B_25,C_26,D_27) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_560,plain,(
    ! [A_58,C_118,D_119,E_117] : k3_enumset1(A_58,A_58,C_118,D_119,E_117) = k2_xboole_0(k1_tarski(A_58),k1_enumset1(C_118,D_119,E_117)) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_548])).

tff(c_563,plain,(
    ! [A_58,C_118,D_119,E_117] : k3_enumset1(A_58,A_58,C_118,D_119,E_117) = k2_enumset1(A_58,C_118,D_119,E_117) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_560])).

tff(c_306,plain,(
    ! [C_96,D_95,B_92,A_94,E_93] : k2_xboole_0(k1_enumset1(A_94,B_92,C_96),k2_tarski(D_95,E_93)) = k3_enumset1(A_94,B_92,C_96,D_95,E_93) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_315,plain,(
    ! [A_59,B_60,D_95,E_93] : k3_enumset1(A_59,A_59,B_60,D_95,E_93) = k2_xboole_0(k2_tarski(A_59,B_60),k2_tarski(D_95,E_93)) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_306])).

tff(c_1800,plain,(
    ! [A_211,B_212,D_213,E_214] : k2_xboole_0(k2_tarski(A_211,B_212),k2_tarski(D_213,E_214)) = k2_enumset1(A_211,B_212,D_213,E_214) ),
    inference(demodulation,[status(thm),theory(equality)],[c_563,c_315])).

tff(c_1809,plain,(
    ! [A_58,D_213,E_214] : k2_xboole_0(k1_tarski(A_58),k2_tarski(D_213,E_214)) = k2_enumset1(A_58,A_58,D_213,E_214) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_1800])).

tff(c_1815,plain,(
    ! [A_58,D_213,E_214] : k2_enumset1(A_58,A_58,D_213,E_214) = k1_enumset1(A_58,D_213,E_214) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1308,c_1809])).

tff(c_32,plain,(
    k2_enumset1('#skF_1','#skF_1','#skF_2','#skF_3') != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1819,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1815,c_32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:02:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.25/1.51  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.25/1.51  
% 3.25/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.25/1.51  %$ k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 3.25/1.51  
% 3.25/1.51  %Foreground sorts:
% 3.25/1.51  
% 3.25/1.51  
% 3.25/1.51  %Background operators:
% 3.25/1.51  
% 3.25/1.51  
% 3.25/1.51  %Foreground operators:
% 3.25/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.25/1.51  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.25/1.51  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.25/1.51  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.25/1.51  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.25/1.51  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.25/1.51  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.25/1.51  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.25/1.51  tff('#skF_2', type, '#skF_2': $i).
% 3.25/1.51  tff('#skF_3', type, '#skF_3': $i).
% 3.25/1.51  tff('#skF_1', type, '#skF_1': $i).
% 3.25/1.51  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.25/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.25/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.25/1.51  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.25/1.51  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.25/1.51  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.25/1.51  
% 3.25/1.52  tff(f_39, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k2_tarski(A, B), k1_tarski(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_enumset1)).
% 3.25/1.52  tff(f_53, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.25/1.52  tff(f_55, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 3.25/1.52  tff(f_45, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k2_tarski(A, B), k1_enumset1(C, D, E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_enumset1)).
% 3.25/1.52  tff(f_41, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_tarski(A), k1_enumset1(B, C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_enumset1)).
% 3.25/1.52  tff(f_43, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_tarski(A), k2_enumset1(B, C, D, E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_enumset1)).
% 3.25/1.52  tff(f_35, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_enumset1(A, B, C), k2_tarski(D, E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l57_enumset1)).
% 3.25/1.52  tff(f_58, negated_conjecture, ~(![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 3.25/1.52  tff(c_14, plain, (![A_21, B_22, C_23]: (k2_xboole_0(k2_tarski(A_21, B_22), k1_tarski(C_23))=k1_enumset1(A_21, B_22, C_23))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.25/1.52  tff(c_28, plain, (![A_58]: (k2_tarski(A_58, A_58)=k1_tarski(A_58))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.25/1.52  tff(c_30, plain, (![A_59, B_60]: (k1_enumset1(A_59, A_59, B_60)=k2_tarski(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.25/1.52  tff(c_548, plain, (![A_116, D_119, E_117, B_120, C_118]: (k2_xboole_0(k2_tarski(A_116, B_120), k1_enumset1(C_118, D_119, E_117))=k3_enumset1(A_116, B_120, C_118, D_119, E_117))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.25/1.52  tff(c_1066, plain, (![A_170, B_171, A_172, B_173]: (k3_enumset1(A_170, B_171, A_172, A_172, B_173)=k2_xboole_0(k2_tarski(A_170, B_171), k2_tarski(A_172, B_173)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_548])).
% 3.25/1.52  tff(c_1140, plain, (![A_170, B_171, A_58]: (k3_enumset1(A_170, B_171, A_58, A_58, A_58)=k2_xboole_0(k2_tarski(A_170, B_171), k1_tarski(A_58)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_1066])).
% 3.25/1.52  tff(c_1157, plain, (![A_170, B_171, A_58]: (k3_enumset1(A_170, B_171, A_58, A_58, A_58)=k1_enumset1(A_170, B_171, A_58))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_1140])).
% 3.25/1.52  tff(c_186, plain, (![A_75, B_76, C_77]: (k2_xboole_0(k2_tarski(A_75, B_76), k1_tarski(C_77))=k1_enumset1(A_75, B_76, C_77))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.25/1.52  tff(c_195, plain, (![A_58, C_77]: (k2_xboole_0(k1_tarski(A_58), k1_tarski(C_77))=k1_enumset1(A_58, A_58, C_77))), inference(superposition, [status(thm), theory('equality')], [c_28, c_186])).
% 3.25/1.52  tff(c_198, plain, (![A_58, C_77]: (k2_xboole_0(k1_tarski(A_58), k1_tarski(C_77))=k2_tarski(A_58, C_77))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_195])).
% 3.25/1.52  tff(c_208, plain, (![A_80, B_81, C_82, D_83]: (k2_xboole_0(k1_tarski(A_80), k1_enumset1(B_81, C_82, D_83))=k2_enumset1(A_80, B_81, C_82, D_83))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.25/1.52  tff(c_220, plain, (![A_84, A_85, B_86]: (k2_xboole_0(k1_tarski(A_84), k2_tarski(A_85, B_86))=k2_enumset1(A_84, A_85, A_85, B_86))), inference(superposition, [status(thm), theory('equality')], [c_30, c_208])).
% 3.25/1.52  tff(c_235, plain, (![A_84, A_58]: (k2_xboole_0(k1_tarski(A_84), k1_tarski(A_58))=k2_enumset1(A_84, A_58, A_58, A_58))), inference(superposition, [status(thm), theory('equality')], [c_28, c_220])).
% 3.25/1.52  tff(c_240, plain, (![A_84, A_58]: (k2_enumset1(A_84, A_58, A_58, A_58)=k2_tarski(A_84, A_58))), inference(demodulation, [status(thm), theory('equality')], [c_198, c_235])).
% 3.25/1.52  tff(c_446, plain, (![C_105, D_107, A_104, E_103, B_106]: (k2_xboole_0(k1_tarski(A_104), k2_enumset1(B_106, C_105, D_107, E_103))=k3_enumset1(A_104, B_106, C_105, D_107, E_103))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.25/1.52  tff(c_455, plain, (![A_104, A_84, A_58]: (k3_enumset1(A_104, A_84, A_58, A_58, A_58)=k2_xboole_0(k1_tarski(A_104), k2_tarski(A_84, A_58)))), inference(superposition, [status(thm), theory('equality')], [c_240, c_446])).
% 3.25/1.52  tff(c_1308, plain, (![A_104, A_84, A_58]: (k2_xboole_0(k1_tarski(A_104), k2_tarski(A_84, A_58))=k1_enumset1(A_104, A_84, A_58))), inference(demodulation, [status(thm), theory('equality')], [c_1157, c_455])).
% 3.25/1.52  tff(c_16, plain, (![A_24, B_25, C_26, D_27]: (k2_xboole_0(k1_tarski(A_24), k1_enumset1(B_25, C_26, D_27))=k2_enumset1(A_24, B_25, C_26, D_27))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.25/1.52  tff(c_560, plain, (![A_58, C_118, D_119, E_117]: (k3_enumset1(A_58, A_58, C_118, D_119, E_117)=k2_xboole_0(k1_tarski(A_58), k1_enumset1(C_118, D_119, E_117)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_548])).
% 3.25/1.52  tff(c_563, plain, (![A_58, C_118, D_119, E_117]: (k3_enumset1(A_58, A_58, C_118, D_119, E_117)=k2_enumset1(A_58, C_118, D_119, E_117))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_560])).
% 3.25/1.52  tff(c_306, plain, (![C_96, D_95, B_92, A_94, E_93]: (k2_xboole_0(k1_enumset1(A_94, B_92, C_96), k2_tarski(D_95, E_93))=k3_enumset1(A_94, B_92, C_96, D_95, E_93))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.25/1.52  tff(c_315, plain, (![A_59, B_60, D_95, E_93]: (k3_enumset1(A_59, A_59, B_60, D_95, E_93)=k2_xboole_0(k2_tarski(A_59, B_60), k2_tarski(D_95, E_93)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_306])).
% 3.25/1.52  tff(c_1800, plain, (![A_211, B_212, D_213, E_214]: (k2_xboole_0(k2_tarski(A_211, B_212), k2_tarski(D_213, E_214))=k2_enumset1(A_211, B_212, D_213, E_214))), inference(demodulation, [status(thm), theory('equality')], [c_563, c_315])).
% 3.25/1.52  tff(c_1809, plain, (![A_58, D_213, E_214]: (k2_xboole_0(k1_tarski(A_58), k2_tarski(D_213, E_214))=k2_enumset1(A_58, A_58, D_213, E_214))), inference(superposition, [status(thm), theory('equality')], [c_28, c_1800])).
% 3.25/1.52  tff(c_1815, plain, (![A_58, D_213, E_214]: (k2_enumset1(A_58, A_58, D_213, E_214)=k1_enumset1(A_58, D_213, E_214))), inference(demodulation, [status(thm), theory('equality')], [c_1308, c_1809])).
% 3.25/1.52  tff(c_32, plain, (k2_enumset1('#skF_1', '#skF_1', '#skF_2', '#skF_3')!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.25/1.52  tff(c_1819, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1815, c_32])).
% 3.25/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.25/1.52  
% 3.25/1.52  Inference rules
% 3.25/1.52  ----------------------
% 3.25/1.52  #Ref     : 0
% 3.25/1.52  #Sup     : 413
% 3.25/1.52  #Fact    : 0
% 3.25/1.52  #Define  : 0
% 3.25/1.52  #Split   : 0
% 3.25/1.52  #Chain   : 0
% 3.25/1.52  #Close   : 0
% 3.25/1.52  
% 3.25/1.52  Ordering : KBO
% 3.25/1.52  
% 3.25/1.52  Simplification rules
% 3.25/1.52  ----------------------
% 3.25/1.52  #Subsume      : 7
% 3.25/1.52  #Demod        : 330
% 3.25/1.52  #Tautology    : 289
% 3.25/1.52  #SimpNegUnit  : 0
% 3.25/1.52  #BackRed      : 6
% 3.25/1.52  
% 3.25/1.52  #Partial instantiations: 0
% 3.25/1.52  #Strategies tried      : 1
% 3.25/1.52  
% 3.25/1.52  Timing (in seconds)
% 3.25/1.52  ----------------------
% 3.25/1.53  Preprocessing        : 0.31
% 3.25/1.53  Parsing              : 0.17
% 3.25/1.53  CNF conversion       : 0.02
% 3.25/1.53  Main loop            : 0.46
% 3.25/1.53  Inferencing          : 0.19
% 3.25/1.53  Reduction            : 0.17
% 3.25/1.53  Demodulation         : 0.14
% 3.25/1.53  BG Simplification    : 0.03
% 3.25/1.53  Subsumption          : 0.05
% 3.25/1.53  Abstraction          : 0.03
% 3.25/1.53  MUC search           : 0.00
% 3.25/1.53  Cooper               : 0.00
% 3.25/1.53  Total                : 0.80
% 3.25/1.53  Index Insertion      : 0.00
% 3.25/1.53  Index Deletion       : 0.00
% 3.25/1.53  Index Matching       : 0.00
% 3.25/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
