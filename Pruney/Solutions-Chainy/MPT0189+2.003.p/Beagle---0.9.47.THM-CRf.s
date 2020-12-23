%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:50 EST 2020

% Result     : Theorem 7.43s
% Output     : CNFRefutation 7.43s
% Verified   : 
% Statistics : Number of formulae       :   50 (  87 expanded)
%              Number of leaves         :   26 (  43 expanded)
%              Depth                    :    9
%              Number of atoms          :   31 (  68 expanded)
%              Number of equality atoms :   30 (  67 expanded)
%              Maximal formula depth    :   10 (   4 average)
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

tff(f_37,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(B,C,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,C,D,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_enumset1)).

tff(f_31,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_49,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_47,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_60,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,A,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_enumset1)).

tff(c_12,plain,(
    ! [A_14,B_15,C_16,D_17] : k2_xboole_0(k1_enumset1(A_14,B_15,C_16),k1_tarski(D_17)) = k2_enumset1(A_14,B_15,C_16,D_17) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_8,plain,(
    ! [B_8,C_9,A_7] : k1_enumset1(B_8,C_9,A_7) = k1_enumset1(A_7,B_8,C_9) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_378,plain,(
    ! [A_102,B_103,C_104,D_105] : k2_xboole_0(k1_enumset1(A_102,B_103,C_104),k1_tarski(D_105)) = k2_enumset1(A_102,B_103,C_104,D_105) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1210,plain,(
    ! [B_179,C_180,A_181,D_182] : k2_xboole_0(k1_enumset1(B_179,C_180,A_181),k1_tarski(D_182)) = k2_enumset1(A_181,B_179,C_180,D_182) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_378])).

tff(c_1266,plain,(
    ! [C_183,A_184,B_185,D_186] : k2_enumset1(C_183,A_184,B_185,D_186) = k2_enumset1(A_184,B_185,C_183,D_186) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_1210])).

tff(c_10,plain,(
    ! [A_10,C_12,D_13,B_11] : k2_enumset1(A_10,C_12,D_13,B_11) = k2_enumset1(A_10,B_11,C_12,D_13) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1324,plain,(
    ! [C_183,A_184,B_185,D_186] : k2_enumset1(C_183,A_184,B_185,D_186) = k2_enumset1(A_184,C_183,D_186,B_185) ),
    inference(superposition,[status(thm),theory(equality)],[c_1266,c_10])).

tff(c_6,plain,(
    ! [B_6,A_5] : k2_tarski(B_6,A_5) = k2_tarski(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_24,plain,(
    ! [A_44,B_45,C_46] : k2_enumset1(A_44,A_44,B_45,C_46) = k1_enumset1(A_44,B_45,C_46) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_22,plain,(
    ! [A_42,B_43] : k1_enumset1(A_42,A_42,B_43) = k2_tarski(A_42,B_43) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_399,plain,(
    ! [A_42,B_43,D_105] : k2_xboole_0(k2_tarski(A_42,B_43),k1_tarski(D_105)) = k2_enumset1(A_42,A_42,B_43,D_105) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_378])).

tff(c_407,plain,(
    ! [A_106,B_107,D_108] : k2_xboole_0(k2_tarski(A_106,B_107),k1_tarski(D_108)) = k1_enumset1(A_106,B_107,D_108) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_399])).

tff(c_444,plain,(
    ! [B_116,A_117,D_118] : k2_xboole_0(k2_tarski(B_116,A_117),k1_tarski(D_118)) = k1_enumset1(A_117,B_116,D_118) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_407])).

tff(c_403,plain,(
    ! [A_42,B_43,D_105] : k2_xboole_0(k2_tarski(A_42,B_43),k1_tarski(D_105)) = k1_enumset1(A_42,B_43,D_105) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_399])).

tff(c_471,plain,(
    ! [B_119,A_120,D_121] : k1_enumset1(B_119,A_120,D_121) = k1_enumset1(A_120,B_119,D_121) ),
    inference(superposition,[status(thm),theory(equality)],[c_444,c_403])).

tff(c_4266,plain,(
    ! [A_279,B_280,D_281,D_282] : k2_xboole_0(k1_enumset1(A_279,B_280,D_281),k1_tarski(D_282)) = k2_enumset1(B_280,A_279,D_281,D_282) ),
    inference(superposition,[status(thm),theory(equality)],[c_471,c_12])).

tff(c_5133,plain,(
    ! [B_291,A_292,D_293,D_294] : k2_enumset1(B_291,A_292,D_293,D_294) = k2_enumset1(A_292,B_291,D_293,D_294) ),
    inference(superposition,[status(thm),theory(equality)],[c_4266,c_12])).

tff(c_5426,plain,(
    ! [C_183,A_184,D_186,B_185] : k2_enumset1(C_183,A_184,D_186,B_185) = k2_enumset1(C_183,A_184,B_185,D_186) ),
    inference(superposition,[status(thm),theory(equality)],[c_1324,c_5133])).

tff(c_1240,plain,(
    ! [C_16,A_14,B_15,D_17] : k2_enumset1(C_16,A_14,B_15,D_17) = k2_enumset1(A_14,B_15,C_16,D_17) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_1210])).

tff(c_34,plain,(
    k2_enumset1('#skF_2','#skF_1','#skF_3','#skF_4') != k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_35,plain,(
    k2_enumset1('#skF_2','#skF_4','#skF_1','#skF_3') != k2_enumset1('#skF_1','#skF_4','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_10,c_34])).

tff(c_1264,plain,(
    k2_enumset1('#skF_4','#skF_2','#skF_1','#skF_3') != k2_enumset1('#skF_4','#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1240,c_1240,c_35])).

tff(c_1265,plain,(
    k2_enumset1('#skF_4','#skF_1','#skF_2','#skF_3') != k2_enumset1('#skF_4','#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_10,c_1264])).

tff(c_7113,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5426,c_1265])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:56:41 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.43/2.50  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.43/2.51  
% 7.43/2.51  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.43/2.51  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 7.43/2.51  
% 7.43/2.51  %Foreground sorts:
% 7.43/2.51  
% 7.43/2.51  
% 7.43/2.51  %Background operators:
% 7.43/2.51  
% 7.43/2.51  
% 7.43/2.51  %Foreground operators:
% 7.43/2.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.43/2.51  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.43/2.51  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.43/2.51  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 7.43/2.51  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 7.43/2.51  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 7.43/2.51  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.43/2.51  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.43/2.51  tff('#skF_2', type, '#skF_2': $i).
% 7.43/2.51  tff('#skF_3', type, '#skF_3': $i).
% 7.43/2.51  tff('#skF_1', type, '#skF_1': $i).
% 7.43/2.51  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.43/2.51  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 7.43/2.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.43/2.51  tff('#skF_4', type, '#skF_4': $i).
% 7.43/2.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.43/2.51  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.43/2.51  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.43/2.51  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 7.43/2.51  
% 7.43/2.52  tff(f_37, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_enumset1)).
% 7.43/2.52  tff(f_33, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(B, C, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_enumset1)).
% 7.43/2.52  tff(f_35, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, C, D, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t105_enumset1)).
% 7.43/2.52  tff(f_31, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 7.43/2.52  tff(f_49, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 7.43/2.52  tff(f_47, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 7.43/2.52  tff(f_60, negated_conjecture, ~(![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, A, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t108_enumset1)).
% 7.43/2.52  tff(c_12, plain, (![A_14, B_15, C_16, D_17]: (k2_xboole_0(k1_enumset1(A_14, B_15, C_16), k1_tarski(D_17))=k2_enumset1(A_14, B_15, C_16, D_17))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.43/2.52  tff(c_8, plain, (![B_8, C_9, A_7]: (k1_enumset1(B_8, C_9, A_7)=k1_enumset1(A_7, B_8, C_9))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.43/2.52  tff(c_378, plain, (![A_102, B_103, C_104, D_105]: (k2_xboole_0(k1_enumset1(A_102, B_103, C_104), k1_tarski(D_105))=k2_enumset1(A_102, B_103, C_104, D_105))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.43/2.52  tff(c_1210, plain, (![B_179, C_180, A_181, D_182]: (k2_xboole_0(k1_enumset1(B_179, C_180, A_181), k1_tarski(D_182))=k2_enumset1(A_181, B_179, C_180, D_182))), inference(superposition, [status(thm), theory('equality')], [c_8, c_378])).
% 7.43/2.52  tff(c_1266, plain, (![C_183, A_184, B_185, D_186]: (k2_enumset1(C_183, A_184, B_185, D_186)=k2_enumset1(A_184, B_185, C_183, D_186))), inference(superposition, [status(thm), theory('equality')], [c_12, c_1210])).
% 7.43/2.52  tff(c_10, plain, (![A_10, C_12, D_13, B_11]: (k2_enumset1(A_10, C_12, D_13, B_11)=k2_enumset1(A_10, B_11, C_12, D_13))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.43/2.52  tff(c_1324, plain, (![C_183, A_184, B_185, D_186]: (k2_enumset1(C_183, A_184, B_185, D_186)=k2_enumset1(A_184, C_183, D_186, B_185))), inference(superposition, [status(thm), theory('equality')], [c_1266, c_10])).
% 7.43/2.52  tff(c_6, plain, (![B_6, A_5]: (k2_tarski(B_6, A_5)=k2_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.43/2.52  tff(c_24, plain, (![A_44, B_45, C_46]: (k2_enumset1(A_44, A_44, B_45, C_46)=k1_enumset1(A_44, B_45, C_46))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.43/2.52  tff(c_22, plain, (![A_42, B_43]: (k1_enumset1(A_42, A_42, B_43)=k2_tarski(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.43/2.52  tff(c_399, plain, (![A_42, B_43, D_105]: (k2_xboole_0(k2_tarski(A_42, B_43), k1_tarski(D_105))=k2_enumset1(A_42, A_42, B_43, D_105))), inference(superposition, [status(thm), theory('equality')], [c_22, c_378])).
% 7.43/2.52  tff(c_407, plain, (![A_106, B_107, D_108]: (k2_xboole_0(k2_tarski(A_106, B_107), k1_tarski(D_108))=k1_enumset1(A_106, B_107, D_108))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_399])).
% 7.43/2.52  tff(c_444, plain, (![B_116, A_117, D_118]: (k2_xboole_0(k2_tarski(B_116, A_117), k1_tarski(D_118))=k1_enumset1(A_117, B_116, D_118))), inference(superposition, [status(thm), theory('equality')], [c_6, c_407])).
% 7.43/2.52  tff(c_403, plain, (![A_42, B_43, D_105]: (k2_xboole_0(k2_tarski(A_42, B_43), k1_tarski(D_105))=k1_enumset1(A_42, B_43, D_105))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_399])).
% 7.43/2.52  tff(c_471, plain, (![B_119, A_120, D_121]: (k1_enumset1(B_119, A_120, D_121)=k1_enumset1(A_120, B_119, D_121))), inference(superposition, [status(thm), theory('equality')], [c_444, c_403])).
% 7.43/2.52  tff(c_4266, plain, (![A_279, B_280, D_281, D_282]: (k2_xboole_0(k1_enumset1(A_279, B_280, D_281), k1_tarski(D_282))=k2_enumset1(B_280, A_279, D_281, D_282))), inference(superposition, [status(thm), theory('equality')], [c_471, c_12])).
% 7.43/2.52  tff(c_5133, plain, (![B_291, A_292, D_293, D_294]: (k2_enumset1(B_291, A_292, D_293, D_294)=k2_enumset1(A_292, B_291, D_293, D_294))), inference(superposition, [status(thm), theory('equality')], [c_4266, c_12])).
% 7.43/2.52  tff(c_5426, plain, (![C_183, A_184, D_186, B_185]: (k2_enumset1(C_183, A_184, D_186, B_185)=k2_enumset1(C_183, A_184, B_185, D_186))), inference(superposition, [status(thm), theory('equality')], [c_1324, c_5133])).
% 7.43/2.52  tff(c_1240, plain, (![C_16, A_14, B_15, D_17]: (k2_enumset1(C_16, A_14, B_15, D_17)=k2_enumset1(A_14, B_15, C_16, D_17))), inference(superposition, [status(thm), theory('equality')], [c_12, c_1210])).
% 7.43/2.52  tff(c_34, plain, (k2_enumset1('#skF_2', '#skF_1', '#skF_3', '#skF_4')!=k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.43/2.52  tff(c_35, plain, (k2_enumset1('#skF_2', '#skF_4', '#skF_1', '#skF_3')!=k2_enumset1('#skF_1', '#skF_4', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_10, c_34])).
% 7.43/2.52  tff(c_1264, plain, (k2_enumset1('#skF_4', '#skF_2', '#skF_1', '#skF_3')!=k2_enumset1('#skF_4', '#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1240, c_1240, c_35])).
% 7.43/2.52  tff(c_1265, plain, (k2_enumset1('#skF_4', '#skF_1', '#skF_2', '#skF_3')!=k2_enumset1('#skF_4', '#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_10, c_1264])).
% 7.43/2.52  tff(c_7113, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5426, c_1265])).
% 7.43/2.52  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.43/2.52  
% 7.43/2.52  Inference rules
% 7.43/2.52  ----------------------
% 7.43/2.52  #Ref     : 0
% 7.43/2.52  #Sup     : 1857
% 7.43/2.52  #Fact    : 0
% 7.43/2.52  #Define  : 0
% 7.43/2.52  #Split   : 0
% 7.43/2.52  #Chain   : 0
% 7.43/2.52  #Close   : 0
% 7.43/2.52  
% 7.43/2.52  Ordering : KBO
% 7.43/2.52  
% 7.43/2.52  Simplification rules
% 7.43/2.52  ----------------------
% 7.43/2.52  #Subsume      : 504
% 7.43/2.52  #Demod        : 943
% 7.43/2.52  #Tautology    : 950
% 7.43/2.52  #SimpNegUnit  : 0
% 7.43/2.52  #BackRed      : 2
% 7.43/2.52  
% 7.43/2.52  #Partial instantiations: 0
% 7.43/2.52  #Strategies tried      : 1
% 7.43/2.52  
% 7.43/2.52  Timing (in seconds)
% 7.43/2.52  ----------------------
% 7.43/2.53  Preprocessing        : 0.31
% 7.43/2.53  Parsing              : 0.16
% 7.43/2.53  CNF conversion       : 0.02
% 7.43/2.53  Main loop            : 1.49
% 7.43/2.53  Inferencing          : 0.42
% 7.43/2.53  Reduction            : 0.81
% 7.43/2.53  Demodulation         : 0.72
% 7.43/2.53  BG Simplification    : 0.05
% 7.43/2.53  Subsumption          : 0.16
% 7.43/2.53  Abstraction          : 0.07
% 7.43/2.53  MUC search           : 0.00
% 7.43/2.53  Cooper               : 0.00
% 7.43/2.53  Total                : 1.83
% 7.43/2.53  Index Insertion      : 0.00
% 7.43/2.53  Index Deletion       : 0.00
% 7.43/2.53  Index Matching       : 0.00
% 7.43/2.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
