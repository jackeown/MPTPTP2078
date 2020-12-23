%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:18 EST 2020

% Result     : Theorem 3.17s
% Output     : CNFRefutation 3.17s
% Verified   : 
% Statistics : Number of formulae       :   42 (  49 expanded)
%              Number of leaves         :   24 (  28 expanded)
%              Depth                    :    6
%              Number of atoms          :   25 (  32 expanded)
%              Number of equality atoms :   24 (  31 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k7_enumset1 > k6_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1

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

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_45,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,D,C,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_enumset1)).

tff(f_61,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_47,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(D,C,B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(C,B,A,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l129_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,D,C,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t107_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k2_tarski(A,B),k2_tarski(C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).

tff(f_66,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(B,A),k2_tarski(C,A)) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_enumset1)).

tff(c_821,plain,(
    ! [B_118,D_119,C_120,A_121] : k2_enumset1(B_118,D_119,C_120,A_121) = k2_enumset1(A_121,B_118,C_120,D_119) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_36,plain,(
    ! [A_66,B_67,C_68] : k2_enumset1(A_66,A_66,B_67,C_68) = k1_enumset1(A_66,B_67,C_68) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1070,plain,(
    ! [A_125,D_126,C_127] : k2_enumset1(A_125,D_126,C_127,D_126) = k1_enumset1(D_126,C_127,A_125) ),
    inference(superposition,[status(thm),theory(equality)],[c_821,c_36])).

tff(c_22,plain,(
    ! [D_36,C_35,B_34,A_33] : k2_enumset1(D_36,C_35,B_34,A_33) = k2_enumset1(A_33,B_34,C_35,D_36) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1094,plain,(
    ! [D_126,C_127,A_125] : k2_enumset1(D_126,C_127,D_126,A_125) = k1_enumset1(D_126,C_127,A_125) ),
    inference(superposition,[status(thm),theory(equality)],[c_1070,c_22])).

tff(c_205,plain,(
    ! [D_92,C_93,B_94,A_95] : k2_enumset1(D_92,C_93,B_94,A_95) = k2_enumset1(A_95,B_94,C_93,D_92) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_291,plain,(
    ! [D_96,C_97,B_98] : k2_enumset1(D_96,C_97,B_98,B_98) = k1_enumset1(B_98,C_97,D_96) ),
    inference(superposition,[status(thm),theory(equality)],[c_205,c_36])).

tff(c_12,plain,(
    ! [C_14,B_13,A_12,D_15] : k2_enumset1(C_14,B_13,A_12,D_15) = k2_enumset1(A_12,B_13,C_14,D_15) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_728,plain,(
    ! [B_115,C_116,D_117] : k2_enumset1(B_115,C_116,D_117,B_115) = k1_enumset1(B_115,C_116,D_117) ),
    inference(superposition,[status(thm),theory(equality)],[c_291,c_12])).

tff(c_403,plain,(
    ! [A_103,D_104,C_105,B_106] : k2_enumset1(A_103,D_104,C_105,B_106) = k2_enumset1(A_103,B_106,C_105,D_104) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_459,plain,(
    ! [B_106,D_104,C_105] : k2_enumset1(B_106,D_104,C_105,B_106) = k1_enumset1(B_106,C_105,D_104) ),
    inference(superposition,[status(thm),theory(equality)],[c_403,c_36])).

tff(c_734,plain,(
    ! [B_115,D_117,C_116] : k1_enumset1(B_115,D_117,C_116) = k1_enumset1(B_115,C_116,D_117) ),
    inference(superposition,[status(thm),theory(equality)],[c_728,c_459])).

tff(c_14,plain,(
    ! [A_16,B_17,C_18,D_19] : k2_xboole_0(k2_tarski(A_16,B_17),k2_tarski(C_18,D_19)) = k2_enumset1(A_16,B_17,C_18,D_19) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_40,plain,(
    k2_xboole_0(k2_tarski('#skF_2','#skF_1'),k2_tarski('#skF_3','#skF_1')) != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_41,plain,(
    k2_enumset1('#skF_2','#skF_1','#skF_3','#skF_1') != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_40])).

tff(c_42,plain,(
    k2_enumset1('#skF_1','#skF_3','#skF_1','#skF_2') != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_41])).

tff(c_1000,plain,(
    k2_enumset1('#skF_1','#skF_3','#skF_1','#skF_2') != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_734,c_42])).

tff(c_1439,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1094,c_1000])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:08:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.17/1.59  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.17/1.59  
% 3.17/1.59  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.17/1.60  %$ k7_enumset1 > k6_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 3.17/1.60  
% 3.17/1.60  %Foreground sorts:
% 3.17/1.60  
% 3.17/1.60  
% 3.17/1.60  %Background operators:
% 3.17/1.60  
% 3.17/1.60  
% 3.17/1.60  %Foreground operators:
% 3.17/1.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.17/1.60  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.17/1.60  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.17/1.60  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.17/1.60  tff(k7_enumset1, type, k7_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.17/1.60  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.17/1.60  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.17/1.60  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.17/1.60  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.17/1.60  tff('#skF_2', type, '#skF_2': $i).
% 3.17/1.60  tff('#skF_3', type, '#skF_3': $i).
% 3.17/1.60  tff('#skF_1', type, '#skF_1': $i).
% 3.17/1.60  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.17/1.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.17/1.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.17/1.60  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.17/1.60  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.17/1.60  
% 3.17/1.61  tff(f_45, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, D, C, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_enumset1)).
% 3.17/1.61  tff(f_61, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 3.17/1.61  tff(f_47, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(D, C, B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_enumset1)).
% 3.17/1.61  tff(f_37, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(C, B, A, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l129_enumset1)).
% 3.17/1.61  tff(f_43, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, D, C, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t107_enumset1)).
% 3.17/1.61  tff(f_39, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k2_tarski(A, B), k2_tarski(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l53_enumset1)).
% 3.17/1.61  tff(f_66, negated_conjecture, ~(![A, B, C]: (k2_xboole_0(k2_tarski(B, A), k2_tarski(C, A)) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t137_enumset1)).
% 3.17/1.61  tff(c_821, plain, (![B_118, D_119, C_120, A_121]: (k2_enumset1(B_118, D_119, C_120, A_121)=k2_enumset1(A_121, B_118, C_120, D_119))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.17/1.61  tff(c_36, plain, (![A_66, B_67, C_68]: (k2_enumset1(A_66, A_66, B_67, C_68)=k1_enumset1(A_66, B_67, C_68))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.17/1.61  tff(c_1070, plain, (![A_125, D_126, C_127]: (k2_enumset1(A_125, D_126, C_127, D_126)=k1_enumset1(D_126, C_127, A_125))), inference(superposition, [status(thm), theory('equality')], [c_821, c_36])).
% 3.17/1.61  tff(c_22, plain, (![D_36, C_35, B_34, A_33]: (k2_enumset1(D_36, C_35, B_34, A_33)=k2_enumset1(A_33, B_34, C_35, D_36))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.17/1.61  tff(c_1094, plain, (![D_126, C_127, A_125]: (k2_enumset1(D_126, C_127, D_126, A_125)=k1_enumset1(D_126, C_127, A_125))), inference(superposition, [status(thm), theory('equality')], [c_1070, c_22])).
% 3.17/1.61  tff(c_205, plain, (![D_92, C_93, B_94, A_95]: (k2_enumset1(D_92, C_93, B_94, A_95)=k2_enumset1(A_95, B_94, C_93, D_92))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.17/1.61  tff(c_291, plain, (![D_96, C_97, B_98]: (k2_enumset1(D_96, C_97, B_98, B_98)=k1_enumset1(B_98, C_97, D_96))), inference(superposition, [status(thm), theory('equality')], [c_205, c_36])).
% 3.17/1.61  tff(c_12, plain, (![C_14, B_13, A_12, D_15]: (k2_enumset1(C_14, B_13, A_12, D_15)=k2_enumset1(A_12, B_13, C_14, D_15))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.17/1.61  tff(c_728, plain, (![B_115, C_116, D_117]: (k2_enumset1(B_115, C_116, D_117, B_115)=k1_enumset1(B_115, C_116, D_117))), inference(superposition, [status(thm), theory('equality')], [c_291, c_12])).
% 3.17/1.61  tff(c_403, plain, (![A_103, D_104, C_105, B_106]: (k2_enumset1(A_103, D_104, C_105, B_106)=k2_enumset1(A_103, B_106, C_105, D_104))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.17/1.61  tff(c_459, plain, (![B_106, D_104, C_105]: (k2_enumset1(B_106, D_104, C_105, B_106)=k1_enumset1(B_106, C_105, D_104))), inference(superposition, [status(thm), theory('equality')], [c_403, c_36])).
% 3.17/1.61  tff(c_734, plain, (![B_115, D_117, C_116]: (k1_enumset1(B_115, D_117, C_116)=k1_enumset1(B_115, C_116, D_117))), inference(superposition, [status(thm), theory('equality')], [c_728, c_459])).
% 3.17/1.61  tff(c_14, plain, (![A_16, B_17, C_18, D_19]: (k2_xboole_0(k2_tarski(A_16, B_17), k2_tarski(C_18, D_19))=k2_enumset1(A_16, B_17, C_18, D_19))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.17/1.61  tff(c_40, plain, (k2_xboole_0(k2_tarski('#skF_2', '#skF_1'), k2_tarski('#skF_3', '#skF_1'))!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.17/1.61  tff(c_41, plain, (k2_enumset1('#skF_2', '#skF_1', '#skF_3', '#skF_1')!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_40])).
% 3.17/1.61  tff(c_42, plain, (k2_enumset1('#skF_1', '#skF_3', '#skF_1', '#skF_2')!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_41])).
% 3.17/1.61  tff(c_1000, plain, (k2_enumset1('#skF_1', '#skF_3', '#skF_1', '#skF_2')!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_734, c_42])).
% 3.17/1.61  tff(c_1439, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1094, c_1000])).
% 3.17/1.61  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.17/1.61  
% 3.17/1.61  Inference rules
% 3.17/1.61  ----------------------
% 3.17/1.61  #Ref     : 0
% 3.17/1.61  #Sup     : 350
% 3.17/1.61  #Fact    : 0
% 3.17/1.61  #Define  : 0
% 3.17/1.61  #Split   : 0
% 3.17/1.61  #Chain   : 0
% 3.17/1.61  #Close   : 0
% 3.17/1.61  
% 3.17/1.61  Ordering : KBO
% 3.17/1.61  
% 3.17/1.61  Simplification rules
% 3.17/1.61  ----------------------
% 3.17/1.61  #Subsume      : 18
% 3.17/1.61  #Demod        : 161
% 3.17/1.61  #Tautology    : 195
% 3.17/1.61  #SimpNegUnit  : 0
% 3.17/1.61  #BackRed      : 2
% 3.17/1.61  
% 3.17/1.61  #Partial instantiations: 0
% 3.17/1.61  #Strategies tried      : 1
% 3.17/1.61  
% 3.17/1.61  Timing (in seconds)
% 3.17/1.61  ----------------------
% 3.17/1.61  Preprocessing        : 0.32
% 3.17/1.61  Parsing              : 0.16
% 3.17/1.61  CNF conversion       : 0.02
% 3.17/1.61  Main loop            : 0.40
% 3.17/1.61  Inferencing          : 0.14
% 3.17/1.61  Reduction            : 0.16
% 3.17/1.61  Demodulation         : 0.14
% 3.17/1.61  BG Simplification    : 0.03
% 3.17/1.61  Subsumption          : 0.05
% 3.17/1.61  Abstraction          : 0.03
% 3.17/1.61  MUC search           : 0.00
% 3.17/1.61  Cooper               : 0.00
% 3.17/1.61  Total                : 0.74
% 3.17/1.61  Index Insertion      : 0.00
% 3.17/1.61  Index Deletion       : 0.00
% 3.17/1.61  Index Matching       : 0.00
% 3.17/1.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
