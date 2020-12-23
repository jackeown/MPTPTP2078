%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:18 EST 2020

% Result     : Theorem 3.32s
% Output     : CNFRefutation 3.32s
% Verified   : 
% Statistics : Number of formulae       :   38 (  43 expanded)
%              Number of leaves         :   23 (  26 expanded)
%              Depth                    :    5
%              Number of atoms          :   22 (  27 expanded)
%              Number of equality atoms :   21 (  26 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   2 average)

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

tff(f_37,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(C,B,A,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l129_enumset1)).

tff(f_61,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_49,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(D,C,B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_enumset1)).

tff(f_47,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,D,C,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,C,B,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t104_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k2_tarski(A,B),k2_tarski(C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).

tff(f_66,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(B,A),k2_tarski(C,A)) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_enumset1)).

tff(c_12,plain,(
    ! [C_14,B_13,A_12,D_15] : k2_enumset1(C_14,B_13,A_12,D_15) = k2_enumset1(A_12,B_13,C_14,D_15) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_36,plain,(
    ! [A_62,B_63,C_64] : k2_enumset1(A_62,A_62,B_63,C_64) = k1_enumset1(A_62,B_63,C_64) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_902,plain,(
    ! [D_116,C_117,B_118,A_119] : k2_enumset1(D_116,C_117,B_118,A_119) = k2_enumset1(A_119,B_118,C_117,D_116) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1110,plain,(
    ! [C_120,B_121,A_122] : k2_enumset1(C_120,B_121,A_122,A_122) = k1_enumset1(A_122,B_121,C_120) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_902])).

tff(c_1304,plain,(
    ! [D_125,B_126,C_127] : k2_enumset1(D_125,B_126,C_127,D_125) = k1_enumset1(D_125,B_126,C_127) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_1110])).

tff(c_385,plain,(
    ! [B_98,D_99,C_100,A_101] : k2_enumset1(B_98,D_99,C_100,A_101) = k2_enumset1(A_101,B_98,C_100,D_99) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_441,plain,(
    ! [B_98,D_99,C_100] : k2_enumset1(B_98,D_99,C_100,B_98) = k1_enumset1(B_98,C_100,D_99) ),
    inference(superposition,[status(thm),theory(equality)],[c_385,c_36])).

tff(c_1330,plain,(
    ! [D_125,C_127,B_126] : k1_enumset1(D_125,C_127,B_126) = k1_enumset1(D_125,B_126,C_127) ),
    inference(superposition,[status(thm),theory(equality)],[c_1304,c_441])).

tff(c_18,plain,(
    ! [A_25,C_27,B_26,D_28] : k2_enumset1(A_25,C_27,B_26,D_28) = k2_enumset1(A_25,B_26,C_27,D_28) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_24,plain,(
    ! [D_40,C_39,B_38,A_37] : k2_enumset1(D_40,C_39,B_38,A_37) = k2_enumset1(A_37,B_38,C_39,D_40) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

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
    k1_enumset1('#skF_1','#skF_2','#skF_3') != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_18,c_24,c_41])).

tff(c_1460,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1330,c_42])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:21:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.32/1.55  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.32/1.56  
% 3.32/1.56  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.32/1.56  %$ k7_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 3.32/1.56  
% 3.32/1.56  %Foreground sorts:
% 3.32/1.56  
% 3.32/1.56  
% 3.32/1.56  %Background operators:
% 3.32/1.56  
% 3.32/1.56  
% 3.32/1.56  %Foreground operators:
% 3.32/1.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.32/1.56  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.32/1.56  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.32/1.56  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.32/1.56  tff(k7_enumset1, type, k7_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.32/1.56  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.32/1.56  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.32/1.56  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.32/1.56  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.32/1.56  tff('#skF_2', type, '#skF_2': $i).
% 3.32/1.56  tff('#skF_3', type, '#skF_3': $i).
% 3.32/1.56  tff('#skF_1', type, '#skF_1': $i).
% 3.32/1.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.32/1.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.32/1.56  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.32/1.56  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.32/1.56  
% 3.32/1.57  tff(f_37, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(C, B, A, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l129_enumset1)).
% 3.32/1.57  tff(f_61, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 3.32/1.57  tff(f_49, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(D, C, B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_enumset1)).
% 3.32/1.57  tff(f_47, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, D, C, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_enumset1)).
% 3.32/1.57  tff(f_43, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, C, B, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t104_enumset1)).
% 3.32/1.57  tff(f_39, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k2_tarski(A, B), k2_tarski(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l53_enumset1)).
% 3.32/1.57  tff(f_66, negated_conjecture, ~(![A, B, C]: (k2_xboole_0(k2_tarski(B, A), k2_tarski(C, A)) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t137_enumset1)).
% 3.32/1.57  tff(c_12, plain, (![C_14, B_13, A_12, D_15]: (k2_enumset1(C_14, B_13, A_12, D_15)=k2_enumset1(A_12, B_13, C_14, D_15))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.32/1.57  tff(c_36, plain, (![A_62, B_63, C_64]: (k2_enumset1(A_62, A_62, B_63, C_64)=k1_enumset1(A_62, B_63, C_64))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.32/1.57  tff(c_902, plain, (![D_116, C_117, B_118, A_119]: (k2_enumset1(D_116, C_117, B_118, A_119)=k2_enumset1(A_119, B_118, C_117, D_116))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.32/1.57  tff(c_1110, plain, (![C_120, B_121, A_122]: (k2_enumset1(C_120, B_121, A_122, A_122)=k1_enumset1(A_122, B_121, C_120))), inference(superposition, [status(thm), theory('equality')], [c_36, c_902])).
% 3.32/1.57  tff(c_1304, plain, (![D_125, B_126, C_127]: (k2_enumset1(D_125, B_126, C_127, D_125)=k1_enumset1(D_125, B_126, C_127))), inference(superposition, [status(thm), theory('equality')], [c_12, c_1110])).
% 3.32/1.57  tff(c_385, plain, (![B_98, D_99, C_100, A_101]: (k2_enumset1(B_98, D_99, C_100, A_101)=k2_enumset1(A_101, B_98, C_100, D_99))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.32/1.57  tff(c_441, plain, (![B_98, D_99, C_100]: (k2_enumset1(B_98, D_99, C_100, B_98)=k1_enumset1(B_98, C_100, D_99))), inference(superposition, [status(thm), theory('equality')], [c_385, c_36])).
% 3.32/1.57  tff(c_1330, plain, (![D_125, C_127, B_126]: (k1_enumset1(D_125, C_127, B_126)=k1_enumset1(D_125, B_126, C_127))), inference(superposition, [status(thm), theory('equality')], [c_1304, c_441])).
% 3.32/1.57  tff(c_18, plain, (![A_25, C_27, B_26, D_28]: (k2_enumset1(A_25, C_27, B_26, D_28)=k2_enumset1(A_25, B_26, C_27, D_28))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.32/1.57  tff(c_24, plain, (![D_40, C_39, B_38, A_37]: (k2_enumset1(D_40, C_39, B_38, A_37)=k2_enumset1(A_37, B_38, C_39, D_40))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.32/1.57  tff(c_14, plain, (![A_16, B_17, C_18, D_19]: (k2_xboole_0(k2_tarski(A_16, B_17), k2_tarski(C_18, D_19))=k2_enumset1(A_16, B_17, C_18, D_19))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.32/1.57  tff(c_40, plain, (k2_xboole_0(k2_tarski('#skF_2', '#skF_1'), k2_tarski('#skF_3', '#skF_1'))!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.32/1.57  tff(c_41, plain, (k2_enumset1('#skF_2', '#skF_1', '#skF_3', '#skF_1')!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_40])).
% 3.32/1.57  tff(c_42, plain, (k1_enumset1('#skF_1', '#skF_2', '#skF_3')!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_18, c_24, c_41])).
% 3.32/1.57  tff(c_1460, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1330, c_42])).
% 3.32/1.57  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.32/1.57  
% 3.32/1.57  Inference rules
% 3.32/1.57  ----------------------
% 3.32/1.57  #Ref     : 0
% 3.32/1.57  #Sup     : 366
% 3.32/1.57  #Fact    : 0
% 3.32/1.57  #Define  : 0
% 3.32/1.57  #Split   : 0
% 3.32/1.57  #Chain   : 0
% 3.32/1.57  #Close   : 0
% 3.32/1.57  
% 3.32/1.57  Ordering : KBO
% 3.32/1.57  
% 3.32/1.57  Simplification rules
% 3.32/1.57  ----------------------
% 3.32/1.57  #Subsume      : 11
% 3.32/1.57  #Demod        : 137
% 3.32/1.57  #Tautology    : 180
% 3.32/1.57  #SimpNegUnit  : 0
% 3.32/1.57  #BackRed      : 1
% 3.32/1.57  
% 3.32/1.57  #Partial instantiations: 0
% 3.32/1.57  #Strategies tried      : 1
% 3.32/1.57  
% 3.32/1.57  Timing (in seconds)
% 3.32/1.57  ----------------------
% 3.32/1.57  Preprocessing        : 0.34
% 3.32/1.57  Parsing              : 0.19
% 3.32/1.57  CNF conversion       : 0.02
% 3.32/1.57  Main loop            : 0.42
% 3.32/1.57  Inferencing          : 0.14
% 3.32/1.57  Reduction            : 0.18
% 3.32/1.57  Demodulation         : 0.15
% 3.32/1.57  BG Simplification    : 0.03
% 3.32/1.57  Subsumption          : 0.06
% 3.32/1.57  Abstraction          : 0.03
% 3.32/1.57  MUC search           : 0.00
% 3.32/1.57  Cooper               : 0.00
% 3.32/1.57  Total                : 0.79
% 3.32/1.57  Index Insertion      : 0.00
% 3.32/1.57  Index Deletion       : 0.00
% 3.32/1.57  Index Matching       : 0.00
% 3.32/1.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
