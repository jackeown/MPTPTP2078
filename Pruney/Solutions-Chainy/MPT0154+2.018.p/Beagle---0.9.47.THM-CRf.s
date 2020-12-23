%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:06 EST 2020

% Result     : Theorem 2.18s
% Output     : CNFRefutation 2.18s
% Verified   : 
% Statistics : Number of formulae       :   36 (  49 expanded)
%              Number of leaves         :   20 (  26 expanded)
%              Depth                    :    8
%              Number of atoms          :   22 (  35 expanded)
%              Number of equality atoms :   21 (  34 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(f_47,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_53,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_49,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k1_tarski(A),k2_tarski(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).

tff(f_51,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_tarski(A),k1_enumset1(B,C,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k2_tarski(A,B),k2_tarski(C,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l53_enumset1)).

tff(f_56,negated_conjecture,(
    ~ ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(c_22,plain,(
    ! [A_23,B_24] : k2_xboole_0(k1_tarski(A_23),k1_tarski(B_24)) = k2_tarski(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_28,plain,(
    ! [A_32] : k2_tarski(A_32,A_32) = k1_tarski(A_32) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_265,plain,(
    ! [A_54,B_55,C_56] : k2_xboole_0(k1_tarski(A_54),k2_tarski(B_55,C_56)) = k1_enumset1(A_54,B_55,C_56) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_274,plain,(
    ! [A_54,A_32] : k2_xboole_0(k1_tarski(A_54),k1_tarski(A_32)) = k1_enumset1(A_54,A_32,A_32) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_265])).

tff(c_277,plain,(
    ! [A_54,A_32] : k1_enumset1(A_54,A_32,A_32) = k2_tarski(A_54,A_32) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_274])).

tff(c_24,plain,(
    ! [A_25,B_26,C_27] : k2_xboole_0(k1_tarski(A_25),k2_tarski(B_26,C_27)) = k1_enumset1(A_25,B_26,C_27) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_421,plain,(
    ! [A_72,B_73,C_74,D_75] : k2_xboole_0(k1_tarski(A_72),k1_enumset1(B_73,C_74,D_75)) = k2_enumset1(A_72,B_73,C_74,D_75) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_433,plain,(
    ! [A_72,A_54,A_32] : k2_xboole_0(k1_tarski(A_72),k2_tarski(A_54,A_32)) = k2_enumset1(A_72,A_54,A_32,A_32) ),
    inference(superposition,[status(thm),theory(equality)],[c_277,c_421])).

tff(c_467,plain,(
    ! [A_78,A_79,A_80] : k2_enumset1(A_78,A_79,A_80,A_80) = k1_enumset1(A_78,A_79,A_80) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_433])).

tff(c_349,plain,(
    ! [A_62,B_63,C_64,D_65] : k2_xboole_0(k2_tarski(A_62,B_63),k2_tarski(C_64,D_65)) = k2_enumset1(A_62,B_63,C_64,D_65) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_362,plain,(
    ! [A_32,C_64,D_65] : k2_xboole_0(k1_tarski(A_32),k2_tarski(C_64,D_65)) = k2_enumset1(A_32,A_32,C_64,D_65) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_349])).

tff(c_372,plain,(
    ! [A_32,C_64,D_65] : k2_enumset1(A_32,A_32,C_64,D_65) = k1_enumset1(A_32,C_64,D_65) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_362])).

tff(c_478,plain,(
    ! [A_79,A_80] : k1_enumset1(A_79,A_80,A_80) = k1_enumset1(A_79,A_79,A_80) ),
    inference(superposition,[status(thm),theory(equality)],[c_467,c_372])).

tff(c_499,plain,(
    ! [A_79,A_80] : k1_enumset1(A_79,A_79,A_80) = k2_tarski(A_79,A_80) ),
    inference(demodulation,[status(thm),theory(equality)],[c_277,c_478])).

tff(c_30,plain,(
    k1_enumset1('#skF_1','#skF_1','#skF_2') != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_507,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_499,c_30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n022.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:14:56 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.18/1.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.18/1.24  
% 2.18/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.18/1.25  %$ k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 2.18/1.25  
% 2.18/1.25  %Foreground sorts:
% 2.18/1.25  
% 2.18/1.25  
% 2.18/1.25  %Background operators:
% 2.18/1.25  
% 2.18/1.25  
% 2.18/1.25  %Foreground operators:
% 2.18/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.18/1.25  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.18/1.25  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.18/1.25  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.18/1.25  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.18/1.25  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.18/1.25  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.18/1.25  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.18/1.25  tff('#skF_2', type, '#skF_2': $i).
% 2.18/1.25  tff('#skF_1', type, '#skF_1': $i).
% 2.18/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.18/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.18/1.25  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.18/1.25  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.18/1.25  
% 2.18/1.25  tff(f_47, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 2.18/1.25  tff(f_53, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.18/1.25  tff(f_49, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k1_tarski(A), k2_tarski(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_enumset1)).
% 2.18/1.25  tff(f_51, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_tarski(A), k1_enumset1(B, C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_enumset1)).
% 2.18/1.25  tff(f_45, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k2_tarski(A, B), k2_tarski(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l53_enumset1)).
% 2.18/1.25  tff(f_56, negated_conjecture, ~(![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.18/1.25  tff(c_22, plain, (![A_23, B_24]: (k2_xboole_0(k1_tarski(A_23), k1_tarski(B_24))=k2_tarski(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.18/1.25  tff(c_28, plain, (![A_32]: (k2_tarski(A_32, A_32)=k1_tarski(A_32))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.18/1.25  tff(c_265, plain, (![A_54, B_55, C_56]: (k2_xboole_0(k1_tarski(A_54), k2_tarski(B_55, C_56))=k1_enumset1(A_54, B_55, C_56))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.18/1.25  tff(c_274, plain, (![A_54, A_32]: (k2_xboole_0(k1_tarski(A_54), k1_tarski(A_32))=k1_enumset1(A_54, A_32, A_32))), inference(superposition, [status(thm), theory('equality')], [c_28, c_265])).
% 2.18/1.25  tff(c_277, plain, (![A_54, A_32]: (k1_enumset1(A_54, A_32, A_32)=k2_tarski(A_54, A_32))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_274])).
% 2.18/1.25  tff(c_24, plain, (![A_25, B_26, C_27]: (k2_xboole_0(k1_tarski(A_25), k2_tarski(B_26, C_27))=k1_enumset1(A_25, B_26, C_27))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.18/1.25  tff(c_421, plain, (![A_72, B_73, C_74, D_75]: (k2_xboole_0(k1_tarski(A_72), k1_enumset1(B_73, C_74, D_75))=k2_enumset1(A_72, B_73, C_74, D_75))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.18/1.25  tff(c_433, plain, (![A_72, A_54, A_32]: (k2_xboole_0(k1_tarski(A_72), k2_tarski(A_54, A_32))=k2_enumset1(A_72, A_54, A_32, A_32))), inference(superposition, [status(thm), theory('equality')], [c_277, c_421])).
% 2.18/1.25  tff(c_467, plain, (![A_78, A_79, A_80]: (k2_enumset1(A_78, A_79, A_80, A_80)=k1_enumset1(A_78, A_79, A_80))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_433])).
% 2.18/1.25  tff(c_349, plain, (![A_62, B_63, C_64, D_65]: (k2_xboole_0(k2_tarski(A_62, B_63), k2_tarski(C_64, D_65))=k2_enumset1(A_62, B_63, C_64, D_65))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.18/1.25  tff(c_362, plain, (![A_32, C_64, D_65]: (k2_xboole_0(k1_tarski(A_32), k2_tarski(C_64, D_65))=k2_enumset1(A_32, A_32, C_64, D_65))), inference(superposition, [status(thm), theory('equality')], [c_28, c_349])).
% 2.18/1.25  tff(c_372, plain, (![A_32, C_64, D_65]: (k2_enumset1(A_32, A_32, C_64, D_65)=k1_enumset1(A_32, C_64, D_65))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_362])).
% 2.18/1.25  tff(c_478, plain, (![A_79, A_80]: (k1_enumset1(A_79, A_80, A_80)=k1_enumset1(A_79, A_79, A_80))), inference(superposition, [status(thm), theory('equality')], [c_467, c_372])).
% 2.18/1.25  tff(c_499, plain, (![A_79, A_80]: (k1_enumset1(A_79, A_79, A_80)=k2_tarski(A_79, A_80))), inference(demodulation, [status(thm), theory('equality')], [c_277, c_478])).
% 2.18/1.25  tff(c_30, plain, (k1_enumset1('#skF_1', '#skF_1', '#skF_2')!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.18/1.25  tff(c_507, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_499, c_30])).
% 2.18/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.18/1.25  
% 2.18/1.25  Inference rules
% 2.18/1.25  ----------------------
% 2.18/1.25  #Ref     : 0
% 2.18/1.25  #Sup     : 110
% 2.18/1.25  #Fact    : 0
% 2.18/1.25  #Define  : 0
% 2.18/1.25  #Split   : 0
% 2.18/1.25  #Chain   : 0
% 2.18/1.26  #Close   : 0
% 2.18/1.26  
% 2.18/1.26  Ordering : KBO
% 2.18/1.26  
% 2.18/1.26  Simplification rules
% 2.18/1.26  ----------------------
% 2.18/1.26  #Subsume      : 0
% 2.18/1.26  #Demod        : 44
% 2.18/1.26  #Tautology    : 83
% 2.18/1.26  #SimpNegUnit  : 0
% 2.18/1.26  #BackRed      : 1
% 2.18/1.26  
% 2.18/1.26  #Partial instantiations: 0
% 2.18/1.26  #Strategies tried      : 1
% 2.18/1.26  
% 2.18/1.26  Timing (in seconds)
% 2.18/1.26  ----------------------
% 2.18/1.26  Preprocessing        : 0.29
% 2.18/1.26  Parsing              : 0.15
% 2.18/1.26  CNF conversion       : 0.02
% 2.18/1.26  Main loop            : 0.22
% 2.18/1.26  Inferencing          : 0.09
% 2.18/1.26  Reduction            : 0.08
% 2.18/1.26  Demodulation         : 0.06
% 2.18/1.26  BG Simplification    : 0.01
% 2.18/1.26  Subsumption          : 0.03
% 2.18/1.26  Abstraction          : 0.01
% 2.18/1.26  MUC search           : 0.00
% 2.18/1.26  Cooper               : 0.00
% 2.18/1.26  Total                : 0.53
% 2.18/1.26  Index Insertion      : 0.00
% 2.18/1.26  Index Deletion       : 0.00
% 2.18/1.26  Index Matching       : 0.00
% 2.18/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
