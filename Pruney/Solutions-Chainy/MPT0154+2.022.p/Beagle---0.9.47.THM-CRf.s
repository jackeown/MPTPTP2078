%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:07 EST 2020

% Result     : Theorem 5.31s
% Output     : CNFRefutation 5.31s
% Verified   : 
% Statistics : Number of formulae       :   38 (  45 expanded)
%              Number of leaves         :   22 (  26 expanded)
%              Depth                    :    7
%              Number of atoms          :   22 (  29 expanded)
%              Number of equality atoms :   21 (  28 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(f_51,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k1_tarski(A),k2_tarski(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).

tff(f_49,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_57,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_53,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_tarski(A),k1_enumset1(B,C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).

tff(f_47,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k2_tarski(A,B),k2_tarski(C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).

tff(f_60,negated_conjecture,(
    ~ ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(c_24,plain,(
    ! [A_25,B_26,C_27] : k2_xboole_0(k1_tarski(A_25),k2_tarski(B_26,C_27)) = k1_enumset1(A_25,B_26,C_27) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_22,plain,(
    ! [A_23,B_24] : k2_xboole_0(k1_tarski(A_23),k1_tarski(B_24)) = k2_tarski(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_30,plain,(
    ! [A_37] : k2_tarski(A_37,A_37) = k1_tarski(A_37) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_400,plain,(
    ! [A_67,B_68,C_69] : k2_xboole_0(k1_tarski(A_67),k2_tarski(B_68,C_69)) = k1_enumset1(A_67,B_68,C_69) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_415,plain,(
    ! [A_67,A_37] : k2_xboole_0(k1_tarski(A_67),k1_tarski(A_37)) = k1_enumset1(A_67,A_37,A_37) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_400])).

tff(c_418,plain,(
    ! [A_67,A_37] : k1_enumset1(A_67,A_37,A_37) = k2_tarski(A_67,A_37) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_415])).

tff(c_780,plain,(
    ! [A_89,B_90,C_91,D_92] : k2_xboole_0(k1_tarski(A_89),k1_enumset1(B_90,C_91,D_92)) = k2_enumset1(A_89,B_90,C_91,D_92) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_795,plain,(
    ! [A_89,A_67,A_37] : k2_xboole_0(k1_tarski(A_89),k2_tarski(A_67,A_37)) = k2_enumset1(A_89,A_67,A_37,A_37) ),
    inference(superposition,[status(thm),theory(equality)],[c_418,c_780])).

tff(c_7628,plain,(
    ! [A_269,A_270,A_271] : k2_enumset1(A_269,A_270,A_271,A_271) = k1_enumset1(A_269,A_270,A_271) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_795])).

tff(c_651,plain,(
    ! [A_83,B_84,C_85,D_86] : k2_xboole_0(k2_tarski(A_83,B_84),k2_tarski(C_85,D_86)) = k2_enumset1(A_83,B_84,C_85,D_86) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2526,plain,(
    ! [A_161,B_162,A_163] : k2_xboole_0(k2_tarski(A_161,B_162),k1_tarski(A_163)) = k2_enumset1(A_161,B_162,A_163,A_163) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_651])).

tff(c_2578,plain,(
    ! [A_37,A_163] : k2_xboole_0(k1_tarski(A_37),k1_tarski(A_163)) = k2_enumset1(A_37,A_37,A_163,A_163) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_2526])).

tff(c_2589,plain,(
    ! [A_37,A_163] : k2_enumset1(A_37,A_37,A_163,A_163) = k2_tarski(A_37,A_163) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_2578])).

tff(c_7639,plain,(
    ! [A_270,A_271] : k1_enumset1(A_270,A_270,A_271) = k2_tarski(A_270,A_271) ),
    inference(superposition,[status(thm),theory(equality)],[c_7628,c_2589])).

tff(c_32,plain,(
    k1_enumset1('#skF_1','#skF_1','#skF_2') != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_7686,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7639,c_32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:50:35 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.31/2.15  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.31/2.15  
% 5.31/2.15  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.31/2.15  %$ r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 5.31/2.15  
% 5.31/2.15  %Foreground sorts:
% 5.31/2.15  
% 5.31/2.15  
% 5.31/2.15  %Background operators:
% 5.31/2.15  
% 5.31/2.15  
% 5.31/2.15  %Foreground operators:
% 5.31/2.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.31/2.15  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.31/2.15  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.31/2.15  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.31/2.15  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 5.31/2.15  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.31/2.15  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.31/2.15  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.31/2.15  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.31/2.15  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.31/2.15  tff('#skF_2', type, '#skF_2': $i).
% 5.31/2.15  tff('#skF_1', type, '#skF_1': $i).
% 5.31/2.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.31/2.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.31/2.15  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.31/2.15  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.31/2.15  
% 5.31/2.16  tff(f_51, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k1_tarski(A), k2_tarski(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_enumset1)).
% 5.31/2.16  tff(f_49, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 5.31/2.16  tff(f_57, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 5.31/2.16  tff(f_53, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_tarski(A), k1_enumset1(B, C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_enumset1)).
% 5.31/2.16  tff(f_47, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k2_tarski(A, B), k2_tarski(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l53_enumset1)).
% 5.31/2.16  tff(f_60, negated_conjecture, ~(![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 5.31/2.16  tff(c_24, plain, (![A_25, B_26, C_27]: (k2_xboole_0(k1_tarski(A_25), k2_tarski(B_26, C_27))=k1_enumset1(A_25, B_26, C_27))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.31/2.16  tff(c_22, plain, (![A_23, B_24]: (k2_xboole_0(k1_tarski(A_23), k1_tarski(B_24))=k2_tarski(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.31/2.16  tff(c_30, plain, (![A_37]: (k2_tarski(A_37, A_37)=k1_tarski(A_37))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.31/2.16  tff(c_400, plain, (![A_67, B_68, C_69]: (k2_xboole_0(k1_tarski(A_67), k2_tarski(B_68, C_69))=k1_enumset1(A_67, B_68, C_69))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.31/2.16  tff(c_415, plain, (![A_67, A_37]: (k2_xboole_0(k1_tarski(A_67), k1_tarski(A_37))=k1_enumset1(A_67, A_37, A_37))), inference(superposition, [status(thm), theory('equality')], [c_30, c_400])).
% 5.31/2.16  tff(c_418, plain, (![A_67, A_37]: (k1_enumset1(A_67, A_37, A_37)=k2_tarski(A_67, A_37))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_415])).
% 5.31/2.16  tff(c_780, plain, (![A_89, B_90, C_91, D_92]: (k2_xboole_0(k1_tarski(A_89), k1_enumset1(B_90, C_91, D_92))=k2_enumset1(A_89, B_90, C_91, D_92))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.31/2.16  tff(c_795, plain, (![A_89, A_67, A_37]: (k2_xboole_0(k1_tarski(A_89), k2_tarski(A_67, A_37))=k2_enumset1(A_89, A_67, A_37, A_37))), inference(superposition, [status(thm), theory('equality')], [c_418, c_780])).
% 5.31/2.16  tff(c_7628, plain, (![A_269, A_270, A_271]: (k2_enumset1(A_269, A_270, A_271, A_271)=k1_enumset1(A_269, A_270, A_271))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_795])).
% 5.31/2.16  tff(c_651, plain, (![A_83, B_84, C_85, D_86]: (k2_xboole_0(k2_tarski(A_83, B_84), k2_tarski(C_85, D_86))=k2_enumset1(A_83, B_84, C_85, D_86))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.31/2.16  tff(c_2526, plain, (![A_161, B_162, A_163]: (k2_xboole_0(k2_tarski(A_161, B_162), k1_tarski(A_163))=k2_enumset1(A_161, B_162, A_163, A_163))), inference(superposition, [status(thm), theory('equality')], [c_30, c_651])).
% 5.31/2.16  tff(c_2578, plain, (![A_37, A_163]: (k2_xboole_0(k1_tarski(A_37), k1_tarski(A_163))=k2_enumset1(A_37, A_37, A_163, A_163))), inference(superposition, [status(thm), theory('equality')], [c_30, c_2526])).
% 5.31/2.16  tff(c_2589, plain, (![A_37, A_163]: (k2_enumset1(A_37, A_37, A_163, A_163)=k2_tarski(A_37, A_163))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_2578])).
% 5.31/2.16  tff(c_7639, plain, (![A_270, A_271]: (k1_enumset1(A_270, A_270, A_271)=k2_tarski(A_270, A_271))), inference(superposition, [status(thm), theory('equality')], [c_7628, c_2589])).
% 5.31/2.16  tff(c_32, plain, (k1_enumset1('#skF_1', '#skF_1', '#skF_2')!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.31/2.16  tff(c_7686, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7639, c_32])).
% 5.31/2.16  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.31/2.16  
% 5.31/2.16  Inference rules
% 5.31/2.16  ----------------------
% 5.31/2.16  #Ref     : 0
% 5.31/2.16  #Sup     : 1885
% 5.31/2.16  #Fact    : 0
% 5.31/2.16  #Define  : 0
% 5.31/2.16  #Split   : 0
% 5.31/2.16  #Chain   : 0
% 5.31/2.16  #Close   : 0
% 5.31/2.16  
% 5.31/2.16  Ordering : KBO
% 5.31/2.16  
% 5.31/2.16  Simplification rules
% 5.31/2.16  ----------------------
% 5.31/2.16  #Subsume      : 7
% 5.31/2.16  #Demod        : 1822
% 5.31/2.16  #Tautology    : 1264
% 5.31/2.16  #SimpNegUnit  : 0
% 5.31/2.16  #BackRed      : 16
% 5.31/2.16  
% 5.31/2.16  #Partial instantiations: 0
% 5.31/2.16  #Strategies tried      : 1
% 5.31/2.16  
% 5.31/2.16  Timing (in seconds)
% 5.31/2.16  ----------------------
% 5.31/2.17  Preprocessing        : 0.30
% 5.31/2.17  Parsing              : 0.16
% 5.31/2.17  CNF conversion       : 0.02
% 5.31/2.17  Main loop            : 1.11
% 5.31/2.17  Inferencing          : 0.36
% 5.31/2.17  Reduction            : 0.50
% 5.31/2.17  Demodulation         : 0.42
% 5.31/2.17  BG Simplification    : 0.04
% 5.31/2.17  Subsumption          : 0.15
% 5.31/2.17  Abstraction          : 0.06
% 5.31/2.17  MUC search           : 0.00
% 5.31/2.17  Cooper               : 0.00
% 5.31/2.17  Total                : 1.44
% 5.31/2.17  Index Insertion      : 0.00
% 5.31/2.17  Index Deletion       : 0.00
% 5.31/2.17  Index Matching       : 0.00
% 5.31/2.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
