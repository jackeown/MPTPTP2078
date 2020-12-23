%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:07 EST 2020

% Result     : Theorem 2.39s
% Output     : CNFRefutation 2.39s
% Verified   : 
% Statistics : Number of formulae       :   35 (  42 expanded)
%              Number of leaves         :   20 (  24 expanded)
%              Depth                    :    7
%              Number of atoms          :   21 (  28 expanded)
%              Number of equality atoms :   20 (  27 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(f_41,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_47,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k1_tarski(A),k2_tarski(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k2_tarski(A,B),k2_tarski(C,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l53_enumset1)).

tff(f_50,negated_conjecture,(
    ~ ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(c_14,plain,(
    ! [A_15,B_16] : k2_xboole_0(k1_tarski(A_15),k1_tarski(B_16)) = k2_tarski(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_20,plain,(
    ! [A_24] : k2_tarski(A_24,A_24) = k1_tarski(A_24) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_200,plain,(
    ! [A_48,B_49,C_50] : k2_xboole_0(k1_tarski(A_48),k2_tarski(B_49,C_50)) = k1_enumset1(A_48,B_49,C_50) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_215,plain,(
    ! [A_48,A_24] : k2_xboole_0(k1_tarski(A_48),k1_tarski(A_24)) = k1_enumset1(A_48,A_24,A_24) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_200])).

tff(c_218,plain,(
    ! [A_48,A_24] : k1_enumset1(A_48,A_24,A_24) = k2_tarski(A_48,A_24) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_215])).

tff(c_328,plain,(
    ! [A_75,B_76,C_77,D_78] : k2_xboole_0(k1_enumset1(A_75,B_76,C_77),k1_tarski(D_78)) = k2_enumset1(A_75,B_76,C_77,D_78) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_511,plain,(
    ! [A_96,A_97,D_98] : k2_xboole_0(k2_tarski(A_96,A_97),k1_tarski(D_98)) = k2_enumset1(A_96,A_97,A_97,D_98) ),
    inference(superposition,[status(thm),theory(equality)],[c_218,c_328])).

tff(c_16,plain,(
    ! [A_17,B_18,C_19] : k2_xboole_0(k1_tarski(A_17),k2_tarski(B_18,C_19)) = k1_enumset1(A_17,B_18,C_19) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_238,plain,(
    ! [A_56,B_57,C_58,D_59] : k2_xboole_0(k2_tarski(A_56,B_57),k2_tarski(C_58,D_59)) = k2_enumset1(A_56,B_57,C_58,D_59) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_253,plain,(
    ! [A_24,C_58,D_59] : k2_xboole_0(k1_tarski(A_24),k2_tarski(C_58,D_59)) = k2_enumset1(A_24,A_24,C_58,D_59) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_238])).

tff(c_259,plain,(
    ! [A_24,C_58,D_59] : k2_enumset1(A_24,A_24,C_58,D_59) = k1_enumset1(A_24,C_58,D_59) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_253])).

tff(c_538,plain,(
    ! [A_97,D_98] : k2_xboole_0(k2_tarski(A_97,A_97),k1_tarski(D_98)) = k1_enumset1(A_97,A_97,D_98) ),
    inference(superposition,[status(thm),theory(equality)],[c_511,c_259])).

tff(c_580,plain,(
    ! [A_97,D_98] : k1_enumset1(A_97,A_97,D_98) = k2_tarski(A_97,D_98) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_20,c_538])).

tff(c_22,plain,(
    k1_enumset1('#skF_1','#skF_1','#skF_2') != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_593,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_580,c_22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:30:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.39/1.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.39/1.32  
% 2.39/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.39/1.32  %$ r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1
% 2.39/1.32  
% 2.39/1.32  %Foreground sorts:
% 2.39/1.32  
% 2.39/1.32  
% 2.39/1.32  %Background operators:
% 2.39/1.32  
% 2.39/1.32  
% 2.39/1.32  %Foreground operators:
% 2.39/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.39/1.32  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.39/1.32  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.39/1.32  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.39/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.39/1.32  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.39/1.32  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.39/1.32  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.39/1.32  tff('#skF_2', type, '#skF_2': $i).
% 2.39/1.32  tff('#skF_1', type, '#skF_1': $i).
% 2.39/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.39/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.39/1.32  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.39/1.32  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.39/1.32  
% 2.39/1.34  tff(f_41, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 2.39/1.34  tff(f_47, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.39/1.34  tff(f_43, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k1_tarski(A), k2_tarski(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_enumset1)).
% 2.39/1.34  tff(f_45, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_enumset1)).
% 2.39/1.34  tff(f_39, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k2_tarski(A, B), k2_tarski(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l53_enumset1)).
% 2.39/1.34  tff(f_50, negated_conjecture, ~(![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.39/1.34  tff(c_14, plain, (![A_15, B_16]: (k2_xboole_0(k1_tarski(A_15), k1_tarski(B_16))=k2_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.39/1.34  tff(c_20, plain, (![A_24]: (k2_tarski(A_24, A_24)=k1_tarski(A_24))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.39/1.34  tff(c_200, plain, (![A_48, B_49, C_50]: (k2_xboole_0(k1_tarski(A_48), k2_tarski(B_49, C_50))=k1_enumset1(A_48, B_49, C_50))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.39/1.34  tff(c_215, plain, (![A_48, A_24]: (k2_xboole_0(k1_tarski(A_48), k1_tarski(A_24))=k1_enumset1(A_48, A_24, A_24))), inference(superposition, [status(thm), theory('equality')], [c_20, c_200])).
% 2.39/1.34  tff(c_218, plain, (![A_48, A_24]: (k1_enumset1(A_48, A_24, A_24)=k2_tarski(A_48, A_24))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_215])).
% 2.39/1.34  tff(c_328, plain, (![A_75, B_76, C_77, D_78]: (k2_xboole_0(k1_enumset1(A_75, B_76, C_77), k1_tarski(D_78))=k2_enumset1(A_75, B_76, C_77, D_78))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.39/1.34  tff(c_511, plain, (![A_96, A_97, D_98]: (k2_xboole_0(k2_tarski(A_96, A_97), k1_tarski(D_98))=k2_enumset1(A_96, A_97, A_97, D_98))), inference(superposition, [status(thm), theory('equality')], [c_218, c_328])).
% 2.39/1.34  tff(c_16, plain, (![A_17, B_18, C_19]: (k2_xboole_0(k1_tarski(A_17), k2_tarski(B_18, C_19))=k1_enumset1(A_17, B_18, C_19))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.39/1.34  tff(c_238, plain, (![A_56, B_57, C_58, D_59]: (k2_xboole_0(k2_tarski(A_56, B_57), k2_tarski(C_58, D_59))=k2_enumset1(A_56, B_57, C_58, D_59))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.39/1.34  tff(c_253, plain, (![A_24, C_58, D_59]: (k2_xboole_0(k1_tarski(A_24), k2_tarski(C_58, D_59))=k2_enumset1(A_24, A_24, C_58, D_59))), inference(superposition, [status(thm), theory('equality')], [c_20, c_238])).
% 2.39/1.34  tff(c_259, plain, (![A_24, C_58, D_59]: (k2_enumset1(A_24, A_24, C_58, D_59)=k1_enumset1(A_24, C_58, D_59))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_253])).
% 2.39/1.34  tff(c_538, plain, (![A_97, D_98]: (k2_xboole_0(k2_tarski(A_97, A_97), k1_tarski(D_98))=k1_enumset1(A_97, A_97, D_98))), inference(superposition, [status(thm), theory('equality')], [c_511, c_259])).
% 2.39/1.34  tff(c_580, plain, (![A_97, D_98]: (k1_enumset1(A_97, A_97, D_98)=k2_tarski(A_97, D_98))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_20, c_538])).
% 2.39/1.34  tff(c_22, plain, (k1_enumset1('#skF_1', '#skF_1', '#skF_2')!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.39/1.34  tff(c_593, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_580, c_22])).
% 2.39/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.39/1.34  
% 2.39/1.34  Inference rules
% 2.39/1.34  ----------------------
% 2.39/1.34  #Ref     : 0
% 2.39/1.34  #Sup     : 138
% 2.39/1.34  #Fact    : 0
% 2.39/1.34  #Define  : 0
% 2.39/1.34  #Split   : 0
% 2.39/1.34  #Chain   : 0
% 2.39/1.34  #Close   : 0
% 2.39/1.34  
% 2.39/1.34  Ordering : KBO
% 2.39/1.34  
% 2.39/1.34  Simplification rules
% 2.39/1.34  ----------------------
% 2.39/1.34  #Subsume      : 0
% 2.39/1.34  #Demod        : 68
% 2.39/1.34  #Tautology    : 87
% 2.39/1.34  #SimpNegUnit  : 0
% 2.39/1.34  #BackRed      : 4
% 2.39/1.34  
% 2.39/1.34  #Partial instantiations: 0
% 2.39/1.34  #Strategies tried      : 1
% 2.39/1.34  
% 2.39/1.34  Timing (in seconds)
% 2.39/1.34  ----------------------
% 2.39/1.34  Preprocessing        : 0.30
% 2.39/1.34  Parsing              : 0.16
% 2.39/1.34  CNF conversion       : 0.02
% 2.39/1.34  Main loop            : 0.28
% 2.39/1.34  Inferencing          : 0.12
% 2.39/1.34  Reduction            : 0.10
% 2.39/1.34  Demodulation         : 0.08
% 2.39/1.34  BG Simplification    : 0.02
% 2.39/1.34  Subsumption          : 0.03
% 2.39/1.34  Abstraction          : 0.02
% 2.39/1.34  MUC search           : 0.00
% 2.39/1.34  Cooper               : 0.00
% 2.39/1.34  Total                : 0.60
% 2.39/1.34  Index Insertion      : 0.00
% 2.39/1.34  Index Deletion       : 0.00
% 2.39/1.34  Index Matching       : 0.00
% 2.39/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
