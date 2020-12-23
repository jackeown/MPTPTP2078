%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:52 EST 2020

% Result     : Theorem 3.27s
% Output     : CNFRefutation 3.27s
% Verified   : 
% Statistics : Number of formulae       :   34 (  67 expanded)
%              Number of leaves         :   20 (  34 expanded)
%              Depth                    :    5
%              Number of atoms          :   20 (  53 expanded)
%              Number of equality atoms :   19 (  52 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_29,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,B,D,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,D,C,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_enumset1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_33,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_tarski(A),k1_enumset1(B,C,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_48,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,A,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_enumset1)).

tff(c_4,plain,(
    ! [A_3,B_4,D_6,C_5] : k2_enumset1(A_3,B_4,D_6,C_5) = k2_enumset1(A_3,B_4,C_5,D_6) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_249,plain,(
    ! [A_54,D_55,C_56,B_57] : k2_enumset1(A_54,D_55,C_56,B_57) = k2_enumset1(A_54,B_57,C_56,D_55) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_319,plain,(
    ! [A_3,C_5,D_6,B_4] : k2_enumset1(A_3,C_5,D_6,B_4) = k2_enumset1(A_3,B_4,C_5,D_6) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_249])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_519,plain,(
    ! [A_72,B_73,C_74,D_75] : k2_xboole_0(k1_tarski(A_72),k1_enumset1(B_73,C_74,D_75)) = k2_enumset1(A_72,B_73,C_74,D_75) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1768,plain,(
    ! [B_122,C_123,D_124,A_125] : k2_xboole_0(k1_enumset1(B_122,C_123,D_124),k1_tarski(A_125)) = k2_enumset1(A_125,B_122,C_123,D_124) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_519])).

tff(c_10,plain,(
    ! [A_15,B_16,C_17,D_18] : k2_xboole_0(k1_enumset1(A_15,B_16,C_17),k1_tarski(D_18)) = k2_enumset1(A_15,B_16,C_17,D_18) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1774,plain,(
    ! [B_122,C_123,D_124,A_125] : k2_enumset1(B_122,C_123,D_124,A_125) = k2_enumset1(A_125,B_122,C_123,D_124) ),
    inference(superposition,[status(thm),theory(equality)],[c_1768,c_10])).

tff(c_6,plain,(
    ! [A_7,D_10,C_9,B_8] : k2_enumset1(A_7,D_10,C_9,B_8) = k2_enumset1(A_7,B_8,C_9,D_10) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_22,plain,(
    k2_enumset1('#skF_2','#skF_1','#skF_3','#skF_4') != k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_23,plain,(
    k2_enumset1('#skF_2','#skF_4','#skF_3','#skF_1') != k2_enumset1('#skF_1','#skF_4','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_6,c_22])).

tff(c_24,plain,(
    k2_enumset1('#skF_2','#skF_4','#skF_1','#skF_3') != k2_enumset1('#skF_1','#skF_4','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_23])).

tff(c_1824,plain,(
    k2_enumset1('#skF_4','#skF_3','#skF_2','#skF_1') != k2_enumset1('#skF_4','#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1774,c_1774,c_1774,c_1774,c_24])).

tff(c_1827,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_319,c_4,c_1824])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:13:17 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.27/1.48  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.27/1.48  
% 3.27/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.27/1.48  %$ k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.27/1.48  
% 3.27/1.48  %Foreground sorts:
% 3.27/1.48  
% 3.27/1.48  
% 3.27/1.48  %Background operators:
% 3.27/1.48  
% 3.27/1.48  
% 3.27/1.48  %Foreground operators:
% 3.27/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.27/1.48  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.27/1.48  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.27/1.48  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.27/1.48  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.27/1.48  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.27/1.48  tff('#skF_2', type, '#skF_2': $i).
% 3.27/1.48  tff('#skF_3', type, '#skF_3': $i).
% 3.27/1.48  tff('#skF_1', type, '#skF_1': $i).
% 3.27/1.48  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.27/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.27/1.48  tff('#skF_4', type, '#skF_4': $i).
% 3.27/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.27/1.48  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.27/1.48  
% 3.27/1.49  tff(f_29, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, B, D, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t103_enumset1)).
% 3.27/1.49  tff(f_31, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, D, C, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t107_enumset1)).
% 3.27/1.49  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.27/1.49  tff(f_33, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_tarski(A), k1_enumset1(B, C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_enumset1)).
% 3.27/1.49  tff(f_35, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_enumset1)).
% 3.27/1.49  tff(f_48, negated_conjecture, ~(![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, A, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t108_enumset1)).
% 3.27/1.49  tff(c_4, plain, (![A_3, B_4, D_6, C_5]: (k2_enumset1(A_3, B_4, D_6, C_5)=k2_enumset1(A_3, B_4, C_5, D_6))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.27/1.49  tff(c_249, plain, (![A_54, D_55, C_56, B_57]: (k2_enumset1(A_54, D_55, C_56, B_57)=k2_enumset1(A_54, B_57, C_56, D_55))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.27/1.49  tff(c_319, plain, (![A_3, C_5, D_6, B_4]: (k2_enumset1(A_3, C_5, D_6, B_4)=k2_enumset1(A_3, B_4, C_5, D_6))), inference(superposition, [status(thm), theory('equality')], [c_4, c_249])).
% 3.27/1.49  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.27/1.49  tff(c_519, plain, (![A_72, B_73, C_74, D_75]: (k2_xboole_0(k1_tarski(A_72), k1_enumset1(B_73, C_74, D_75))=k2_enumset1(A_72, B_73, C_74, D_75))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.27/1.49  tff(c_1768, plain, (![B_122, C_123, D_124, A_125]: (k2_xboole_0(k1_enumset1(B_122, C_123, D_124), k1_tarski(A_125))=k2_enumset1(A_125, B_122, C_123, D_124))), inference(superposition, [status(thm), theory('equality')], [c_2, c_519])).
% 3.27/1.49  tff(c_10, plain, (![A_15, B_16, C_17, D_18]: (k2_xboole_0(k1_enumset1(A_15, B_16, C_17), k1_tarski(D_18))=k2_enumset1(A_15, B_16, C_17, D_18))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.27/1.49  tff(c_1774, plain, (![B_122, C_123, D_124, A_125]: (k2_enumset1(B_122, C_123, D_124, A_125)=k2_enumset1(A_125, B_122, C_123, D_124))), inference(superposition, [status(thm), theory('equality')], [c_1768, c_10])).
% 3.27/1.49  tff(c_6, plain, (![A_7, D_10, C_9, B_8]: (k2_enumset1(A_7, D_10, C_9, B_8)=k2_enumset1(A_7, B_8, C_9, D_10))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.27/1.49  tff(c_22, plain, (k2_enumset1('#skF_2', '#skF_1', '#skF_3', '#skF_4')!=k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.27/1.49  tff(c_23, plain, (k2_enumset1('#skF_2', '#skF_4', '#skF_3', '#skF_1')!=k2_enumset1('#skF_1', '#skF_4', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_6, c_22])).
% 3.27/1.49  tff(c_24, plain, (k2_enumset1('#skF_2', '#skF_4', '#skF_1', '#skF_3')!=k2_enumset1('#skF_1', '#skF_4', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_23])).
% 3.27/1.49  tff(c_1824, plain, (k2_enumset1('#skF_4', '#skF_3', '#skF_2', '#skF_1')!=k2_enumset1('#skF_4', '#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1774, c_1774, c_1774, c_1774, c_24])).
% 3.27/1.49  tff(c_1827, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4, c_319, c_4, c_1824])).
% 3.27/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.27/1.49  
% 3.27/1.49  Inference rules
% 3.27/1.49  ----------------------
% 3.27/1.49  #Ref     : 0
% 3.27/1.49  #Sup     : 438
% 3.27/1.49  #Fact    : 0
% 3.27/1.49  #Define  : 0
% 3.27/1.49  #Split   : 0
% 3.27/1.49  #Chain   : 0
% 3.27/1.49  #Close   : 0
% 3.27/1.49  
% 3.27/1.49  Ordering : KBO
% 3.27/1.49  
% 3.27/1.49  Simplification rules
% 3.27/1.49  ----------------------
% 3.27/1.49  #Subsume      : 75
% 3.27/1.49  #Demod        : 292
% 3.27/1.49  #Tautology    : 306
% 3.27/1.49  #SimpNegUnit  : 0
% 3.27/1.49  #BackRed      : 1
% 3.27/1.49  
% 3.27/1.49  #Partial instantiations: 0
% 3.27/1.49  #Strategies tried      : 1
% 3.27/1.49  
% 3.27/1.49  Timing (in seconds)
% 3.27/1.49  ----------------------
% 3.27/1.50  Preprocessing        : 0.28
% 3.27/1.50  Parsing              : 0.15
% 3.27/1.50  CNF conversion       : 0.02
% 3.27/1.50  Main loop            : 0.46
% 3.27/1.50  Inferencing          : 0.16
% 3.27/1.50  Reduction            : 0.20
% 3.27/1.50  Demodulation         : 0.18
% 3.27/1.50  BG Simplification    : 0.02
% 3.27/1.50  Subsumption          : 0.06
% 3.27/1.50  Abstraction          : 0.02
% 3.27/1.50  MUC search           : 0.00
% 3.27/1.50  Cooper               : 0.00
% 3.27/1.50  Total                : 0.76
% 3.27/1.50  Index Insertion      : 0.00
% 3.27/1.50  Index Deletion       : 0.00
% 3.27/1.50  Index Matching       : 0.00
% 3.27/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
