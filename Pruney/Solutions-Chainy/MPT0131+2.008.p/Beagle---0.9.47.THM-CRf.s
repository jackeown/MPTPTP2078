%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:41 EST 2020

% Result     : Theorem 1.65s
% Output     : CNFRefutation 1.65s
% Verified   : 
% Statistics : Number of formulae       :   30 (  30 expanded)
%              Number of leaves         :   21 (  21 expanded)
%              Depth                    :    5
%              Number of atoms          :   14 (  14 expanded)
%              Number of equality atoms :   13 (  13 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_31,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_enumset1(A,B,C),k2_tarski(D,E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l57_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k2_tarski(A,B),k2_tarski(C,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k1_tarski(A),k2_tarski(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_40,negated_conjecture,(
    ~ ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_tarski(A),k2_enumset1(B,C,D,E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_enumset1)).

tff(c_6,plain,(
    ! [B_7,D_9,C_8,E_10,A_6] : k2_xboole_0(k1_enumset1(A_6,B_7,C_8),k2_tarski(D_9,E_10)) = k3_enumset1(A_6,B_7,C_8,D_9,E_10) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12,plain,(
    ! [A_16,B_17,C_18,D_19] : k2_xboole_0(k2_tarski(A_16,B_17),k2_tarski(C_18,D_19)) = k2_enumset1(A_16,B_17,C_18,D_19) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_10,plain,(
    ! [A_13,B_14,C_15] : k2_xboole_0(k1_tarski(A_13),k2_tarski(B_14,C_15)) = k1_enumset1(A_13,B_14,C_15) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_42,plain,(
    ! [A_27,B_28,C_29] : k2_xboole_0(k2_xboole_0(A_27,B_28),C_29) = k2_xboole_0(A_27,k2_xboole_0(B_28,C_29)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_143,plain,(
    ! [A_49,B_50,C_51,C_52] : k2_xboole_0(k1_tarski(A_49),k2_xboole_0(k2_tarski(B_50,C_51),C_52)) = k2_xboole_0(k1_enumset1(A_49,B_50,C_51),C_52) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_42])).

tff(c_161,plain,(
    ! [C_18,B_17,A_16,D_19,A_49] : k2_xboole_0(k1_enumset1(A_49,A_16,B_17),k2_tarski(C_18,D_19)) = k2_xboole_0(k1_tarski(A_49),k2_enumset1(A_16,B_17,C_18,D_19)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_143])).

tff(c_166,plain,(
    ! [C_18,B_17,A_16,D_19,A_49] : k2_xboole_0(k1_tarski(A_49),k2_enumset1(A_16,B_17,C_18,D_19)) = k3_enumset1(A_49,A_16,B_17,C_18,D_19) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_161])).

tff(c_14,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k2_enumset1('#skF_2','#skF_3','#skF_4','#skF_5')) != k3_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_181,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_166,c_14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:56:31 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.65/1.15  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.65/1.15  
% 1.65/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.65/1.15  %$ k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.65/1.15  
% 1.65/1.15  %Foreground sorts:
% 1.65/1.15  
% 1.65/1.15  
% 1.65/1.15  %Background operators:
% 1.65/1.15  
% 1.65/1.15  
% 1.65/1.15  %Foreground operators:
% 1.65/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.65/1.15  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.65/1.15  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.65/1.15  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.65/1.15  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.65/1.15  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.65/1.15  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.65/1.15  tff('#skF_5', type, '#skF_5': $i).
% 1.65/1.15  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.65/1.15  tff('#skF_2', type, '#skF_2': $i).
% 1.65/1.15  tff('#skF_3', type, '#skF_3': $i).
% 1.65/1.15  tff('#skF_1', type, '#skF_1': $i).
% 1.65/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.65/1.15  tff('#skF_4', type, '#skF_4': $i).
% 1.65/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.65/1.15  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.65/1.15  
% 1.65/1.16  tff(f_31, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_enumset1(A, B, C), k2_tarski(D, E)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l57_enumset1)).
% 1.65/1.16  tff(f_37, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k2_tarski(A, B), k2_tarski(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_enumset1)).
% 1.65/1.16  tff(f_35, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k1_tarski(A), k2_tarski(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_enumset1)).
% 1.65/1.16  tff(f_27, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_1)).
% 1.65/1.16  tff(f_40, negated_conjecture, ~(![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_tarski(A), k2_enumset1(B, C, D, E)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_enumset1)).
% 1.65/1.16  tff(c_6, plain, (![B_7, D_9, C_8, E_10, A_6]: (k2_xboole_0(k1_enumset1(A_6, B_7, C_8), k2_tarski(D_9, E_10))=k3_enumset1(A_6, B_7, C_8, D_9, E_10))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.65/1.16  tff(c_12, plain, (![A_16, B_17, C_18, D_19]: (k2_xboole_0(k2_tarski(A_16, B_17), k2_tarski(C_18, D_19))=k2_enumset1(A_16, B_17, C_18, D_19))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.65/1.16  tff(c_10, plain, (![A_13, B_14, C_15]: (k2_xboole_0(k1_tarski(A_13), k2_tarski(B_14, C_15))=k1_enumset1(A_13, B_14, C_15))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.65/1.16  tff(c_42, plain, (![A_27, B_28, C_29]: (k2_xboole_0(k2_xboole_0(A_27, B_28), C_29)=k2_xboole_0(A_27, k2_xboole_0(B_28, C_29)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.65/1.16  tff(c_143, plain, (![A_49, B_50, C_51, C_52]: (k2_xboole_0(k1_tarski(A_49), k2_xboole_0(k2_tarski(B_50, C_51), C_52))=k2_xboole_0(k1_enumset1(A_49, B_50, C_51), C_52))), inference(superposition, [status(thm), theory('equality')], [c_10, c_42])).
% 1.65/1.16  tff(c_161, plain, (![C_18, B_17, A_16, D_19, A_49]: (k2_xboole_0(k1_enumset1(A_49, A_16, B_17), k2_tarski(C_18, D_19))=k2_xboole_0(k1_tarski(A_49), k2_enumset1(A_16, B_17, C_18, D_19)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_143])).
% 1.65/1.16  tff(c_166, plain, (![C_18, B_17, A_16, D_19, A_49]: (k2_xboole_0(k1_tarski(A_49), k2_enumset1(A_16, B_17, C_18, D_19))=k3_enumset1(A_49, A_16, B_17, C_18, D_19))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_161])).
% 1.65/1.16  tff(c_14, plain, (k2_xboole_0(k1_tarski('#skF_1'), k2_enumset1('#skF_2', '#skF_3', '#skF_4', '#skF_5'))!=k3_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.65/1.16  tff(c_181, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_166, c_14])).
% 1.65/1.16  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.65/1.16  
% 1.65/1.16  Inference rules
% 1.65/1.16  ----------------------
% 1.65/1.16  #Ref     : 0
% 1.65/1.16  #Sup     : 41
% 1.65/1.16  #Fact    : 0
% 1.65/1.16  #Define  : 0
% 1.65/1.16  #Split   : 0
% 1.65/1.16  #Chain   : 0
% 1.65/1.16  #Close   : 0
% 1.65/1.16  
% 1.65/1.16  Ordering : KBO
% 1.65/1.16  
% 1.65/1.16  Simplification rules
% 1.65/1.16  ----------------------
% 1.65/1.16  #Subsume      : 0
% 1.65/1.16  #Demod        : 17
% 1.65/1.16  #Tautology    : 26
% 1.65/1.16  #SimpNegUnit  : 0
% 1.65/1.16  #BackRed      : 1
% 1.65/1.16  
% 1.65/1.16  #Partial instantiations: 0
% 1.65/1.16  #Strategies tried      : 1
% 1.65/1.16  
% 1.65/1.16  Timing (in seconds)
% 1.65/1.16  ----------------------
% 1.65/1.16  Preprocessing        : 0.25
% 1.65/1.17  Parsing              : 0.13
% 1.65/1.17  CNF conversion       : 0.02
% 1.65/1.17  Main loop            : 0.15
% 1.65/1.17  Inferencing          : 0.07
% 1.65/1.17  Reduction            : 0.05
% 1.65/1.17  Demodulation         : 0.04
% 1.65/1.17  BG Simplification    : 0.01
% 1.65/1.17  Subsumption          : 0.02
% 1.65/1.17  Abstraction          : 0.01
% 1.65/1.17  MUC search           : 0.00
% 1.65/1.17  Cooper               : 0.00
% 1.65/1.17  Total                : 0.42
% 1.65/1.17  Index Insertion      : 0.00
% 1.65/1.17  Index Deletion       : 0.00
% 1.65/1.17  Index Matching       : 0.00
% 1.65/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
