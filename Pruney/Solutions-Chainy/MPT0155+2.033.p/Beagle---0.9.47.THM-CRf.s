%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:13 EST 2020

% Result     : Theorem 1.67s
% Output     : CNFRefutation 1.67s
% Verified   : 
% Statistics : Number of formulae       :   24 (  25 expanded)
%              Number of leaves         :   15 (  16 expanded)
%              Depth                    :    5
%              Number of atoms          :   13 (  14 expanded)
%              Number of equality atoms :   12 (  13 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_29,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k1_tarski(A),k2_tarski(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,k2_xboole_0(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_1)).

tff(f_31,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_tarski(A),k1_enumset1(B,C,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).

tff(f_36,negated_conjecture,(
    ~ ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(c_4,plain,(
    ! [A_3,B_4,C_5] : k2_xboole_0(k1_tarski(A_3),k2_tarski(B_4,C_5)) = k1_enumset1(A_3,B_4,C_5) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_37,plain,(
    ! [A_14,B_15,C_16] : k2_xboole_0(k1_tarski(A_14),k2_tarski(B_15,C_16)) = k1_enumset1(A_14,B_15,C_16) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2,plain,(
    ! [A_1,B_2] : k2_xboole_0(A_1,k2_xboole_0(A_1,B_2)) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_43,plain,(
    ! [A_14,B_15,C_16] : k2_xboole_0(k1_tarski(A_14),k1_enumset1(A_14,B_15,C_16)) = k2_xboole_0(k1_tarski(A_14),k2_tarski(B_15,C_16)) ),
    inference(superposition,[status(thm),theory(equality)],[c_37,c_2])).

tff(c_89,plain,(
    ! [A_23,B_24,C_25] : k2_xboole_0(k1_tarski(A_23),k1_enumset1(A_23,B_24,C_25)) = k1_enumset1(A_23,B_24,C_25) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_43])).

tff(c_6,plain,(
    ! [A_6,B_7,C_8,D_9] : k2_xboole_0(k1_tarski(A_6),k1_enumset1(B_7,C_8,D_9)) = k2_enumset1(A_6,B_7,C_8,D_9) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_95,plain,(
    ! [A_23,B_24,C_25] : k2_enumset1(A_23,A_23,B_24,C_25) = k1_enumset1(A_23,B_24,C_25) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_6])).

tff(c_10,plain,(
    k2_enumset1('#skF_1','#skF_1','#skF_2','#skF_3') != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_114,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:01:30 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.67/1.10  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.67/1.10  
% 1.67/1.10  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.67/1.10  %$ k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 1.67/1.10  
% 1.67/1.10  %Foreground sorts:
% 1.67/1.10  
% 1.67/1.10  
% 1.67/1.10  %Background operators:
% 1.67/1.10  
% 1.67/1.10  
% 1.67/1.10  %Foreground operators:
% 1.67/1.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.67/1.10  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.67/1.10  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.67/1.10  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.67/1.10  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.67/1.10  tff('#skF_2', type, '#skF_2': $i).
% 1.67/1.10  tff('#skF_3', type, '#skF_3': $i).
% 1.67/1.10  tff('#skF_1', type, '#skF_1': $i).
% 1.67/1.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.67/1.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.67/1.10  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.67/1.10  
% 1.67/1.11  tff(f_29, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k1_tarski(A), k2_tarski(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_enumset1)).
% 1.67/1.11  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, k2_xboole_0(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_xboole_1)).
% 1.67/1.11  tff(f_31, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_tarski(A), k1_enumset1(B, C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_enumset1)).
% 1.67/1.11  tff(f_36, negated_conjecture, ~(![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 1.67/1.11  tff(c_4, plain, (![A_3, B_4, C_5]: (k2_xboole_0(k1_tarski(A_3), k2_tarski(B_4, C_5))=k1_enumset1(A_3, B_4, C_5))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.67/1.11  tff(c_37, plain, (![A_14, B_15, C_16]: (k2_xboole_0(k1_tarski(A_14), k2_tarski(B_15, C_16))=k1_enumset1(A_14, B_15, C_16))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.67/1.11  tff(c_2, plain, (![A_1, B_2]: (k2_xboole_0(A_1, k2_xboole_0(A_1, B_2))=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.67/1.11  tff(c_43, plain, (![A_14, B_15, C_16]: (k2_xboole_0(k1_tarski(A_14), k1_enumset1(A_14, B_15, C_16))=k2_xboole_0(k1_tarski(A_14), k2_tarski(B_15, C_16)))), inference(superposition, [status(thm), theory('equality')], [c_37, c_2])).
% 1.67/1.11  tff(c_89, plain, (![A_23, B_24, C_25]: (k2_xboole_0(k1_tarski(A_23), k1_enumset1(A_23, B_24, C_25))=k1_enumset1(A_23, B_24, C_25))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_43])).
% 1.67/1.11  tff(c_6, plain, (![A_6, B_7, C_8, D_9]: (k2_xboole_0(k1_tarski(A_6), k1_enumset1(B_7, C_8, D_9))=k2_enumset1(A_6, B_7, C_8, D_9))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.67/1.11  tff(c_95, plain, (![A_23, B_24, C_25]: (k2_enumset1(A_23, A_23, B_24, C_25)=k1_enumset1(A_23, B_24, C_25))), inference(superposition, [status(thm), theory('equality')], [c_89, c_6])).
% 1.67/1.11  tff(c_10, plain, (k2_enumset1('#skF_1', '#skF_1', '#skF_2', '#skF_3')!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.67/1.11  tff(c_114, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_95, c_10])).
% 1.67/1.11  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.67/1.11  
% 1.67/1.11  Inference rules
% 1.67/1.11  ----------------------
% 1.67/1.11  #Ref     : 0
% 1.67/1.11  #Sup     : 25
% 1.67/1.11  #Fact    : 0
% 1.67/1.11  #Define  : 0
% 1.67/1.11  #Split   : 0
% 1.67/1.11  #Chain   : 0
% 1.67/1.11  #Close   : 0
% 1.67/1.11  
% 1.67/1.11  Ordering : KBO
% 1.67/1.11  
% 1.67/1.11  Simplification rules
% 1.67/1.11  ----------------------
% 1.67/1.11  #Subsume      : 0
% 1.67/1.11  #Demod        : 9
% 1.67/1.11  #Tautology    : 17
% 1.67/1.11  #SimpNegUnit  : 0
% 1.67/1.11  #BackRed      : 1
% 1.67/1.11  
% 1.67/1.11  #Partial instantiations: 0
% 1.67/1.11  #Strategies tried      : 1
% 1.67/1.11  
% 1.67/1.11  Timing (in seconds)
% 1.67/1.11  ----------------------
% 1.67/1.11  Preprocessing        : 0.26
% 1.67/1.11  Parsing              : 0.14
% 1.67/1.11  CNF conversion       : 0.01
% 1.67/1.11  Main loop            : 0.09
% 1.67/1.11  Inferencing          : 0.04
% 1.67/1.11  Reduction            : 0.03
% 1.67/1.11  Demodulation         : 0.02
% 1.67/1.11  BG Simplification    : 0.01
% 1.67/1.11  Subsumption          : 0.01
% 1.67/1.11  Abstraction          : 0.01
% 1.67/1.11  MUC search           : 0.00
% 1.67/1.11  Cooper               : 0.00
% 1.67/1.11  Total                : 0.37
% 1.67/1.11  Index Insertion      : 0.00
% 1.67/1.11  Index Deletion       : 0.00
% 1.67/1.11  Index Matching       : 0.00
% 1.67/1.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------
