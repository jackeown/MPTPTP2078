%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:39 EST 2020

% Result     : Theorem 1.64s
% Output     : CNFRefutation 1.64s
% Verified   : 
% Statistics : Number of formulae       :   28 (  28 expanded)
%              Number of leaves         :   19 (  19 expanded)
%              Depth                    :    5
%              Number of atoms          :   14 (  14 expanded)
%              Number of equality atoms :   13 (  13 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_35,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_tarski(A),k1_enumset1(B,C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k1_tarski(A),k2_tarski(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).

tff(f_31,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_38,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k2_tarski(A,B),k2_tarski(C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_enumset1)).

tff(c_10,plain,(
    ! [A_11,B_12,C_13,D_14] : k2_xboole_0(k1_tarski(A_11),k1_enumset1(B_12,C_13,D_14)) = k2_enumset1(A_11,B_12,C_13,D_14) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_8,plain,(
    ! [A_8,B_9,C_10] : k2_xboole_0(k1_tarski(A_8),k2_tarski(B_9,C_10)) = k1_enumset1(A_8,B_9,C_10) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_6,plain,(
    ! [A_6,B_7] : k2_xboole_0(k1_tarski(A_6),k1_tarski(B_7)) = k2_tarski(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_40,plain,(
    ! [A_22,B_23,C_24] : k2_xboole_0(k2_xboole_0(A_22,B_23),C_24) = k2_xboole_0(A_22,k2_xboole_0(B_23,C_24)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_75,plain,(
    ! [A_29,B_30,C_31] : k2_xboole_0(k1_tarski(A_29),k2_xboole_0(k1_tarski(B_30),C_31)) = k2_xboole_0(k2_tarski(A_29,B_30),C_31) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_40])).

tff(c_96,plain,(
    ! [A_29,A_8,B_9,C_10] : k2_xboole_0(k2_tarski(A_29,A_8),k2_tarski(B_9,C_10)) = k2_xboole_0(k1_tarski(A_29),k1_enumset1(A_8,B_9,C_10)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_75])).

tff(c_103,plain,(
    ! [A_29,A_8,B_9,C_10] : k2_xboole_0(k2_tarski(A_29,A_8),k2_tarski(B_9,C_10)) = k2_enumset1(A_29,A_8,B_9,C_10) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_96])).

tff(c_12,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_2'),k2_tarski('#skF_3','#skF_4')) != k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_119,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 21:19:45 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.64/1.12  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.64/1.12  
% 1.64/1.12  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.64/1.12  %$ k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.64/1.12  
% 1.64/1.12  %Foreground sorts:
% 1.64/1.12  
% 1.64/1.12  
% 1.64/1.12  %Background operators:
% 1.64/1.12  
% 1.64/1.12  
% 1.64/1.12  %Foreground operators:
% 1.64/1.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.64/1.12  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.64/1.12  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.64/1.12  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.64/1.12  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.64/1.12  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.64/1.12  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.64/1.12  tff('#skF_2', type, '#skF_2': $i).
% 1.64/1.12  tff('#skF_3', type, '#skF_3': $i).
% 1.64/1.12  tff('#skF_1', type, '#skF_1': $i).
% 1.64/1.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.64/1.12  tff('#skF_4', type, '#skF_4': $i).
% 1.64/1.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.64/1.12  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.64/1.12  
% 1.64/1.13  tff(f_35, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_tarski(A), k1_enumset1(B, C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_enumset1)).
% 1.64/1.13  tff(f_33, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k1_tarski(A), k2_tarski(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_enumset1)).
% 1.64/1.13  tff(f_31, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 1.64/1.13  tff(f_27, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 1.64/1.13  tff(f_38, negated_conjecture, ~(![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k2_tarski(A, B), k2_tarski(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_enumset1)).
% 1.64/1.13  tff(c_10, plain, (![A_11, B_12, C_13, D_14]: (k2_xboole_0(k1_tarski(A_11), k1_enumset1(B_12, C_13, D_14))=k2_enumset1(A_11, B_12, C_13, D_14))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.64/1.13  tff(c_8, plain, (![A_8, B_9, C_10]: (k2_xboole_0(k1_tarski(A_8), k2_tarski(B_9, C_10))=k1_enumset1(A_8, B_9, C_10))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.64/1.13  tff(c_6, plain, (![A_6, B_7]: (k2_xboole_0(k1_tarski(A_6), k1_tarski(B_7))=k2_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.64/1.13  tff(c_40, plain, (![A_22, B_23, C_24]: (k2_xboole_0(k2_xboole_0(A_22, B_23), C_24)=k2_xboole_0(A_22, k2_xboole_0(B_23, C_24)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.64/1.13  tff(c_75, plain, (![A_29, B_30, C_31]: (k2_xboole_0(k1_tarski(A_29), k2_xboole_0(k1_tarski(B_30), C_31))=k2_xboole_0(k2_tarski(A_29, B_30), C_31))), inference(superposition, [status(thm), theory('equality')], [c_6, c_40])).
% 1.64/1.13  tff(c_96, plain, (![A_29, A_8, B_9, C_10]: (k2_xboole_0(k2_tarski(A_29, A_8), k2_tarski(B_9, C_10))=k2_xboole_0(k1_tarski(A_29), k1_enumset1(A_8, B_9, C_10)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_75])).
% 1.64/1.13  tff(c_103, plain, (![A_29, A_8, B_9, C_10]: (k2_xboole_0(k2_tarski(A_29, A_8), k2_tarski(B_9, C_10))=k2_enumset1(A_29, A_8, B_9, C_10))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_96])).
% 1.64/1.13  tff(c_12, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), k2_tarski('#skF_3', '#skF_4'))!=k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.64/1.13  tff(c_119, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_103, c_12])).
% 1.64/1.13  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.64/1.13  
% 1.64/1.13  Inference rules
% 1.64/1.13  ----------------------
% 1.64/1.13  #Ref     : 0
% 1.64/1.13  #Sup     : 26
% 1.64/1.13  #Fact    : 0
% 1.64/1.13  #Define  : 0
% 1.64/1.13  #Split   : 0
% 1.64/1.13  #Chain   : 0
% 1.64/1.13  #Close   : 0
% 1.64/1.13  
% 1.64/1.13  Ordering : KBO
% 1.64/1.13  
% 1.64/1.13  Simplification rules
% 1.64/1.13  ----------------------
% 1.64/1.13  #Subsume      : 0
% 1.64/1.13  #Demod        : 12
% 1.64/1.13  #Tautology    : 17
% 1.64/1.13  #SimpNegUnit  : 0
% 1.64/1.13  #BackRed      : 1
% 1.64/1.13  
% 1.64/1.13  #Partial instantiations: 0
% 1.64/1.13  #Strategies tried      : 1
% 1.64/1.13  
% 1.64/1.13  Timing (in seconds)
% 1.64/1.13  ----------------------
% 1.64/1.13  Preprocessing        : 0.25
% 1.64/1.13  Parsing              : 0.14
% 1.64/1.13  CNF conversion       : 0.01
% 1.64/1.13  Main loop            : 0.12
% 1.64/1.13  Inferencing          : 0.06
% 1.64/1.13  Reduction            : 0.04
% 1.64/1.13  Demodulation         : 0.03
% 1.64/1.13  BG Simplification    : 0.01
% 1.64/1.13  Subsumption          : 0.01
% 1.64/1.13  Abstraction          : 0.01
% 1.64/1.13  MUC search           : 0.00
% 1.64/1.13  Cooper               : 0.00
% 1.64/1.13  Total                : 0.39
% 1.64/1.13  Index Insertion      : 0.00
% 1.64/1.13  Index Deletion       : 0.00
% 1.64/1.13  Index Matching       : 0.00
% 1.64/1.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
