%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:23 EST 2020

% Result     : Theorem 1.65s
% Output     : CNFRefutation 1.65s
% Verified   : 
% Statistics : Number of formulae       :   24 (  28 expanded)
%              Number of leaves         :   18 (  20 expanded)
%              Depth                    :    3
%              Number of atoms          :   10 (  14 expanded)
%              Number of equality atoms :    9 (  13 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_41,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,D,A,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k2_tarski(A,B),k2_tarski(C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).

tff(f_46,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(B,A),k2_tarski(C,A)) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_enumset1)).

tff(c_16,plain,(
    ! [A_23,B_24,C_25] : k2_enumset1(A_23,A_23,B_24,C_25) = k1_enumset1(A_23,B_24,C_25) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_10,plain,(
    ! [B_14,D_16,A_13,C_15] : k2_enumset1(B_14,D_16,A_13,C_15) = k2_enumset1(A_13,B_14,C_15,D_16) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_6,plain,(
    ! [A_5,B_6,C_7,D_8] : k2_xboole_0(k2_tarski(A_5,B_6),k2_tarski(C_7,D_8)) = k2_enumset1(A_5,B_6,C_7,D_8) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_20,plain,(
    k2_xboole_0(k2_tarski('#skF_2','#skF_1'),k2_tarski('#skF_3','#skF_1')) != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_21,plain,(
    k2_enumset1('#skF_2','#skF_1','#skF_3','#skF_1') != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_20])).

tff(c_23,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_10,c_10,c_10,c_21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:37:35 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.65/1.11  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.65/1.11  
% 1.65/1.11  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.65/1.11  %$ k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > #skF_2 > #skF_3 > #skF_1
% 1.65/1.11  
% 1.65/1.11  %Foreground sorts:
% 1.65/1.11  
% 1.65/1.11  
% 1.65/1.11  %Background operators:
% 1.65/1.11  
% 1.65/1.11  
% 1.65/1.11  %Foreground operators:
% 1.65/1.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.65/1.11  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.65/1.11  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.65/1.11  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.65/1.11  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.65/1.11  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.65/1.11  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.65/1.11  tff('#skF_2', type, '#skF_2': $i).
% 1.65/1.11  tff('#skF_3', type, '#skF_3': $i).
% 1.65/1.11  tff('#skF_1', type, '#skF_1': $i).
% 1.65/1.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.65/1.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.65/1.11  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.65/1.11  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.65/1.11  
% 1.65/1.12  tff(f_41, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 1.65/1.12  tff(f_35, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, D, A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t112_enumset1)).
% 1.65/1.12  tff(f_31, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k2_tarski(A, B), k2_tarski(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l53_enumset1)).
% 1.65/1.12  tff(f_46, negated_conjecture, ~(![A, B, C]: (k2_xboole_0(k2_tarski(B, A), k2_tarski(C, A)) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t137_enumset1)).
% 1.65/1.12  tff(c_16, plain, (![A_23, B_24, C_25]: (k2_enumset1(A_23, A_23, B_24, C_25)=k1_enumset1(A_23, B_24, C_25))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.65/1.12  tff(c_10, plain, (![B_14, D_16, A_13, C_15]: (k2_enumset1(B_14, D_16, A_13, C_15)=k2_enumset1(A_13, B_14, C_15, D_16))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.65/1.12  tff(c_6, plain, (![A_5, B_6, C_7, D_8]: (k2_xboole_0(k2_tarski(A_5, B_6), k2_tarski(C_7, D_8))=k2_enumset1(A_5, B_6, C_7, D_8))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.65/1.12  tff(c_20, plain, (k2_xboole_0(k2_tarski('#skF_2', '#skF_1'), k2_tarski('#skF_3', '#skF_1'))!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.65/1.12  tff(c_21, plain, (k2_enumset1('#skF_2', '#skF_1', '#skF_3', '#skF_1')!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_20])).
% 1.65/1.12  tff(c_23, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_10, c_10, c_10, c_21])).
% 1.65/1.12  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.65/1.12  
% 1.65/1.12  Inference rules
% 1.65/1.12  ----------------------
% 1.65/1.12  #Ref     : 0
% 1.65/1.12  #Sup     : 0
% 1.65/1.12  #Fact    : 0
% 1.65/1.12  #Define  : 0
% 1.65/1.12  #Split   : 0
% 1.65/1.12  #Chain   : 0
% 1.65/1.12  #Close   : 0
% 1.65/1.12  
% 1.65/1.12  Ordering : KBO
% 1.65/1.12  
% 1.65/1.12  Simplification rules
% 1.65/1.12  ----------------------
% 1.65/1.12  #Subsume      : 9
% 1.65/1.12  #Demod        : 5
% 1.65/1.12  #Tautology    : 0
% 1.65/1.12  #SimpNegUnit  : 0
% 1.65/1.12  #BackRed      : 0
% 1.65/1.12  
% 1.65/1.12  #Partial instantiations: 0
% 1.65/1.12  #Strategies tried      : 1
% 1.65/1.12  
% 1.65/1.12  Timing (in seconds)
% 1.65/1.12  ----------------------
% 1.65/1.12  Preprocessing        : 0.30
% 1.65/1.12  Parsing              : 0.16
% 1.65/1.12  CNF conversion       : 0.02
% 1.65/1.12  Main loop            : 0.04
% 1.65/1.12  Inferencing          : 0.00
% 1.65/1.12  Reduction            : 0.02
% 1.65/1.12  Demodulation         : 0.02
% 1.65/1.12  BG Simplification    : 0.01
% 1.65/1.12  Subsumption          : 0.01
% 1.65/1.12  Abstraction          : 0.01
% 1.65/1.12  MUC search           : 0.00
% 1.65/1.12  Cooper               : 0.00
% 1.65/1.12  Total                : 0.36
% 1.65/1.12  Index Insertion      : 0.00
% 1.65/1.12  Index Deletion       : 0.00
% 1.65/1.12  Index Matching       : 0.00
% 1.65/1.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------
