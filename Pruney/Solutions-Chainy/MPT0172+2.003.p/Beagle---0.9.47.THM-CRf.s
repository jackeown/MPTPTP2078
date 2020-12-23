%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:30 EST 2020

% Result     : Theorem 1.59s
% Output     : CNFRefutation 1.59s
% Verified   : 
% Statistics : Number of formulae       :   25 (  25 expanded)
%              Number of leaves         :   18 (  18 expanded)
%              Depth                    :    4
%              Number of atoms          :   11 (  11 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_31,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D] : k4_enumset1(A,A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_enumset1)).

tff(f_40,negated_conjecture,(
    ~ ! [A,B] : k4_enumset1(A,A,A,A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_enumset1)).

tff(c_6,plain,(
    ! [A_9,B_10] : k1_enumset1(A_9,A_9,B_10) = k2_tarski(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [A_11,B_12,C_13] : k2_enumset1(A_11,A_11,B_12,C_13) = k1_enumset1(A_11,B_12,C_13) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_12,plain,(
    ! [A_15,B_16,C_17,D_18] : k4_enumset1(A_15,A_15,A_15,B_16,C_17,D_18) = k2_enumset1(A_15,B_16,C_17,D_18) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_14,plain,(
    k4_enumset1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_2') != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_15,plain,(
    k2_enumset1('#skF_1','#skF_1','#skF_1','#skF_2') != k2_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_14])).

tff(c_16,plain,(
    k1_enumset1('#skF_1','#skF_1','#skF_2') != k2_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_15])).

tff(c_18,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.33  % Computer   : n016.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % DateTime   : Tue Dec  1 14:03:49 EST 2020
% 0.11/0.34  % CPUTime    : 
% 0.11/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.59/1.03  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.59/1.03  
% 1.59/1.03  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.59/1.03  %$ k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1
% 1.59/1.03  
% 1.59/1.03  %Foreground sorts:
% 1.59/1.03  
% 1.59/1.03  
% 1.59/1.03  %Background operators:
% 1.59/1.03  
% 1.59/1.03  
% 1.59/1.03  %Foreground operators:
% 1.59/1.03  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.59/1.03  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.59/1.03  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.59/1.03  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.59/1.03  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.59/1.03  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.59/1.03  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.59/1.03  tff('#skF_2', type, '#skF_2': $i).
% 1.59/1.03  tff('#skF_1', type, '#skF_1': $i).
% 1.59/1.03  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.59/1.03  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.59/1.03  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.59/1.03  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.59/1.03  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.59/1.03  
% 1.59/1.04  tff(f_31, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 1.59/1.04  tff(f_33, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 1.59/1.04  tff(f_37, axiom, (![A, B, C, D]: (k4_enumset1(A, A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_enumset1)).
% 1.59/1.04  tff(f_40, negated_conjecture, ~(![A, B]: (k4_enumset1(A, A, A, A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_enumset1)).
% 1.59/1.04  tff(c_6, plain, (![A_9, B_10]: (k1_enumset1(A_9, A_9, B_10)=k2_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.59/1.04  tff(c_8, plain, (![A_11, B_12, C_13]: (k2_enumset1(A_11, A_11, B_12, C_13)=k1_enumset1(A_11, B_12, C_13))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.59/1.04  tff(c_12, plain, (![A_15, B_16, C_17, D_18]: (k4_enumset1(A_15, A_15, A_15, B_16, C_17, D_18)=k2_enumset1(A_15, B_16, C_17, D_18))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.59/1.04  tff(c_14, plain, (k4_enumset1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2')!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.59/1.04  tff(c_15, plain, (k2_enumset1('#skF_1', '#skF_1', '#skF_1', '#skF_2')!=k2_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_14])).
% 1.59/1.04  tff(c_16, plain, (k1_enumset1('#skF_1', '#skF_1', '#skF_2')!=k2_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_15])).
% 1.59/1.04  tff(c_18, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_16])).
% 1.59/1.04  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.59/1.04  
% 1.59/1.04  Inference rules
% 1.59/1.04  ----------------------
% 1.59/1.04  #Ref     : 0
% 1.59/1.04  #Sup     : 0
% 1.59/1.04  #Fact    : 0
% 1.59/1.04  #Define  : 0
% 1.59/1.04  #Split   : 0
% 1.59/1.04  #Chain   : 0
% 1.59/1.04  #Close   : 0
% 1.59/1.04  
% 1.59/1.04  Ordering : KBO
% 1.59/1.04  
% 1.59/1.04  Simplification rules
% 1.59/1.04  ----------------------
% 1.59/1.04  #Subsume      : 6
% 1.59/1.04  #Demod        : 3
% 1.59/1.04  #Tautology    : 0
% 1.59/1.04  #SimpNegUnit  : 0
% 1.59/1.04  #BackRed      : 0
% 1.59/1.04  
% 1.59/1.04  #Partial instantiations: 0
% 1.59/1.04  #Strategies tried      : 1
% 1.59/1.04  
% 1.59/1.04  Timing (in seconds)
% 1.59/1.04  ----------------------
% 1.59/1.05  Preprocessing        : 0.27
% 1.59/1.05  Parsing              : 0.15
% 1.59/1.05  CNF conversion       : 0.01
% 1.59/1.05  Main loop            : 0.02
% 1.59/1.05  Inferencing          : 0.00
% 1.59/1.05  Reduction            : 0.02
% 1.59/1.05  Demodulation         : 0.01
% 1.59/1.05  BG Simplification    : 0.01
% 1.59/1.05  Subsumption          : 0.00
% 1.59/1.05  Abstraction          : 0.00
% 1.59/1.05  MUC search           : 0.00
% 1.59/1.05  Cooper               : 0.00
% 1.59/1.05  Total                : 0.32
% 1.59/1.05  Index Insertion      : 0.00
% 1.59/1.05  Index Deletion       : 0.00
% 1.59/1.05  Index Matching       : 0.00
% 1.59/1.05  BG Taut test         : 0.00
%------------------------------------------------------------------------------
