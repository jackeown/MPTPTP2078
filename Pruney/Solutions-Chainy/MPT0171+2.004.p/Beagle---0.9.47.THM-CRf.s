%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:29 EST 2020

% Result     : Theorem 1.54s
% Output     : CNFRefutation 1.59s
% Verified   : 
% Statistics : Number of formulae       :   18 (  18 expanded)
%              Number of leaves         :   13 (  13 expanded)
%              Depth                    :    3
%              Number of atoms          :    8 (   8 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k3_enumset1 > k2_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_tarski > #skF_1

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

tff(f_33,axiom,(
    ! [A] : k2_enumset1(A,A,A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_36,negated_conjecture,(
    ~ ! [A] : k3_enumset1(A,A,A,A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_enumset1)).

tff(c_8,plain,(
    ! [A_12] : k2_enumset1(A_12,A_12,A_12,A_12) = k1_tarski(A_12) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_6,plain,(
    ! [A_8,B_9,C_10,D_11] : k3_enumset1(A_8,A_8,B_9,C_10,D_11) = k2_enumset1(A_8,B_9,C_10,D_11) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    k3_enumset1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1') != k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_11,plain,(
    k2_enumset1('#skF_1','#skF_1','#skF_1','#skF_1') != k1_tarski('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_10])).

tff(c_13,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:37:04 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.54/1.03  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.54/1.04  
% 1.54/1.04  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.59/1.04  %$ k3_enumset1 > k2_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_tarski > #skF_1
% 1.59/1.04  
% 1.59/1.04  %Foreground sorts:
% 1.59/1.04  
% 1.59/1.04  
% 1.59/1.04  %Background operators:
% 1.59/1.04  
% 1.59/1.04  
% 1.59/1.04  %Foreground operators:
% 1.59/1.04  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.59/1.04  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.59/1.04  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.59/1.04  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.59/1.04  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.59/1.04  tff('#skF_1', type, '#skF_1': $i).
% 1.59/1.04  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.59/1.04  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.59/1.04  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.59/1.04  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.59/1.04  
% 1.59/1.05  tff(f_33, axiom, (![A]: (k2_enumset1(A, A, A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t82_enumset1)).
% 1.59/1.05  tff(f_31, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 1.59/1.05  tff(f_36, negated_conjecture, ~(![A]: (k3_enumset1(A, A, A, A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_enumset1)).
% 1.59/1.05  tff(c_8, plain, (![A_12]: (k2_enumset1(A_12, A_12, A_12, A_12)=k1_tarski(A_12))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.59/1.05  tff(c_6, plain, (![A_8, B_9, C_10, D_11]: (k3_enumset1(A_8, A_8, B_9, C_10, D_11)=k2_enumset1(A_8, B_9, C_10, D_11))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.59/1.05  tff(c_10, plain, (k3_enumset1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1')!=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.59/1.05  tff(c_11, plain, (k2_enumset1('#skF_1', '#skF_1', '#skF_1', '#skF_1')!=k1_tarski('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_10])).
% 1.59/1.05  tff(c_13, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_11])).
% 1.59/1.05  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.59/1.05  
% 1.59/1.05  Inference rules
% 1.59/1.05  ----------------------
% 1.59/1.05  #Ref     : 0
% 1.59/1.05  #Sup     : 0
% 1.59/1.05  #Fact    : 0
% 1.59/1.05  #Define  : 0
% 1.59/1.05  #Split   : 0
% 1.59/1.05  #Chain   : 0
% 1.59/1.05  #Close   : 0
% 1.59/1.05  
% 1.59/1.05  Ordering : KBO
% 1.59/1.05  
% 1.59/1.05  Simplification rules
% 1.59/1.05  ----------------------
% 1.59/1.05  #Subsume      : 4
% 1.59/1.05  #Demod        : 2
% 1.59/1.05  #Tautology    : 0
% 1.59/1.05  #SimpNegUnit  : 0
% 1.59/1.05  #BackRed      : 0
% 1.59/1.05  
% 1.59/1.05  #Partial instantiations: 0
% 1.59/1.05  #Strategies tried      : 1
% 1.59/1.05  
% 1.59/1.05  Timing (in seconds)
% 1.59/1.05  ----------------------
% 1.59/1.05  Preprocessing        : 0.27
% 1.59/1.05  Parsing              : 0.14
% 1.59/1.05  CNF conversion       : 0.01
% 1.59/1.05  Main loop            : 0.02
% 1.59/1.05  Inferencing          : 0.00
% 1.59/1.05  Reduction            : 0.01
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
