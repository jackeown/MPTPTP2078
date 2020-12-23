%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:40 EST 2020

% Result     : Theorem 1.56s
% Output     : CNFRefutation 1.56s
% Verified   : 
% Statistics : Number of formulae       :   21 (  21 expanded)
%              Number of leaves         :   14 (  14 expanded)
%              Depth                    :    4
%              Number of atoms          :   11 (  11 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > #nlpp > k1_tarski > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_31,axiom,(
    ! [A] : k1_enumset1(A,A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D] : k6_enumset1(A,A,A,A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_enumset1)).

tff(f_36,negated_conjecture,(
    ~ ! [A] : k6_enumset1(A,A,A,A,A,A,A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_enumset1)).

tff(c_6,plain,(
    ! [A_12] : k1_enumset1(A_12,A_12,A_12) = k1_tarski(A_12) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4,plain,(
    ! [A_9,B_10,C_11] : k2_enumset1(A_9,A_9,B_10,C_11) = k1_enumset1(A_9,B_10,C_11) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_8,plain,(
    ! [A_13,B_14,C_15,D_16] : k6_enumset1(A_13,A_13,A_13,A_13,A_13,B_14,C_15,D_16) = k2_enumset1(A_13,B_14,C_15,D_16) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    k6_enumset1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_1') != k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_11,plain,(
    k2_enumset1('#skF_1','#skF_1','#skF_1','#skF_1') != k1_tarski('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_10])).

tff(c_12,plain,(
    k1_enumset1('#skF_1','#skF_1','#skF_1') != k1_tarski('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_11])).

tff(c_14,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 18:31:25 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.56/1.01  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.56/1.02  
% 1.56/1.02  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.56/1.02  %$ k6_enumset1 > k5_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > #nlpp > k1_tarski > #skF_1
% 1.56/1.02  
% 1.56/1.02  %Foreground sorts:
% 1.56/1.02  
% 1.56/1.02  
% 1.56/1.02  %Background operators:
% 1.56/1.02  
% 1.56/1.02  
% 1.56/1.02  %Foreground operators:
% 1.56/1.02  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.56/1.02  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.56/1.02  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.56/1.02  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.56/1.02  tff('#skF_1', type, '#skF_1': $i).
% 1.56/1.02  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 1.56/1.02  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.56/1.02  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.56/1.02  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.56/1.02  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.56/1.02  
% 1.56/1.03  tff(f_31, axiom, (![A]: (k1_enumset1(A, A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_enumset1)).
% 1.56/1.03  tff(f_29, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 1.56/1.03  tff(f_33, axiom, (![A, B, C, D]: (k6_enumset1(A, A, A, A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_enumset1)).
% 1.56/1.03  tff(f_36, negated_conjecture, ~(![A]: (k6_enumset1(A, A, A, A, A, A, A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t96_enumset1)).
% 1.56/1.03  tff(c_6, plain, (![A_12]: (k1_enumset1(A_12, A_12, A_12)=k1_tarski(A_12))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.56/1.03  tff(c_4, plain, (![A_9, B_10, C_11]: (k2_enumset1(A_9, A_9, B_10, C_11)=k1_enumset1(A_9, B_10, C_11))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.56/1.03  tff(c_8, plain, (![A_13, B_14, C_15, D_16]: (k6_enumset1(A_13, A_13, A_13, A_13, A_13, B_14, C_15, D_16)=k2_enumset1(A_13, B_14, C_15, D_16))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.56/1.03  tff(c_10, plain, (k6_enumset1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1')!=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.56/1.03  tff(c_11, plain, (k2_enumset1('#skF_1', '#skF_1', '#skF_1', '#skF_1')!=k1_tarski('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_10])).
% 1.56/1.03  tff(c_12, plain, (k1_enumset1('#skF_1', '#skF_1', '#skF_1')!=k1_tarski('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_11])).
% 1.56/1.03  tff(c_14, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_12])).
% 1.56/1.03  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.56/1.03  
% 1.56/1.03  Inference rules
% 1.56/1.03  ----------------------
% 1.56/1.03  #Ref     : 0
% 1.56/1.03  #Sup     : 0
% 1.56/1.03  #Fact    : 0
% 1.56/1.03  #Define  : 0
% 1.56/1.03  #Split   : 0
% 1.56/1.03  #Chain   : 0
% 1.56/1.03  #Close   : 0
% 1.56/1.03  
% 1.56/1.03  Ordering : KBO
% 1.56/1.03  
% 1.56/1.03  Simplification rules
% 1.56/1.03  ----------------------
% 1.56/1.03  #Subsume      : 4
% 1.56/1.03  #Demod        : 3
% 1.56/1.03  #Tautology    : 0
% 1.56/1.03  #SimpNegUnit  : 0
% 1.56/1.03  #BackRed      : 0
% 1.56/1.03  
% 1.56/1.03  #Partial instantiations: 0
% 1.56/1.03  #Strategies tried      : 1
% 1.56/1.03  
% 1.56/1.03  Timing (in seconds)
% 1.56/1.03  ----------------------
% 1.56/1.03  Preprocessing        : 0.26
% 1.56/1.03  Parsing              : 0.14
% 1.56/1.03  CNF conversion       : 0.01
% 1.56/1.03  Main loop            : 0.02
% 1.56/1.03  Inferencing          : 0.00
% 1.56/1.03  Reduction            : 0.01
% 1.56/1.03  Demodulation         : 0.01
% 1.56/1.03  BG Simplification    : 0.01
% 1.56/1.03  Subsumption          : 0.00
% 1.56/1.03  Abstraction          : 0.00
% 1.56/1.03  MUC search           : 0.00
% 1.56/1.03  Cooper               : 0.00
% 1.56/1.03  Total                : 0.31
% 1.56/1.03  Index Insertion      : 0.00
% 1.56/1.03  Index Deletion       : 0.00
% 1.56/1.03  Index Matching       : 0.00
% 1.56/1.03  BG Taut test         : 0.00
%------------------------------------------------------------------------------
