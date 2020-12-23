%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:31 EST 2020

% Result     : Theorem 1.55s
% Output     : CNFRefutation 1.55s
% Verified   : 
% Statistics : Number of formulae       :   20 (  20 expanded)
%              Number of leaves         :   15 (  15 expanded)
%              Depth                    :    3
%              Number of atoms          :    8 (   8 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k5_enumset1 > k4_enumset1 > k3_enumset1 > k1_enumset1 > k2_xboole_0 > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_31,axiom,(
    ! [A,B,C] : k3_enumset1(A,A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D,E] : k5_enumset1(A,A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_enumset1)).

tff(f_36,negated_conjecture,(
    ~ ! [A,B,C] : k5_enumset1(A,A,A,A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t89_enumset1)).

tff(c_6,plain,(
    ! [A_9,B_10,C_11] : k3_enumset1(A_9,A_9,A_9,B_10,C_11) = k1_enumset1(A_9,B_10,C_11) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [E_16,D_15,C_14,A_12,B_13] : k5_enumset1(A_12,A_12,A_12,B_13,C_14,D_15,E_16) = k3_enumset1(A_12,B_13,C_14,D_15,E_16) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    k5_enumset1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3') != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_11,plain,(
    k3_enumset1('#skF_1','#skF_1','#skF_1','#skF_2','#skF_3') != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_10])).

tff(c_13,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:34:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.55/1.03  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.55/1.03  
% 1.55/1.03  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.55/1.04  %$ k5_enumset1 > k4_enumset1 > k3_enumset1 > k1_enumset1 > k2_xboole_0 > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 1.55/1.04  
% 1.55/1.04  %Foreground sorts:
% 1.55/1.04  
% 1.55/1.04  
% 1.55/1.04  %Background operators:
% 1.55/1.04  
% 1.55/1.04  
% 1.55/1.04  %Foreground operators:
% 1.55/1.04  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.55/1.04  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.55/1.04  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.55/1.04  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.55/1.04  tff('#skF_2', type, '#skF_2': $i).
% 1.55/1.04  tff('#skF_3', type, '#skF_3': $i).
% 1.55/1.04  tff('#skF_1', type, '#skF_1': $i).
% 1.55/1.04  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.55/1.04  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.55/1.04  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.55/1.04  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.55/1.04  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.55/1.04  
% 1.55/1.04  tff(f_31, axiom, (![A, B, C]: (k3_enumset1(A, A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_enumset1)).
% 1.55/1.04  tff(f_33, axiom, (![A, B, C, D, E]: (k5_enumset1(A, A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_enumset1)).
% 1.55/1.04  tff(f_36, negated_conjecture, ~(![A, B, C]: (k5_enumset1(A, A, A, A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t89_enumset1)).
% 1.55/1.04  tff(c_6, plain, (![A_9, B_10, C_11]: (k3_enumset1(A_9, A_9, A_9, B_10, C_11)=k1_enumset1(A_9, B_10, C_11))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.55/1.04  tff(c_8, plain, (![E_16, D_15, C_14, A_12, B_13]: (k5_enumset1(A_12, A_12, A_12, B_13, C_14, D_15, E_16)=k3_enumset1(A_12, B_13, C_14, D_15, E_16))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.55/1.04  tff(c_10, plain, (k5_enumset1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3')!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.55/1.04  tff(c_11, plain, (k3_enumset1('#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3')!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_10])).
% 1.55/1.04  tff(c_13, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_11])).
% 1.55/1.04  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.55/1.04  
% 1.55/1.04  Inference rules
% 1.55/1.04  ----------------------
% 1.55/1.04  #Ref     : 0
% 1.55/1.04  #Sup     : 0
% 1.55/1.05  #Fact    : 0
% 1.55/1.05  #Define  : 0
% 1.55/1.05  #Split   : 0
% 1.55/1.05  #Chain   : 0
% 1.55/1.05  #Close   : 0
% 1.55/1.05  
% 1.55/1.05  Ordering : KBO
% 1.55/1.05  
% 1.55/1.05  Simplification rules
% 1.55/1.05  ----------------------
% 1.55/1.05  #Subsume      : 4
% 1.55/1.05  #Demod        : 2
% 1.55/1.05  #Tautology    : 0
% 1.55/1.05  #SimpNegUnit  : 0
% 1.55/1.05  #BackRed      : 0
% 1.55/1.05  
% 1.55/1.05  #Partial instantiations: 0
% 1.55/1.05  #Strategies tried      : 1
% 1.55/1.05  
% 1.55/1.05  Timing (in seconds)
% 1.55/1.05  ----------------------
% 1.55/1.05  Preprocessing        : 0.27
% 1.55/1.05  Parsing              : 0.14
% 1.55/1.05  CNF conversion       : 0.02
% 1.55/1.05  Main loop            : 0.02
% 1.55/1.05  Inferencing          : 0.00
% 1.55/1.05  Reduction            : 0.01
% 1.55/1.05  Demodulation         : 0.01
% 1.55/1.05  BG Simplification    : 0.01
% 1.55/1.05  Subsumption          : 0.00
% 1.55/1.05  Abstraction          : 0.00
% 1.55/1.05  MUC search           : 0.00
% 1.55/1.05  Cooper               : 0.00
% 1.55/1.05  Total                : 0.31
% 1.55/1.05  Index Insertion      : 0.00
% 1.55/1.05  Index Deletion       : 0.00
% 1.55/1.05  Index Matching       : 0.00
% 1.55/1.05  BG Taut test         : 0.00
%------------------------------------------------------------------------------
