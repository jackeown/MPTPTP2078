%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:28 EST 2020

% Result     : Theorem 1.43s
% Output     : CNFRefutation 1.58s
% Verified   : 
% Statistics : Number of formulae       :   19 (  19 expanded)
%              Number of leaves         :   14 (  14 expanded)
%              Depth                    :    3
%              Number of atoms          :    8 (   8 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k4_enumset1 > k3_enumset1 > k1_enumset1 > k2_xboole_0 > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1

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

tff(f_33,axiom,(
    ! [A,B,C] : k3_enumset1(A,A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_36,negated_conjecture,(
    ~ ! [A,B,C] : k4_enumset1(A,A,A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_enumset1)).

tff(c_8,plain,(
    ! [A_13,B_14,C_15] : k3_enumset1(A_13,A_13,A_13,B_14,C_15) = k1_enumset1(A_13,B_14,C_15) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_4,plain,(
    ! [D_10,A_7,B_8,E_11,C_9] : k4_enumset1(A_7,A_7,B_8,C_9,D_10,E_11) = k3_enumset1(A_7,B_8,C_9,D_10,E_11) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_10,plain,(
    k4_enumset1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3') != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_11,plain,(
    k3_enumset1('#skF_1','#skF_1','#skF_1','#skF_2','#skF_3') != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_10])).

tff(c_13,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.32  % Computer   : n008.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 13:53:45 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.43/1.01  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.43/1.01  
% 1.43/1.01  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.58/1.01  %$ k4_enumset1 > k3_enumset1 > k1_enumset1 > k2_xboole_0 > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 1.58/1.01  
% 1.58/1.01  %Foreground sorts:
% 1.58/1.01  
% 1.58/1.01  
% 1.58/1.01  %Background operators:
% 1.58/1.01  
% 1.58/1.01  
% 1.58/1.01  %Foreground operators:
% 1.58/1.01  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.58/1.01  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.58/1.01  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.58/1.01  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.58/1.01  tff('#skF_2', type, '#skF_2': $i).
% 1.58/1.01  tff('#skF_3', type, '#skF_3': $i).
% 1.58/1.01  tff('#skF_1', type, '#skF_1': $i).
% 1.58/1.01  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.58/1.01  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.58/1.01  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.58/1.01  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.58/1.01  
% 1.58/1.02  tff(f_33, axiom, (![A, B, C]: (k3_enumset1(A, A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_enumset1)).
% 1.58/1.02  tff(f_29, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 1.58/1.02  tff(f_36, negated_conjecture, ~(![A, B, C]: (k4_enumset1(A, A, A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_enumset1)).
% 1.58/1.02  tff(c_8, plain, (![A_13, B_14, C_15]: (k3_enumset1(A_13, A_13, A_13, B_14, C_15)=k1_enumset1(A_13, B_14, C_15))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.58/1.02  tff(c_4, plain, (![D_10, A_7, B_8, E_11, C_9]: (k4_enumset1(A_7, A_7, B_8, C_9, D_10, E_11)=k3_enumset1(A_7, B_8, C_9, D_10, E_11))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.58/1.02  tff(c_10, plain, (k4_enumset1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3')!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.58/1.02  tff(c_11, plain, (k3_enumset1('#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3')!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_10])).
% 1.58/1.02  tff(c_13, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_11])).
% 1.58/1.02  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.58/1.02  
% 1.58/1.02  Inference rules
% 1.58/1.02  ----------------------
% 1.58/1.02  #Ref     : 0
% 1.58/1.02  #Sup     : 0
% 1.58/1.02  #Fact    : 0
% 1.58/1.02  #Define  : 0
% 1.58/1.02  #Split   : 0
% 1.58/1.02  #Chain   : 0
% 1.58/1.02  #Close   : 0
% 1.58/1.02  
% 1.58/1.02  Ordering : KBO
% 1.58/1.02  
% 1.58/1.02  Simplification rules
% 1.58/1.02  ----------------------
% 1.58/1.02  #Subsume      : 4
% 1.58/1.02  #Demod        : 2
% 1.58/1.02  #Tautology    : 0
% 1.58/1.02  #SimpNegUnit  : 0
% 1.58/1.02  #BackRed      : 0
% 1.58/1.02  
% 1.58/1.02  #Partial instantiations: 0
% 1.58/1.02  #Strategies tried      : 1
% 1.58/1.02  
% 1.58/1.02  Timing (in seconds)
% 1.58/1.02  ----------------------
% 1.58/1.03  Preprocessing        : 0.27
% 1.58/1.03  Parsing              : 0.14
% 1.58/1.03  CNF conversion       : 0.02
% 1.58/1.03  Main loop            : 0.02
% 1.58/1.03  Inferencing          : 0.00
% 1.58/1.03  Reduction            : 0.01
% 1.58/1.03  Demodulation         : 0.01
% 1.58/1.03  BG Simplification    : 0.01
% 1.58/1.03  Subsumption          : 0.01
% 1.58/1.03  Abstraction          : 0.00
% 1.58/1.03  MUC search           : 0.00
% 1.58/1.03  Cooper               : 0.00
% 1.58/1.03  Total                : 0.31
% 1.58/1.03  Index Insertion      : 0.00
% 1.58/1.03  Index Deletion       : 0.00
% 1.58/1.03  Index Matching       : 0.00
% 1.58/1.03  BG Taut test         : 0.00
%------------------------------------------------------------------------------
