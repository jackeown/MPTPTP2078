%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:38 EST 2020

% Result     : Theorem 1.56s
% Output     : CNFRefutation 1.56s
% Verified   : 
% Statistics : Number of formulae       :   22 (  22 expanded)
%              Number of leaves         :   16 (  16 expanded)
%              Depth                    :    3
%              Number of atoms          :   10 (  10 expanded)
%              Number of equality atoms :    9 (   9 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff(f_35,axiom,(
    ! [A,B] : k3_enumset1(A,A,A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D,E] : k5_enumset1(A,A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D,E,F,G] : k6_enumset1(A,A,B,C,D,E,F,G) = k5_enumset1(A,B,C,D,E,F,G) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

tff(f_38,negated_conjecture,(
    ~ ! [A,B] : k6_enumset1(A,A,A,A,A,A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_enumset1)).

tff(c_10,plain,(
    ! [A_23,B_24] : k3_enumset1(A_23,A_23,A_23,A_23,B_24) = k2_tarski(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_8,plain,(
    ! [E_22,D_21,A_18,C_20,B_19] : k5_enumset1(A_18,A_18,A_18,B_19,C_20,D_21,E_22) = k3_enumset1(A_18,B_19,C_20,D_21,E_22) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_6,plain,(
    ! [G_17,F_16,D_14,E_15,B_12,A_11,C_13] : k6_enumset1(A_11,A_11,B_12,C_13,D_14,E_15,F_16,G_17) = k5_enumset1(A_11,B_12,C_13,D_14,E_15,F_16,G_17) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12,plain,(
    k6_enumset1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_2') != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_13,plain,(
    k5_enumset1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_2') != k2_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_12])).

tff(c_15,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_8,c_13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:38:26 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.56/1.03  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.56/1.03  
% 1.56/1.03  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.56/1.03  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > #skF_2 > #skF_1
% 1.56/1.03  
% 1.56/1.03  %Foreground sorts:
% 1.56/1.03  
% 1.56/1.03  
% 1.56/1.03  %Background operators:
% 1.56/1.03  
% 1.56/1.03  
% 1.56/1.03  %Foreground operators:
% 1.56/1.03  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.56/1.03  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.56/1.03  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.56/1.03  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.56/1.03  tff('#skF_2', type, '#skF_2': $i).
% 1.56/1.03  tff('#skF_1', type, '#skF_1': $i).
% 1.56/1.03  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.56/1.03  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 1.56/1.03  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.56/1.03  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.56/1.03  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.56/1.03  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.56/1.03  
% 1.56/1.04  tff(f_35, axiom, (![A, B]: (k3_enumset1(A, A, A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_enumset1)).
% 1.56/1.04  tff(f_33, axiom, (![A, B, C, D, E]: (k5_enumset1(A, A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_enumset1)).
% 1.56/1.04  tff(f_31, axiom, (![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 1.56/1.04  tff(f_38, negated_conjecture, ~(![A, B]: (k6_enumset1(A, A, A, A, A, A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_enumset1)).
% 1.56/1.04  tff(c_10, plain, (![A_23, B_24]: (k3_enumset1(A_23, A_23, A_23, A_23, B_24)=k2_tarski(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.56/1.04  tff(c_8, plain, (![E_22, D_21, A_18, C_20, B_19]: (k5_enumset1(A_18, A_18, A_18, B_19, C_20, D_21, E_22)=k3_enumset1(A_18, B_19, C_20, D_21, E_22))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.56/1.04  tff(c_6, plain, (![G_17, F_16, D_14, E_15, B_12, A_11, C_13]: (k6_enumset1(A_11, A_11, B_12, C_13, D_14, E_15, F_16, G_17)=k5_enumset1(A_11, B_12, C_13, D_14, E_15, F_16, G_17))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.56/1.04  tff(c_12, plain, (k6_enumset1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2')!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.56/1.04  tff(c_13, plain, (k5_enumset1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2')!=k2_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_12])).
% 1.56/1.04  tff(c_15, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_8, c_13])).
% 1.56/1.04  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.56/1.04  
% 1.56/1.04  Inference rules
% 1.56/1.04  ----------------------
% 1.56/1.04  #Ref     : 0
% 1.56/1.04  #Sup     : 0
% 1.56/1.04  #Fact    : 0
% 1.56/1.04  #Define  : 0
% 1.56/1.04  #Split   : 0
% 1.56/1.04  #Chain   : 0
% 1.56/1.04  #Close   : 0
% 1.56/1.04  
% 1.56/1.04  Ordering : KBO
% 1.56/1.04  
% 1.56/1.04  Simplification rules
% 1.56/1.04  ----------------------
% 1.56/1.04  #Subsume      : 5
% 1.56/1.04  #Demod        : 3
% 1.56/1.04  #Tautology    : 0
% 1.56/1.04  #SimpNegUnit  : 0
% 1.56/1.04  #BackRed      : 0
% 1.56/1.04  
% 1.56/1.04  #Partial instantiations: 0
% 1.56/1.04  #Strategies tried      : 1
% 1.56/1.04  
% 1.56/1.04  Timing (in seconds)
% 1.56/1.04  ----------------------
% 1.56/1.05  Preprocessing        : 0.27
% 1.56/1.05  Parsing              : 0.15
% 1.56/1.05  CNF conversion       : 0.02
% 1.56/1.05  Main loop            : 0.02
% 1.56/1.05  Inferencing          : 0.00
% 1.56/1.05  Reduction            : 0.02
% 1.56/1.05  Demodulation         : 0.01
% 1.56/1.05  BG Simplification    : 0.01
% 1.56/1.05  Subsumption          : 0.01
% 1.56/1.05  Abstraction          : 0.00
% 1.56/1.05  MUC search           : 0.00
% 1.56/1.05  Cooper               : 0.00
% 1.56/1.05  Total                : 0.32
% 1.56/1.05  Index Insertion      : 0.00
% 1.56/1.05  Index Deletion       : 0.00
% 1.56/1.05  Index Matching       : 0.00
% 1.56/1.05  BG Taut test         : 0.00
%------------------------------------------------------------------------------
