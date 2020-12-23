%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:27 EST 2020

% Result     : Theorem 1.58s
% Output     : CNFRefutation 1.58s
% Verified   : 
% Statistics : Number of formulae       :   21 (  21 expanded)
%              Number of leaves         :   16 (  16 expanded)
%              Depth                    :    3
%              Number of atoms          :    8 (   8 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff(f_31,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_38,negated_conjecture,(
    ~ ! [A,B,C] : k4_enumset1(A,A,A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_enumset1)).

tff(c_8,plain,(
    ! [A_15,B_16,C_17] : k3_enumset1(A_15,A_15,A_15,B_16,C_17) = k1_enumset1(A_15,B_16,C_17) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_6,plain,(
    ! [B_11,A_10,C_12,E_14,D_13] : k4_enumset1(A_10,A_10,B_11,C_12,D_13,E_14) = k3_enumset1(A_10,B_11,C_12,D_13,E_14) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12,plain,(
    k4_enumset1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3') != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_13,plain,(
    k3_enumset1('#skF_1','#skF_1','#skF_1','#skF_2','#skF_3') != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_12])).

tff(c_15,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:25:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.58/1.03  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.58/1.04  
% 1.58/1.04  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.58/1.04  %$ k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 1.58/1.04  
% 1.58/1.04  %Foreground sorts:
% 1.58/1.04  
% 1.58/1.04  
% 1.58/1.04  %Background operators:
% 1.58/1.04  
% 1.58/1.04  
% 1.58/1.04  %Foreground operators:
% 1.58/1.04  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.58/1.04  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.58/1.04  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.58/1.04  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.58/1.04  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.58/1.04  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.58/1.04  tff('#skF_2', type, '#skF_2': $i).
% 1.58/1.04  tff('#skF_3', type, '#skF_3': $i).
% 1.58/1.04  tff('#skF_1', type, '#skF_1': $i).
% 1.58/1.04  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.58/1.04  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.58/1.04  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.58/1.04  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.58/1.04  
% 1.58/1.05  tff(f_33, axiom, (![A, B, C]: (k3_enumset1(A, A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_enumset1)).
% 1.58/1.05  tff(f_31, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 1.58/1.05  tff(f_38, negated_conjecture, ~(![A, B, C]: (k4_enumset1(A, A, A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_enumset1)).
% 1.58/1.05  tff(c_8, plain, (![A_15, B_16, C_17]: (k3_enumset1(A_15, A_15, A_15, B_16, C_17)=k1_enumset1(A_15, B_16, C_17))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.58/1.05  tff(c_6, plain, (![B_11, A_10, C_12, E_14, D_13]: (k4_enumset1(A_10, A_10, B_11, C_12, D_13, E_14)=k3_enumset1(A_10, B_11, C_12, D_13, E_14))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.58/1.05  tff(c_12, plain, (k4_enumset1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3')!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.58/1.05  tff(c_13, plain, (k3_enumset1('#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3')!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_12])).
% 1.58/1.05  tff(c_15, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_13])).
% 1.58/1.05  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.58/1.05  
% 1.58/1.05  Inference rules
% 1.58/1.05  ----------------------
% 1.58/1.05  #Ref     : 0
% 1.58/1.05  #Sup     : 0
% 1.58/1.05  #Fact    : 0
% 1.58/1.05  #Define  : 0
% 1.58/1.05  #Split   : 0
% 1.58/1.05  #Chain   : 0
% 1.58/1.05  #Close   : 0
% 1.58/1.05  
% 1.58/1.05  Ordering : KBO
% 1.58/1.05  
% 1.58/1.05  Simplification rules
% 1.58/1.05  ----------------------
% 1.58/1.05  #Subsume      : 5
% 1.58/1.05  #Demod        : 2
% 1.58/1.05  #Tautology    : 0
% 1.58/1.05  #SimpNegUnit  : 0
% 1.58/1.05  #BackRed      : 0
% 1.58/1.05  
% 1.58/1.05  #Partial instantiations: 0
% 1.58/1.05  #Strategies tried      : 1
% 1.58/1.05  
% 1.58/1.05  Timing (in seconds)
% 1.58/1.05  ----------------------
% 1.58/1.05  Preprocessing        : 0.27
% 1.58/1.05  Parsing              : 0.14
% 1.58/1.05  CNF conversion       : 0.02
% 1.58/1.05  Main loop            : 0.02
% 1.58/1.05  Inferencing          : 0.00
% 1.58/1.05  Reduction            : 0.02
% 1.58/1.05  Demodulation         : 0.01
% 1.58/1.05  BG Simplification    : 0.01
% 1.58/1.05  Subsumption          : 0.00
% 1.58/1.05  Abstraction          : 0.00
% 1.58/1.05  MUC search           : 0.00
% 1.58/1.05  Cooper               : 0.00
% 1.58/1.05  Total                : 0.31
% 1.58/1.05  Index Insertion      : 0.00
% 1.58/1.05  Index Deletion       : 0.00
% 1.58/1.05  Index Matching       : 0.00
% 1.58/1.05  BG Taut test         : 0.00
%------------------------------------------------------------------------------
