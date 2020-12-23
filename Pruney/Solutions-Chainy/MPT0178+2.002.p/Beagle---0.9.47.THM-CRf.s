%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:37 EST 2020

% Result     : Theorem 1.86s
% Output     : CNFRefutation 1.91s
% Verified   : 
% Statistics : Number of formulae       :   21 (  21 expanded)
%              Number of leaves         :   14 (  14 expanded)
%              Depth                    :    4
%              Number of atoms          :   11 (  11 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k2_xboole_0 > #nlpp > k1_tarski > #skF_1

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

tff(f_33,axiom,(
    ! [A] : k2_enumset1(A,A,A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D,E] : k5_enumset1(A,A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_enumset1)).

tff(f_36,negated_conjecture,(
    ~ ! [A] : k5_enumset1(A,A,A,A,A,A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_enumset1)).

tff(c_8,plain,(
    ! [A_17] : k2_enumset1(A_17,A_17,A_17,A_17) = k1_tarski(A_17) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_4,plain,(
    ! [A_8,B_9,C_10,D_11] : k3_enumset1(A_8,A_8,B_9,C_10,D_11) = k2_enumset1(A_8,B_9,C_10,D_11) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [E_16,D_15,C_14,A_12,B_13] : k5_enumset1(A_12,A_12,A_12,B_13,C_14,D_15,E_16) = k3_enumset1(A_12,B_13,C_14,D_15,E_16) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    k5_enumset1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_1') != k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_11,plain,(
    k3_enumset1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1') != k1_tarski('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_10])).

tff(c_12,plain,(
    k2_enumset1('#skF_1','#skF_1','#skF_1','#skF_1') != k1_tarski('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_11])).

tff(c_14,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:03:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.86/1.36  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.86/1.36  
% 1.86/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.91/1.37  %$ k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k2_xboole_0 > #nlpp > k1_tarski > #skF_1
% 1.91/1.37  
% 1.91/1.37  %Foreground sorts:
% 1.91/1.37  
% 1.91/1.37  
% 1.91/1.37  %Background operators:
% 1.91/1.37  
% 1.91/1.37  
% 1.91/1.37  %Foreground operators:
% 1.91/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.91/1.37  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.91/1.37  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.91/1.37  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.91/1.37  tff('#skF_1', type, '#skF_1': $i).
% 1.91/1.37  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.91/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.91/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.91/1.37  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.91/1.37  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.91/1.37  
% 1.91/1.38  tff(f_33, axiom, (![A]: (k2_enumset1(A, A, A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t82_enumset1)).
% 1.91/1.38  tff(f_29, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 1.91/1.38  tff(f_31, axiom, (![A, B, C, D, E]: (k5_enumset1(A, A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_enumset1)).
% 1.91/1.38  tff(f_36, negated_conjecture, ~(![A]: (k5_enumset1(A, A, A, A, A, A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_enumset1)).
% 1.91/1.38  tff(c_8, plain, (![A_17]: (k2_enumset1(A_17, A_17, A_17, A_17)=k1_tarski(A_17))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.91/1.38  tff(c_4, plain, (![A_8, B_9, C_10, D_11]: (k3_enumset1(A_8, A_8, B_9, C_10, D_11)=k2_enumset1(A_8, B_9, C_10, D_11))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.91/1.38  tff(c_6, plain, (![E_16, D_15, C_14, A_12, B_13]: (k5_enumset1(A_12, A_12, A_12, B_13, C_14, D_15, E_16)=k3_enumset1(A_12, B_13, C_14, D_15, E_16))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.91/1.38  tff(c_10, plain, (k5_enumset1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1')!=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.91/1.38  tff(c_11, plain, (k3_enumset1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1')!=k1_tarski('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_10])).
% 1.91/1.38  tff(c_12, plain, (k2_enumset1('#skF_1', '#skF_1', '#skF_1', '#skF_1')!=k1_tarski('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_11])).
% 1.91/1.38  tff(c_14, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_12])).
% 1.91/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.91/1.38  
% 1.91/1.38  Inference rules
% 1.91/1.38  ----------------------
% 1.91/1.38  #Ref     : 0
% 1.91/1.38  #Sup     : 0
% 1.91/1.38  #Fact    : 0
% 1.91/1.38  #Define  : 0
% 1.91/1.38  #Split   : 0
% 1.91/1.39  #Chain   : 0
% 1.91/1.39  #Close   : 0
% 1.91/1.39  
% 1.91/1.39  Ordering : KBO
% 1.91/1.39  
% 1.91/1.39  Simplification rules
% 1.91/1.39  ----------------------
% 1.91/1.39  #Subsume      : 4
% 1.91/1.39  #Demod        : 3
% 1.91/1.39  #Tautology    : 0
% 1.91/1.39  #SimpNegUnit  : 0
% 1.91/1.39  #BackRed      : 0
% 1.91/1.39  
% 1.91/1.39  #Partial instantiations: 0
% 1.91/1.39  #Strategies tried      : 1
% 1.91/1.39  
% 1.91/1.39  Timing (in seconds)
% 1.91/1.39  ----------------------
% 1.91/1.39  Preprocessing        : 0.41
% 1.91/1.39  Parsing              : 0.21
% 1.91/1.39  CNF conversion       : 0.02
% 1.91/1.39  Main loop            : 0.05
% 1.91/1.39  Inferencing          : 0.00
% 1.91/1.39  Reduction            : 0.03
% 1.91/1.39  Demodulation         : 0.02
% 1.91/1.39  BG Simplification    : 0.01
% 1.91/1.39  Subsumption          : 0.01
% 1.91/1.39  Abstraction          : 0.01
% 1.91/1.39  MUC search           : 0.00
% 1.91/1.39  Cooper               : 0.00
% 1.91/1.39  Total                : 0.50
% 1.91/1.39  Index Insertion      : 0.00
% 1.91/1.39  Index Deletion       : 0.00
% 1.91/1.39  Index Matching       : 0.00
% 1.91/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
