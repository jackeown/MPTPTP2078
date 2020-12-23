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
% DateTime   : Thu Dec  3 09:46:33 EST 2020

% Result     : Theorem 1.51s
% Output     : CNFRefutation 1.51s
% Verified   : 
% Statistics : Number of formulae       :   23 (  23 expanded)
%              Number of leaves         :   14 (  14 expanded)
%              Depth                    :    5
%              Number of atoms          :   14 (  14 expanded)
%              Number of equality atoms :   13 (  13 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k4_enumset1 > k3_enumset1 > k2_enumset1 > k2_tarski > #nlpp > k1_tarski > #skF_1

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_27,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_33,axiom,(
    ! [A,B] : k2_enumset1(A,A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_36,negated_conjecture,(
    ~ ! [A] : k4_enumset1(A,A,A,A,A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_enumset1)).

tff(c_2,plain,(
    ! [A_1] : k2_tarski(A_1,A_1) = k1_tarski(A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    ! [A_11,B_12] : k2_enumset1(A_11,A_11,A_11,B_12) = k2_tarski(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_4,plain,(
    ! [A_2,B_3,C_4,D_5] : k3_enumset1(A_2,A_2,B_3,C_4,D_5) = k2_enumset1(A_2,B_3,C_4,D_5) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [B_7,D_9,C_8,E_10,A_6] : k4_enumset1(A_6,A_6,B_7,C_8,D_9,E_10) = k3_enumset1(A_6,B_7,C_8,D_9,E_10) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    k4_enumset1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_1') != k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_11,plain,(
    k3_enumset1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1') != k1_tarski('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_10])).

tff(c_12,plain,(
    k2_enumset1('#skF_1','#skF_1','#skF_1','#skF_1') != k1_tarski('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_11])).

tff(c_13,plain,(
    k2_tarski('#skF_1','#skF_1') != k1_tarski('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_12])).

tff(c_15,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:40:34 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.51/1.02  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.51/1.02  
% 1.51/1.02  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.51/1.03  %$ k4_enumset1 > k3_enumset1 > k2_enumset1 > k2_tarski > #nlpp > k1_tarski > #skF_1
% 1.51/1.03  
% 1.51/1.03  %Foreground sorts:
% 1.51/1.03  
% 1.51/1.03  
% 1.51/1.03  %Background operators:
% 1.51/1.03  
% 1.51/1.03  
% 1.51/1.03  %Foreground operators:
% 1.51/1.03  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.51/1.03  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.51/1.03  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.51/1.03  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.51/1.03  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.51/1.03  tff('#skF_1', type, '#skF_1': $i).
% 1.51/1.03  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.51/1.03  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.51/1.03  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.51/1.03  
% 1.51/1.04  tff(f_27, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 1.51/1.04  tff(f_33, axiom, (![A, B]: (k2_enumset1(A, A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_enumset1)).
% 1.51/1.04  tff(f_29, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 1.51/1.04  tff(f_31, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 1.51/1.04  tff(f_36, negated_conjecture, ~(![A]: (k4_enumset1(A, A, A, A, A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_enumset1)).
% 1.51/1.04  tff(c_2, plain, (![A_1]: (k2_tarski(A_1, A_1)=k1_tarski(A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.51/1.04  tff(c_8, plain, (![A_11, B_12]: (k2_enumset1(A_11, A_11, A_11, B_12)=k2_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.51/1.04  tff(c_4, plain, (![A_2, B_3, C_4, D_5]: (k3_enumset1(A_2, A_2, B_3, C_4, D_5)=k2_enumset1(A_2, B_3, C_4, D_5))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.51/1.04  tff(c_6, plain, (![B_7, D_9, C_8, E_10, A_6]: (k4_enumset1(A_6, A_6, B_7, C_8, D_9, E_10)=k3_enumset1(A_6, B_7, C_8, D_9, E_10))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.51/1.04  tff(c_10, plain, (k4_enumset1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1')!=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.51/1.04  tff(c_11, plain, (k3_enumset1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1')!=k1_tarski('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_10])).
% 1.51/1.04  tff(c_12, plain, (k2_enumset1('#skF_1', '#skF_1', '#skF_1', '#skF_1')!=k1_tarski('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_11])).
% 1.51/1.04  tff(c_13, plain, (k2_tarski('#skF_1', '#skF_1')!=k1_tarski('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_12])).
% 1.51/1.04  tff(c_15, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_13])).
% 1.51/1.04  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.51/1.04  
% 1.51/1.04  Inference rules
% 1.51/1.04  ----------------------
% 1.51/1.04  #Ref     : 0
% 1.51/1.04  #Sup     : 0
% 1.51/1.04  #Fact    : 0
% 1.51/1.04  #Define  : 0
% 1.51/1.04  #Split   : 0
% 1.51/1.04  #Chain   : 0
% 1.51/1.04  #Close   : 0
% 1.51/1.04  
% 1.51/1.04  Ordering : KBO
% 1.51/1.04  
% 1.51/1.04  Simplification rules
% 1.51/1.04  ----------------------
% 1.51/1.04  #Subsume      : 4
% 1.51/1.04  #Demod        : 4
% 1.51/1.04  #Tautology    : 0
% 1.51/1.04  #SimpNegUnit  : 0
% 1.51/1.04  #BackRed      : 0
% 1.51/1.04  
% 1.51/1.04  #Partial instantiations: 0
% 1.51/1.04  #Strategies tried      : 1
% 1.51/1.04  
% 1.51/1.04  Timing (in seconds)
% 1.51/1.04  ----------------------
% 1.51/1.04  Preprocessing        : 0.26
% 1.51/1.04  Parsing              : 0.13
% 1.51/1.04  CNF conversion       : 0.01
% 1.51/1.04  Main loop            : 0.03
% 1.51/1.04  Inferencing          : 0.00
% 1.51/1.04  Reduction            : 0.02
% 1.51/1.04  Demodulation         : 0.01
% 1.51/1.04  BG Simplification    : 0.01
% 1.51/1.04  Subsumption          : 0.01
% 1.51/1.04  Abstraction          : 0.00
% 1.51/1.04  MUC search           : 0.00
% 1.51/1.04  Cooper               : 0.00
% 1.51/1.04  Total                : 0.31
% 1.51/1.04  Index Insertion      : 0.00
% 1.51/1.04  Index Deletion       : 0.00
% 1.51/1.04  Index Matching       : 0.00
% 1.51/1.04  BG Taut test         : 0.00
%------------------------------------------------------------------------------
