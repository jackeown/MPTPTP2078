%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:34 EST 2020

% Result     : Theorem 1.56s
% Output     : CNFRefutation 1.56s
% Verified   : 
% Statistics : Number of formulae       :   28 (  28 expanded)
%              Number of leaves         :   17 (  17 expanded)
%              Depth                    :    6
%              Number of atoms          :   17 (  17 expanded)
%              Number of equality atoms :   16 (  16 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_27,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_38,negated_conjecture,(
    ~ ! [A,B] : k5_enumset1(A,A,A,A,A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_enumset1)).

tff(c_2,plain,(
    ! [A_1,B_2] : k1_enumset1(A_1,A_1,B_2) = k2_tarski(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_3,B_4,C_5] : k2_enumset1(A_3,A_3,B_4,C_5) = k1_enumset1(A_3,B_4,C_5) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [A_6,B_7,C_8,D_9] : k3_enumset1(A_6,A_6,B_7,C_8,D_9) = k2_enumset1(A_6,B_7,C_8,D_9) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [B_11,A_10,C_12,E_14,D_13] : k4_enumset1(A_10,A_10,B_11,C_12,D_13,E_14) = k3_enumset1(A_10,B_11,C_12,D_13,E_14) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [B_16,A_15,D_18,E_19,F_20,C_17] : k5_enumset1(A_15,A_15,B_16,C_17,D_18,E_19,F_20) = k4_enumset1(A_15,B_16,C_17,D_18,E_19,F_20) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    k5_enumset1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_2') != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_13,plain,(
    k4_enumset1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_2') != k2_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_12])).

tff(c_14,plain,(
    k3_enumset1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2') != k2_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_13])).

tff(c_15,plain,(
    k2_enumset1('#skF_1','#skF_1','#skF_1','#skF_2') != k2_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_14])).

tff(c_16,plain,(
    k1_enumset1('#skF_1','#skF_1','#skF_2') != k2_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_15])).

tff(c_18,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 10:25:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.56/1.03  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.56/1.04  
% 1.56/1.04  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.56/1.04  %$ k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > #skF_2 > #skF_1
% 1.56/1.04  
% 1.56/1.04  %Foreground sorts:
% 1.56/1.04  
% 1.56/1.04  
% 1.56/1.04  %Background operators:
% 1.56/1.04  
% 1.56/1.04  
% 1.56/1.04  %Foreground operators:
% 1.56/1.04  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.56/1.04  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.56/1.04  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.56/1.04  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.56/1.04  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.56/1.04  tff('#skF_2', type, '#skF_2': $i).
% 1.56/1.04  tff('#skF_1', type, '#skF_1': $i).
% 1.56/1.04  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.56/1.04  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.56/1.04  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.56/1.04  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.56/1.04  
% 1.56/1.05  tff(f_27, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 1.56/1.05  tff(f_29, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 1.56/1.05  tff(f_31, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 1.56/1.05  tff(f_33, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 1.56/1.05  tff(f_35, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 1.56/1.05  tff(f_38, negated_conjecture, ~(![A, B]: (k5_enumset1(A, A, A, A, A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_enumset1)).
% 1.56/1.05  tff(c_2, plain, (![A_1, B_2]: (k1_enumset1(A_1, A_1, B_2)=k2_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.56/1.05  tff(c_4, plain, (![A_3, B_4, C_5]: (k2_enumset1(A_3, A_3, B_4, C_5)=k1_enumset1(A_3, B_4, C_5))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.56/1.05  tff(c_6, plain, (![A_6, B_7, C_8, D_9]: (k3_enumset1(A_6, A_6, B_7, C_8, D_9)=k2_enumset1(A_6, B_7, C_8, D_9))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.56/1.05  tff(c_8, plain, (![B_11, A_10, C_12, E_14, D_13]: (k4_enumset1(A_10, A_10, B_11, C_12, D_13, E_14)=k3_enumset1(A_10, B_11, C_12, D_13, E_14))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.56/1.05  tff(c_10, plain, (![B_16, A_15, D_18, E_19, F_20, C_17]: (k5_enumset1(A_15, A_15, B_16, C_17, D_18, E_19, F_20)=k4_enumset1(A_15, B_16, C_17, D_18, E_19, F_20))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.56/1.05  tff(c_12, plain, (k5_enumset1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2')!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.56/1.05  tff(c_13, plain, (k4_enumset1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2')!=k2_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_12])).
% 1.56/1.05  tff(c_14, plain, (k3_enumset1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2')!=k2_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_13])).
% 1.56/1.05  tff(c_15, plain, (k2_enumset1('#skF_1', '#skF_1', '#skF_1', '#skF_2')!=k2_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_14])).
% 1.56/1.05  tff(c_16, plain, (k1_enumset1('#skF_1', '#skF_1', '#skF_2')!=k2_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_15])).
% 1.56/1.05  tff(c_18, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_16])).
% 1.56/1.05  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.56/1.05  
% 1.56/1.05  Inference rules
% 1.56/1.05  ----------------------
% 1.56/1.05  #Ref     : 0
% 1.56/1.05  #Sup     : 0
% 1.56/1.05  #Fact    : 0
% 1.56/1.05  #Define  : 0
% 1.56/1.05  #Split   : 0
% 1.56/1.05  #Chain   : 0
% 1.56/1.05  #Close   : 0
% 1.56/1.05  
% 1.56/1.05  Ordering : KBO
% 1.56/1.05  
% 1.56/1.05  Simplification rules
% 1.56/1.05  ----------------------
% 1.56/1.05  #Subsume      : 5
% 1.56/1.05  #Demod        : 5
% 1.56/1.05  #Tautology    : 0
% 1.56/1.05  #SimpNegUnit  : 0
% 1.56/1.05  #BackRed      : 0
% 1.56/1.05  
% 1.56/1.05  #Partial instantiations: 0
% 1.56/1.05  #Strategies tried      : 1
% 1.56/1.05  
% 1.56/1.05  Timing (in seconds)
% 1.56/1.05  ----------------------
% 1.56/1.05  Preprocessing        : 0.27
% 1.56/1.05  Parsing              : 0.14
% 1.56/1.05  CNF conversion       : 0.01
% 1.56/1.05  Main loop            : 0.03
% 1.56/1.05  Inferencing          : 0.00
% 1.56/1.05  Reduction            : 0.02
% 1.56/1.05  Demodulation         : 0.02
% 1.56/1.05  BG Simplification    : 0.01
% 1.56/1.05  Subsumption          : 0.01
% 1.56/1.05  Abstraction          : 0.00
% 1.56/1.06  MUC search           : 0.00
% 1.56/1.06  Cooper               : 0.00
% 1.56/1.06  Total                : 0.32
% 1.56/1.06  Index Insertion      : 0.00
% 1.56/1.06  Index Deletion       : 0.00
% 1.56/1.06  Index Matching       : 0.00
% 1.56/1.06  BG Taut test         : 0.00
%------------------------------------------------------------------------------
