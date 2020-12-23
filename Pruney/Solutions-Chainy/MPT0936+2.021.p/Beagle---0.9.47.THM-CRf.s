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
% DateTime   : Thu Dec  3 10:10:29 EST 2020

% Result     : Theorem 1.62s
% Output     : CNFRefutation 1.62s
% Verified   : 
% Statistics : Number of formulae       :   20 (  22 expanded)
%              Number of leaves         :   14 (  15 expanded)
%              Depth                    :    4
%              Number of atoms          :    9 (  11 expanded)
%              Number of equality atoms :    8 (  10 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k3_mcart_1 > k4_tarski > k2_tarski > #nlpp > k1_tarski > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_27,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D,E,F] : k1_relat_1(k1_relat_1(k2_tarski(k3_mcart_1(A,B,C),k3_mcart_1(D,E,F)))) = k2_tarski(A,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_mcart_1)).

tff(f_34,negated_conjecture,(
    ~ ! [A,B,C] : k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(A,B,C)))) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_mcart_1)).

tff(c_2,plain,(
    ! [A_1] : k2_tarski(A_1,A_1) = k1_tarski(A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_47,plain,(
    ! [C_22,B_21,D_19,A_23,E_24,F_20] : k1_relat_1(k1_relat_1(k2_tarski(k3_mcart_1(A_23,B_21,C_22),k3_mcart_1(D_19,E_24,F_20)))) = k2_tarski(A_23,D_19) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_63,plain,(
    ! [A_23,B_21,C_22] : k2_tarski(A_23,A_23) = k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(A_23,B_21,C_22)))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_47])).

tff(c_66,plain,(
    ! [A_23,B_21,C_22] : k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(A_23,B_21,C_22)))) = k1_tarski(A_23) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_63])).

tff(c_8,plain,(
    k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1('#skF_1','#skF_2','#skF_3')))) != k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_69,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:42:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.62/1.09  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.62/1.09  
% 1.62/1.09  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.62/1.09  %$ k3_mcart_1 > k4_tarski > k2_tarski > #nlpp > k1_tarski > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 1.62/1.09  
% 1.62/1.09  %Foreground sorts:
% 1.62/1.09  
% 1.62/1.09  
% 1.62/1.09  %Background operators:
% 1.62/1.09  
% 1.62/1.09  
% 1.62/1.09  %Foreground operators:
% 1.62/1.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.62/1.09  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.62/1.09  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.62/1.09  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 1.62/1.09  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.62/1.09  tff('#skF_2', type, '#skF_2': $i).
% 1.62/1.09  tff('#skF_3', type, '#skF_3': $i).
% 1.62/1.09  tff('#skF_1', type, '#skF_1': $i).
% 1.62/1.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.62/1.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.62/1.09  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.62/1.09  
% 1.62/1.10  tff(f_27, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 1.62/1.10  tff(f_31, axiom, (![A, B, C, D, E, F]: (k1_relat_1(k1_relat_1(k2_tarski(k3_mcart_1(A, B, C), k3_mcart_1(D, E, F)))) = k2_tarski(A, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t96_mcart_1)).
% 1.62/1.10  tff(f_34, negated_conjecture, ~(![A, B, C]: (k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(A, B, C)))) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_mcart_1)).
% 1.62/1.10  tff(c_2, plain, (![A_1]: (k2_tarski(A_1, A_1)=k1_tarski(A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.62/1.10  tff(c_47, plain, (![C_22, B_21, D_19, A_23, E_24, F_20]: (k1_relat_1(k1_relat_1(k2_tarski(k3_mcart_1(A_23, B_21, C_22), k3_mcart_1(D_19, E_24, F_20))))=k2_tarski(A_23, D_19))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.62/1.10  tff(c_63, plain, (![A_23, B_21, C_22]: (k2_tarski(A_23, A_23)=k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(A_23, B_21, C_22)))))), inference(superposition, [status(thm), theory('equality')], [c_2, c_47])).
% 1.62/1.10  tff(c_66, plain, (![A_23, B_21, C_22]: (k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(A_23, B_21, C_22))))=k1_tarski(A_23))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_63])).
% 1.62/1.10  tff(c_8, plain, (k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1('#skF_1', '#skF_2', '#skF_3'))))!=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.62/1.10  tff(c_69, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_8])).
% 1.62/1.10  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.62/1.10  
% 1.62/1.10  Inference rules
% 1.62/1.10  ----------------------
% 1.62/1.10  #Ref     : 0
% 1.62/1.10  #Sup     : 14
% 1.62/1.10  #Fact    : 0
% 1.62/1.10  #Define  : 0
% 1.62/1.10  #Split   : 0
% 1.62/1.10  #Chain   : 0
% 1.62/1.10  #Close   : 0
% 1.62/1.10  
% 1.62/1.10  Ordering : KBO
% 1.62/1.10  
% 1.62/1.10  Simplification rules
% 1.62/1.10  ----------------------
% 1.62/1.10  #Subsume      : 0
% 1.62/1.10  #Demod        : 5
% 1.62/1.10  #Tautology    : 10
% 1.62/1.10  #SimpNegUnit  : 0
% 1.62/1.10  #BackRed      : 1
% 1.62/1.10  
% 1.62/1.10  #Partial instantiations: 0
% 1.62/1.10  #Strategies tried      : 1
% 1.62/1.10  
% 1.62/1.10  Timing (in seconds)
% 1.62/1.10  ----------------------
% 1.62/1.10  Preprocessing        : 0.26
% 1.62/1.10  Parsing              : 0.14
% 1.62/1.10  CNF conversion       : 0.01
% 1.62/1.10  Main loop            : 0.08
% 1.62/1.10  Inferencing          : 0.04
% 1.62/1.10  Reduction            : 0.03
% 1.62/1.10  Demodulation         : 0.02
% 1.62/1.10  BG Simplification    : 0.01
% 1.62/1.10  Subsumption          : 0.01
% 1.62/1.10  Abstraction          : 0.01
% 1.62/1.10  MUC search           : 0.00
% 1.62/1.10  Cooper               : 0.00
% 1.62/1.10  Total                : 0.36
% 1.62/1.10  Index Insertion      : 0.00
% 1.62/1.10  Index Deletion       : 0.00
% 1.62/1.10  Index Matching       : 0.00
% 1.62/1.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------
