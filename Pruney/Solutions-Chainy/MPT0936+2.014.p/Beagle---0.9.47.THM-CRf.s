%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:29 EST 2020

% Result     : Theorem 1.77s
% Output     : CNFRefutation 1.89s
% Verified   : 
% Statistics : Number of formulae       :   31 (  43 expanded)
%              Number of leaves         :   19 (  24 expanded)
%              Depth                    :    7
%              Number of atoms          :   21 (  37 expanded)
%              Number of equality atoms :   16 (  28 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_relat_1 > k2_enumset1 > k3_mcart_1 > k4_tarski > k2_tarski > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_27,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D] : v1_relat_1(k2_tarski(k4_tarski(A,B),k4_tarski(C,D))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_relat_1)).

tff(f_39,axiom,(
    ! [A,B,C,D,E] :
      ( v1_relat_1(E)
     => ( E = k2_tarski(k4_tarski(A,B),k4_tarski(C,D))
       => ( k1_relat_1(E) = k2_tarski(A,C)
          & k2_relat_1(E) = k2_tarski(B,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_relat_1)).

tff(f_41,axiom,(
    ! [A,B,C] : k3_mcart_1(A,B,C) = k4_tarski(k4_tarski(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

tff(f_44,negated_conjecture,(
    ~ ! [A,B,C] : k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(A,B,C)))) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_mcart_1)).

tff(c_2,plain,(
    ! [A_1] : k2_tarski(A_1,A_1) = k1_tarski(A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [A_4,B_5,C_6,D_7] : v1_relat_1(k2_tarski(k4_tarski(A_4,B_5),k4_tarski(C_6,D_7))) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    ! [A_8,B_9,C_10,D_11] :
      ( k1_relat_1(k2_tarski(k4_tarski(A_8,B_9),k4_tarski(C_10,D_11))) = k2_tarski(A_8,C_10)
      | ~ v1_relat_1(k2_tarski(k4_tarski(A_8,B_9),k4_tarski(C_10,D_11))) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_119,plain,(
    ! [A_56,B_57,C_58,D_59] : k1_relat_1(k2_tarski(k4_tarski(A_56,B_57),k4_tarski(C_58,D_59))) = k2_tarski(A_56,C_58) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_10])).

tff(c_135,plain,(
    ! [A_56,B_57] : k2_tarski(A_56,A_56) = k1_relat_1(k1_tarski(k4_tarski(A_56,B_57))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_119])).

tff(c_138,plain,(
    ! [A_56,B_57] : k1_relat_1(k1_tarski(k4_tarski(A_56,B_57))) = k1_tarski(A_56) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_135])).

tff(c_12,plain,(
    ! [A_13,B_14,C_15] : k4_tarski(k4_tarski(A_13,B_14),C_15) = k3_mcart_1(A_13,B_14,C_15) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_139,plain,(
    ! [A_60,B_61] : k1_relat_1(k1_tarski(k4_tarski(A_60,B_61))) = k1_tarski(A_60) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_135])).

tff(c_148,plain,(
    ! [A_13,B_14,C_15] : k1_relat_1(k1_tarski(k3_mcart_1(A_13,B_14,C_15))) = k1_tarski(k4_tarski(A_13,B_14)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_139])).

tff(c_14,plain,(
    k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1('#skF_1','#skF_2','#skF_3')))) != k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_151,plain,(
    k1_relat_1(k1_tarski(k4_tarski('#skF_1','#skF_2'))) != k1_tarski('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_14])).

tff(c_154,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_151])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n007.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 19:27:06 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.77/1.16  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.77/1.16  
% 1.77/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.77/1.16  %$ v1_relat_1 > k2_enumset1 > k3_mcart_1 > k4_tarski > k2_tarski > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 1.77/1.16  
% 1.77/1.16  %Foreground sorts:
% 1.77/1.16  
% 1.77/1.16  
% 1.77/1.16  %Background operators:
% 1.77/1.16  
% 1.77/1.16  
% 1.77/1.16  %Foreground operators:
% 1.77/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.77/1.16  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.77/1.16  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.77/1.16  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 1.77/1.16  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.77/1.16  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.77/1.16  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.77/1.16  tff('#skF_2', type, '#skF_2': $i).
% 1.77/1.16  tff('#skF_3', type, '#skF_3': $i).
% 1.77/1.16  tff('#skF_1', type, '#skF_1': $i).
% 1.77/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.77/1.16  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.77/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.77/1.16  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.77/1.16  
% 1.89/1.17  tff(f_27, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 1.89/1.17  tff(f_31, axiom, (![A, B, C, D]: v1_relat_1(k2_tarski(k4_tarski(A, B), k4_tarski(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc7_relat_1)).
% 1.89/1.17  tff(f_39, axiom, (![A, B, C, D, E]: (v1_relat_1(E) => ((E = k2_tarski(k4_tarski(A, B), k4_tarski(C, D))) => ((k1_relat_1(E) = k2_tarski(A, C)) & (k2_relat_1(E) = k2_tarski(B, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_relat_1)).
% 1.89/1.17  tff(f_41, axiom, (![A, B, C]: (k3_mcart_1(A, B, C) = k4_tarski(k4_tarski(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_mcart_1)).
% 1.89/1.17  tff(f_44, negated_conjecture, ~(![A, B, C]: (k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(A, B, C)))) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_mcart_1)).
% 1.89/1.17  tff(c_2, plain, (![A_1]: (k2_tarski(A_1, A_1)=k1_tarski(A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.89/1.17  tff(c_6, plain, (![A_4, B_5, C_6, D_7]: (v1_relat_1(k2_tarski(k4_tarski(A_4, B_5), k4_tarski(C_6, D_7))))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.89/1.17  tff(c_10, plain, (![A_8, B_9, C_10, D_11]: (k1_relat_1(k2_tarski(k4_tarski(A_8, B_9), k4_tarski(C_10, D_11)))=k2_tarski(A_8, C_10) | ~v1_relat_1(k2_tarski(k4_tarski(A_8, B_9), k4_tarski(C_10, D_11))))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.89/1.17  tff(c_119, plain, (![A_56, B_57, C_58, D_59]: (k1_relat_1(k2_tarski(k4_tarski(A_56, B_57), k4_tarski(C_58, D_59)))=k2_tarski(A_56, C_58))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_10])).
% 1.89/1.17  tff(c_135, plain, (![A_56, B_57]: (k2_tarski(A_56, A_56)=k1_relat_1(k1_tarski(k4_tarski(A_56, B_57))))), inference(superposition, [status(thm), theory('equality')], [c_2, c_119])).
% 1.89/1.17  tff(c_138, plain, (![A_56, B_57]: (k1_relat_1(k1_tarski(k4_tarski(A_56, B_57)))=k1_tarski(A_56))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_135])).
% 1.89/1.17  tff(c_12, plain, (![A_13, B_14, C_15]: (k4_tarski(k4_tarski(A_13, B_14), C_15)=k3_mcart_1(A_13, B_14, C_15))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.89/1.17  tff(c_139, plain, (![A_60, B_61]: (k1_relat_1(k1_tarski(k4_tarski(A_60, B_61)))=k1_tarski(A_60))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_135])).
% 1.89/1.17  tff(c_148, plain, (![A_13, B_14, C_15]: (k1_relat_1(k1_tarski(k3_mcart_1(A_13, B_14, C_15)))=k1_tarski(k4_tarski(A_13, B_14)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_139])).
% 1.89/1.17  tff(c_14, plain, (k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1('#skF_1', '#skF_2', '#skF_3'))))!=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.89/1.17  tff(c_151, plain, (k1_relat_1(k1_tarski(k4_tarski('#skF_1', '#skF_2')))!=k1_tarski('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_148, c_14])).
% 1.89/1.17  tff(c_154, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_138, c_151])).
% 1.89/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.89/1.17  
% 1.89/1.17  Inference rules
% 1.89/1.17  ----------------------
% 1.89/1.17  #Ref     : 0
% 1.89/1.17  #Sup     : 33
% 1.89/1.17  #Fact    : 0
% 1.89/1.17  #Define  : 0
% 1.89/1.17  #Split   : 0
% 1.89/1.17  #Chain   : 0
% 1.89/1.17  #Close   : 0
% 1.89/1.17  
% 1.89/1.17  Ordering : KBO
% 1.89/1.17  
% 1.89/1.17  Simplification rules
% 1.89/1.17  ----------------------
% 1.89/1.17  #Subsume      : 0
% 1.89/1.17  #Demod        : 8
% 1.89/1.17  #Tautology    : 18
% 1.89/1.17  #SimpNegUnit  : 0
% 1.89/1.17  #BackRed      : 1
% 1.89/1.17  
% 1.89/1.17  #Partial instantiations: 0
% 1.89/1.17  #Strategies tried      : 1
% 1.89/1.17  
% 1.89/1.17  Timing (in seconds)
% 1.89/1.17  ----------------------
% 1.89/1.17  Preprocessing        : 0.28
% 1.89/1.17  Parsing              : 0.15
% 1.89/1.17  CNF conversion       : 0.02
% 1.89/1.17  Main loop            : 0.12
% 1.89/1.17  Inferencing          : 0.05
% 1.89/1.17  Reduction            : 0.04
% 1.89/1.17  Demodulation         : 0.03
% 1.89/1.18  BG Simplification    : 0.01
% 1.89/1.18  Subsumption          : 0.01
% 1.89/1.18  Abstraction          : 0.01
% 1.89/1.18  MUC search           : 0.00
% 1.89/1.18  Cooper               : 0.00
% 1.89/1.18  Total                : 0.43
% 1.89/1.18  Index Insertion      : 0.00
% 1.89/1.18  Index Deletion       : 0.00
% 1.89/1.18  Index Matching       : 0.00
% 1.89/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
