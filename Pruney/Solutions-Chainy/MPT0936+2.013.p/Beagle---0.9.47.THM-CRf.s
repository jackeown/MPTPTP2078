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
% DateTime   : Thu Dec  3 10:10:28 EST 2020

% Result     : Theorem 1.85s
% Output     : CNFRefutation 1.93s
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
%$ v1_relat_1 > k3_mcart_1 > k1_enumset1 > k4_tarski > k2_tarski > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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
% 0.07/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.36  % Computer   : n022.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 10:16:41 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.37  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.85/1.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.22  
% 1.93/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.22  %$ v1_relat_1 > k3_mcart_1 > k1_enumset1 > k4_tarski > k2_tarski > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 1.93/1.22  
% 1.93/1.22  %Foreground sorts:
% 1.93/1.22  
% 1.93/1.22  
% 1.93/1.22  %Background operators:
% 1.93/1.22  
% 1.93/1.22  
% 1.93/1.22  %Foreground operators:
% 1.93/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.93/1.22  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.93/1.22  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.93/1.22  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 1.93/1.22  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.93/1.22  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.93/1.22  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.93/1.22  tff('#skF_2', type, '#skF_2': $i).
% 1.93/1.22  tff('#skF_3', type, '#skF_3': $i).
% 1.93/1.22  tff('#skF_1', type, '#skF_1': $i).
% 1.93/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.93/1.22  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.93/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.93/1.22  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.93/1.22  
% 1.93/1.24  tff(f_27, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 1.93/1.24  tff(f_31, axiom, (![A, B, C, D]: v1_relat_1(k2_tarski(k4_tarski(A, B), k4_tarski(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc7_relat_1)).
% 1.93/1.24  tff(f_39, axiom, (![A, B, C, D, E]: (v1_relat_1(E) => ((E = k2_tarski(k4_tarski(A, B), k4_tarski(C, D))) => ((k1_relat_1(E) = k2_tarski(A, C)) & (k2_relat_1(E) = k2_tarski(B, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_relat_1)).
% 1.93/1.24  tff(f_41, axiom, (![A, B, C]: (k3_mcart_1(A, B, C) = k4_tarski(k4_tarski(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_mcart_1)).
% 1.93/1.24  tff(f_44, negated_conjecture, ~(![A, B, C]: (k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(A, B, C)))) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_mcart_1)).
% 1.93/1.24  tff(c_2, plain, (![A_1]: (k2_tarski(A_1, A_1)=k1_tarski(A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.93/1.24  tff(c_6, plain, (![A_4, B_5, C_6, D_7]: (v1_relat_1(k2_tarski(k4_tarski(A_4, B_5), k4_tarski(C_6, D_7))))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.93/1.24  tff(c_10, plain, (![A_8, B_9, C_10, D_11]: (k1_relat_1(k2_tarski(k4_tarski(A_8, B_9), k4_tarski(C_10, D_11)))=k2_tarski(A_8, C_10) | ~v1_relat_1(k2_tarski(k4_tarski(A_8, B_9), k4_tarski(C_10, D_11))))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.93/1.24  tff(c_119, plain, (![A_56, B_57, C_58, D_59]: (k1_relat_1(k2_tarski(k4_tarski(A_56, B_57), k4_tarski(C_58, D_59)))=k2_tarski(A_56, C_58))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_10])).
% 1.93/1.24  tff(c_135, plain, (![A_56, B_57]: (k2_tarski(A_56, A_56)=k1_relat_1(k1_tarski(k4_tarski(A_56, B_57))))), inference(superposition, [status(thm), theory('equality')], [c_2, c_119])).
% 1.93/1.24  tff(c_138, plain, (![A_56, B_57]: (k1_relat_1(k1_tarski(k4_tarski(A_56, B_57)))=k1_tarski(A_56))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_135])).
% 1.93/1.24  tff(c_12, plain, (![A_13, B_14, C_15]: (k4_tarski(k4_tarski(A_13, B_14), C_15)=k3_mcart_1(A_13, B_14, C_15))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.93/1.24  tff(c_139, plain, (![A_60, B_61]: (k1_relat_1(k1_tarski(k4_tarski(A_60, B_61)))=k1_tarski(A_60))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_135])).
% 1.93/1.24  tff(c_148, plain, (![A_13, B_14, C_15]: (k1_relat_1(k1_tarski(k3_mcart_1(A_13, B_14, C_15)))=k1_tarski(k4_tarski(A_13, B_14)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_139])).
% 1.93/1.24  tff(c_14, plain, (k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1('#skF_1', '#skF_2', '#skF_3'))))!=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.93/1.24  tff(c_151, plain, (k1_relat_1(k1_tarski(k4_tarski('#skF_1', '#skF_2')))!=k1_tarski('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_148, c_14])).
% 1.93/1.24  tff(c_154, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_138, c_151])).
% 1.93/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.24  
% 1.93/1.24  Inference rules
% 1.93/1.24  ----------------------
% 1.93/1.24  #Ref     : 0
% 1.93/1.24  #Sup     : 33
% 1.93/1.24  #Fact    : 0
% 1.93/1.24  #Define  : 0
% 1.93/1.24  #Split   : 0
% 1.93/1.24  #Chain   : 0
% 1.93/1.24  #Close   : 0
% 1.93/1.24  
% 1.93/1.24  Ordering : KBO
% 1.93/1.24  
% 1.93/1.24  Simplification rules
% 1.93/1.24  ----------------------
% 1.93/1.24  #Subsume      : 0
% 1.93/1.24  #Demod        : 8
% 1.93/1.24  #Tautology    : 18
% 1.93/1.24  #SimpNegUnit  : 0
% 1.93/1.24  #BackRed      : 1
% 1.93/1.24  
% 1.93/1.24  #Partial instantiations: 0
% 1.93/1.24  #Strategies tried      : 1
% 1.93/1.24  
% 1.93/1.24  Timing (in seconds)
% 1.93/1.24  ----------------------
% 1.93/1.24  Preprocessing        : 0.28
% 1.93/1.24  Parsing              : 0.15
% 1.93/1.24  CNF conversion       : 0.02
% 1.93/1.24  Main loop            : 0.17
% 1.93/1.24  Inferencing          : 0.07
% 1.93/1.24  Reduction            : 0.05
% 1.93/1.24  Demodulation         : 0.04
% 1.93/1.24  BG Simplification    : 0.01
% 1.93/1.24  Subsumption          : 0.02
% 1.93/1.24  Abstraction          : 0.01
% 1.93/1.24  MUC search           : 0.00
% 1.93/1.24  Cooper               : 0.00
% 1.93/1.24  Total                : 0.48
% 1.93/1.24  Index Insertion      : 0.00
% 1.93/1.24  Index Deletion       : 0.00
% 1.93/1.24  Index Matching       : 0.00
% 1.93/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
