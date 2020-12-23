%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:50 EST 2020

% Result     : Theorem 1.48s
% Output     : CNFRefutation 1.48s
% Verified   : 
% Statistics : Number of formulae       :   18 (  24 expanded)
%              Number of leaves         :   11 (  15 expanded)
%              Depth                    :    3
%              Number of atoms          :   11 (  21 expanded)
%              Number of equality atoms :   10 (  20 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k4_tarski > #nlpp > k2_mcart_1 > k1_mcart_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(f_35,negated_conjecture,(
    ~ ! [A] :
        ( ? [B,C] : A = k4_tarski(B,C)
       => k4_tarski(k1_mcart_1(A),k2_mcart_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_mcart_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

tff(c_8,plain,(
    k4_tarski('#skF_2','#skF_3') = '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_29,plain,(
    ! [A_7,B_8] : k2_mcart_1(k4_tarski(A_7,B_8)) = B_8 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_38,plain,(
    k2_mcart_1('#skF_1') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_29])).

tff(c_13,plain,(
    ! [A_5,B_6] : k1_mcart_1(k4_tarski(A_5,B_6)) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_22,plain,(
    k1_mcart_1('#skF_1') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_13])).

tff(c_6,plain,(
    k4_tarski(k1_mcart_1('#skF_1'),k2_mcart_1('#skF_1')) != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_46,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_38,c_22,c_6])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:26:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.48/1.07  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.48/1.07  
% 1.48/1.07  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.48/1.08  %$ k4_tarski > #nlpp > k2_mcart_1 > k1_mcart_1 > #skF_2 > #skF_3 > #skF_1
% 1.48/1.08  
% 1.48/1.08  %Foreground sorts:
% 1.48/1.08  
% 1.48/1.08  
% 1.48/1.08  %Background operators:
% 1.48/1.08  
% 1.48/1.08  
% 1.48/1.08  %Foreground operators:
% 1.48/1.08  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.48/1.08  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.48/1.08  tff('#skF_2', type, '#skF_2': $i).
% 1.48/1.08  tff('#skF_3', type, '#skF_3': $i).
% 1.48/1.08  tff('#skF_1', type, '#skF_1': $i).
% 1.48/1.08  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.48/1.08  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 1.48/1.08  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.48/1.08  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 1.48/1.08  
% 1.48/1.08  tff(f_35, negated_conjecture, ~(![A]: ((?[B, C]: (A = k4_tarski(B, C))) => (k4_tarski(k1_mcart_1(A), k2_mcart_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_mcart_1)).
% 1.48/1.08  tff(f_29, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_mcart_1)).
% 1.48/1.08  tff(c_8, plain, (k4_tarski('#skF_2', '#skF_3')='#skF_1'), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.48/1.08  tff(c_29, plain, (![A_7, B_8]: (k2_mcart_1(k4_tarski(A_7, B_8))=B_8)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.48/1.08  tff(c_38, plain, (k2_mcart_1('#skF_1')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_8, c_29])).
% 1.48/1.08  tff(c_13, plain, (![A_5, B_6]: (k1_mcart_1(k4_tarski(A_5, B_6))=A_5)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.48/1.08  tff(c_22, plain, (k1_mcart_1('#skF_1')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_8, c_13])).
% 1.48/1.08  tff(c_6, plain, (k4_tarski(k1_mcart_1('#skF_1'), k2_mcart_1('#skF_1'))!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.48/1.08  tff(c_46, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_38, c_22, c_6])).
% 1.48/1.08  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.48/1.08  
% 1.48/1.09  Inference rules
% 1.48/1.09  ----------------------
% 1.48/1.09  #Ref     : 0
% 1.48/1.09  #Sup     : 12
% 1.48/1.09  #Fact    : 0
% 1.48/1.09  #Define  : 0
% 1.48/1.09  #Split   : 0
% 1.48/1.09  #Chain   : 0
% 1.48/1.09  #Close   : 0
% 1.48/1.09  
% 1.48/1.09  Ordering : KBO
% 1.48/1.09  
% 1.48/1.09  Simplification rules
% 1.48/1.09  ----------------------
% 1.48/1.09  #Subsume      : 0
% 1.48/1.09  #Demod        : 3
% 1.48/1.09  #Tautology    : 10
% 1.48/1.09  #SimpNegUnit  : 0
% 1.48/1.09  #BackRed      : 0
% 1.48/1.09  
% 1.48/1.09  #Partial instantiations: 0
% 1.48/1.09  #Strategies tried      : 1
% 1.48/1.09  
% 1.48/1.09  Timing (in seconds)
% 1.48/1.09  ----------------------
% 1.60/1.09  Preprocessing        : 0.25
% 1.60/1.09  Parsing              : 0.14
% 1.60/1.09  CNF conversion       : 0.01
% 1.60/1.09  Main loop            : 0.05
% 1.60/1.09  Inferencing          : 0.02
% 1.60/1.09  Reduction            : 0.02
% 1.60/1.09  Demodulation         : 0.02
% 1.60/1.09  BG Simplification    : 0.01
% 1.60/1.09  Subsumption          : 0.00
% 1.60/1.09  Abstraction          : 0.00
% 1.60/1.09  MUC search           : 0.00
% 1.60/1.09  Cooper               : 0.00
% 1.60/1.09  Total                : 0.33
% 1.60/1.09  Index Insertion      : 0.00
% 1.60/1.09  Index Deletion       : 0.00
% 1.60/1.09  Index Matching       : 0.00
% 1.60/1.09  BG Taut test         : 0.00
%------------------------------------------------------------------------------
