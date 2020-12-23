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
% DateTime   : Thu Dec  3 10:10:27 EST 2020

% Result     : Theorem 1.78s
% Output     : CNFRefutation 1.78s
% Verified   : 
% Statistics : Number of formulae       :   29 (  35 expanded)
%              Number of leaves         :   19 (  22 expanded)
%              Depth                    :    6
%              Number of atoms          :   18 (  28 expanded)
%              Number of equality atoms :   13 (  19 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_relat_1 > k3_mcart_1 > k4_tarski > k2_tarski > #nlpp > k2_relat_1 > k1_relat_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_27,axiom,(
    ! [A,B,C,D] : v1_relat_1(k2_tarski(k4_tarski(A,B),k4_tarski(C,D))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_relat_1)).

tff(f_35,axiom,(
    ! [A,B,C,D,E] :
      ( v1_relat_1(E)
     => ( E = k2_tarski(k4_tarski(A,B),k4_tarski(C,D))
       => ( k1_relat_1(E) = k2_tarski(A,C)
          & k2_relat_1(E) = k2_tarski(B,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_relat_1)).

tff(f_37,axiom,(
    ! [A,B,C] : k3_mcart_1(A,B,C) = k4_tarski(k4_tarski(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

tff(f_40,negated_conjecture,(
    ~ ! [A,B,C,D,E,F] : k1_relat_1(k1_relat_1(k2_tarski(k3_mcart_1(A,B,C),k3_mcart_1(D,E,F)))) = k2_tarski(A,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_mcart_1)).

tff(c_2,plain,(
    ! [A_1,B_2,C_3,D_4] : v1_relat_1(k2_tarski(k4_tarski(A_1,B_2),k4_tarski(C_3,D_4))) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [A_5,B_6,C_7,D_8] :
      ( k1_relat_1(k2_tarski(k4_tarski(A_5,B_6),k4_tarski(C_7,D_8))) = k2_tarski(A_5,C_7)
      | ~ v1_relat_1(k2_tarski(k4_tarski(A_5,B_6),k4_tarski(C_7,D_8))) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [A_5,B_6,C_7,D_8] : k1_relat_1(k2_tarski(k4_tarski(A_5,B_6),k4_tarski(C_7,D_8))) = k2_tarski(A_5,C_7) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_6])).

tff(c_8,plain,(
    ! [A_10,B_11,C_12] : k4_tarski(k4_tarski(A_10,B_11),C_12) = k3_mcart_1(A_10,B_11,C_12) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_42,plain,(
    ! [A_36,B_37,C_38,D_39] : k1_relat_1(k2_tarski(k4_tarski(A_36,B_37),k4_tarski(C_38,D_39))) = k2_tarski(A_36,C_38) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_6])).

tff(c_149,plain,(
    ! [C_67,A_66,B_64,C_68,D_65] : k1_relat_1(k2_tarski(k3_mcart_1(A_66,B_64,C_68),k4_tarski(C_67,D_65))) = k2_tarski(k4_tarski(A_66,B_64),C_67) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_42])).

tff(c_161,plain,(
    ! [B_11,A_10,C_12,A_66,B_64,C_68] : k1_relat_1(k2_tarski(k3_mcart_1(A_66,B_64,C_68),k3_mcart_1(A_10,B_11,C_12))) = k2_tarski(k4_tarski(A_66,B_64),k4_tarski(A_10,B_11)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_149])).

tff(c_10,plain,(
    k1_relat_1(k1_relat_1(k2_tarski(k3_mcart_1('#skF_1','#skF_2','#skF_3'),k3_mcart_1('#skF_4','#skF_5','#skF_6')))) != k2_tarski('#skF_1','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_181,plain,(
    k1_relat_1(k2_tarski(k4_tarski('#skF_1','#skF_2'),k4_tarski('#skF_4','#skF_5'))) != k2_tarski('#skF_1','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_10])).

tff(c_184,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_181])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:38:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.78/1.13  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.78/1.13  
% 1.78/1.13  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.78/1.14  %$ v1_relat_1 > k3_mcart_1 > k4_tarski > k2_tarski > #nlpp > k2_relat_1 > k1_relat_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.78/1.14  
% 1.78/1.14  %Foreground sorts:
% 1.78/1.14  
% 1.78/1.14  
% 1.78/1.14  %Background operators:
% 1.78/1.14  
% 1.78/1.14  
% 1.78/1.14  %Foreground operators:
% 1.78/1.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.78/1.14  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.78/1.14  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 1.78/1.14  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.78/1.14  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.78/1.14  tff('#skF_5', type, '#skF_5': $i).
% 1.78/1.14  tff('#skF_6', type, '#skF_6': $i).
% 1.78/1.14  tff('#skF_2', type, '#skF_2': $i).
% 1.78/1.14  tff('#skF_3', type, '#skF_3': $i).
% 1.78/1.14  tff('#skF_1', type, '#skF_1': $i).
% 1.78/1.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.78/1.14  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.78/1.14  tff('#skF_4', type, '#skF_4': $i).
% 1.78/1.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.78/1.14  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.78/1.14  
% 1.78/1.15  tff(f_27, axiom, (![A, B, C, D]: v1_relat_1(k2_tarski(k4_tarski(A, B), k4_tarski(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc7_relat_1)).
% 1.78/1.15  tff(f_35, axiom, (![A, B, C, D, E]: (v1_relat_1(E) => ((E = k2_tarski(k4_tarski(A, B), k4_tarski(C, D))) => ((k1_relat_1(E) = k2_tarski(A, C)) & (k2_relat_1(E) = k2_tarski(B, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_relat_1)).
% 1.78/1.15  tff(f_37, axiom, (![A, B, C]: (k3_mcart_1(A, B, C) = k4_tarski(k4_tarski(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_mcart_1)).
% 1.78/1.15  tff(f_40, negated_conjecture, ~(![A, B, C, D, E, F]: (k1_relat_1(k1_relat_1(k2_tarski(k3_mcart_1(A, B, C), k3_mcart_1(D, E, F)))) = k2_tarski(A, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t96_mcart_1)).
% 1.78/1.15  tff(c_2, plain, (![A_1, B_2, C_3, D_4]: (v1_relat_1(k2_tarski(k4_tarski(A_1, B_2), k4_tarski(C_3, D_4))))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.78/1.15  tff(c_6, plain, (![A_5, B_6, C_7, D_8]: (k1_relat_1(k2_tarski(k4_tarski(A_5, B_6), k4_tarski(C_7, D_8)))=k2_tarski(A_5, C_7) | ~v1_relat_1(k2_tarski(k4_tarski(A_5, B_6), k4_tarski(C_7, D_8))))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.78/1.15  tff(c_12, plain, (![A_5, B_6, C_7, D_8]: (k1_relat_1(k2_tarski(k4_tarski(A_5, B_6), k4_tarski(C_7, D_8)))=k2_tarski(A_5, C_7))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_6])).
% 1.78/1.15  tff(c_8, plain, (![A_10, B_11, C_12]: (k4_tarski(k4_tarski(A_10, B_11), C_12)=k3_mcart_1(A_10, B_11, C_12))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.78/1.15  tff(c_42, plain, (![A_36, B_37, C_38, D_39]: (k1_relat_1(k2_tarski(k4_tarski(A_36, B_37), k4_tarski(C_38, D_39)))=k2_tarski(A_36, C_38))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_6])).
% 1.78/1.15  tff(c_149, plain, (![C_67, A_66, B_64, C_68, D_65]: (k1_relat_1(k2_tarski(k3_mcart_1(A_66, B_64, C_68), k4_tarski(C_67, D_65)))=k2_tarski(k4_tarski(A_66, B_64), C_67))), inference(superposition, [status(thm), theory('equality')], [c_8, c_42])).
% 1.78/1.15  tff(c_161, plain, (![B_11, A_10, C_12, A_66, B_64, C_68]: (k1_relat_1(k2_tarski(k3_mcart_1(A_66, B_64, C_68), k3_mcart_1(A_10, B_11, C_12)))=k2_tarski(k4_tarski(A_66, B_64), k4_tarski(A_10, B_11)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_149])).
% 1.78/1.15  tff(c_10, plain, (k1_relat_1(k1_relat_1(k2_tarski(k3_mcart_1('#skF_1', '#skF_2', '#skF_3'), k3_mcart_1('#skF_4', '#skF_5', '#skF_6'))))!=k2_tarski('#skF_1', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.78/1.15  tff(c_181, plain, (k1_relat_1(k2_tarski(k4_tarski('#skF_1', '#skF_2'), k4_tarski('#skF_4', '#skF_5')))!=k2_tarski('#skF_1', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_161, c_10])).
% 1.78/1.15  tff(c_184, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_181])).
% 1.78/1.15  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.78/1.15  
% 1.78/1.15  Inference rules
% 1.78/1.15  ----------------------
% 1.78/1.15  #Ref     : 0
% 1.78/1.15  #Sup     : 43
% 1.78/1.15  #Fact    : 0
% 1.78/1.15  #Define  : 0
% 1.78/1.15  #Split   : 0
% 1.78/1.15  #Chain   : 0
% 1.78/1.15  #Close   : 0
% 1.78/1.15  
% 1.78/1.15  Ordering : KBO
% 1.78/1.15  
% 1.78/1.15  Simplification rules
% 1.78/1.15  ----------------------
% 1.78/1.15  #Subsume      : 0
% 1.78/1.15  #Demod        : 21
% 1.78/1.15  #Tautology    : 32
% 1.78/1.15  #SimpNegUnit  : 0
% 1.78/1.15  #BackRed      : 1
% 1.78/1.15  
% 1.78/1.15  #Partial instantiations: 0
% 1.78/1.15  #Strategies tried      : 1
% 1.78/1.15  
% 1.78/1.15  Timing (in seconds)
% 1.78/1.15  ----------------------
% 1.78/1.15  Preprocessing        : 0.24
% 1.78/1.15  Parsing              : 0.13
% 1.78/1.15  CNF conversion       : 0.01
% 1.78/1.15  Main loop            : 0.15
% 1.78/1.15  Inferencing          : 0.07
% 1.78/1.15  Reduction            : 0.04
% 1.78/1.15  Demodulation         : 0.03
% 1.78/1.15  BG Simplification    : 0.01
% 1.78/1.15  Subsumption          : 0.02
% 1.78/1.15  Abstraction          : 0.01
% 1.78/1.15  MUC search           : 0.00
% 1.78/1.15  Cooper               : 0.00
% 1.78/1.15  Total                : 0.42
% 1.78/1.15  Index Insertion      : 0.00
% 1.78/1.15  Index Deletion       : 0.00
% 1.78/1.15  Index Matching       : 0.00
% 1.78/1.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
