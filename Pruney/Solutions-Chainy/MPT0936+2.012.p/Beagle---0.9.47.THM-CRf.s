%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:28 EST 2020

% Result     : Theorem 1.67s
% Output     : CNFRefutation 1.67s
% Verified   : 
% Statistics : Number of formulae       :   35 (  42 expanded)
%              Number of leaves         :   24 (  27 expanded)
%              Depth                    :    6
%              Number of atoms          :   20 (  31 expanded)
%              Number of equality atoms :   14 (  20 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k3_mcart_1 > k1_enumset1 > k4_tarski > k2_tarski > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_27,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C,D] : v1_relat_1(k2_tarski(k4_tarski(A,B),k4_tarski(C,D))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_relat_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( C = k1_tarski(k4_tarski(A,B))
       => ( k1_relat_1(C) = k1_tarski(A)
          & k2_relat_1(C) = k1_tarski(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_relat_1)).

tff(f_51,axiom,(
    ! [A,B,C] : k3_mcart_1(A,B,C) = k4_tarski(k4_tarski(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

tff(f_54,negated_conjecture,(
    ~ ! [A,B,C] : k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(A,B,C)))) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_mcart_1)).

tff(c_2,plain,(
    ! [A_1] : k2_tarski(A_1,A_1) = k1_tarski(A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_43,plain,(
    ! [A_42,B_43,C_44,D_45] : v1_relat_1(k2_tarski(k4_tarski(A_42,B_43),k4_tarski(C_44,D_45))) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_47,plain,(
    ! [A_42,B_43] : v1_relat_1(k1_tarski(k4_tarski(A_42,B_43))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_43])).

tff(c_20,plain,(
    ! [A_33,B_34] :
      ( k1_relat_1(k1_tarski(k4_tarski(A_33,B_34))) = k1_tarski(A_33)
      | ~ v1_relat_1(k1_tarski(k4_tarski(A_33,B_34))) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_103,plain,(
    ! [A_33,B_34] : k1_relat_1(k1_tarski(k4_tarski(A_33,B_34))) = k1_tarski(A_33) ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_20])).

tff(c_22,plain,(
    ! [A_36,B_37,C_38] : k4_tarski(k4_tarski(A_36,B_37),C_38) = k3_mcart_1(A_36,B_37,C_38) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_104,plain,(
    ! [A_77,B_78] : k1_relat_1(k1_tarski(k4_tarski(A_77,B_78))) = k1_tarski(A_77) ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_20])).

tff(c_113,plain,(
    ! [A_36,B_37,C_38] : k1_relat_1(k1_tarski(k3_mcart_1(A_36,B_37,C_38))) = k1_tarski(k4_tarski(A_36,B_37)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_104])).

tff(c_24,plain,(
    k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1('#skF_1','#skF_2','#skF_3')))) != k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_116,plain,(
    k1_relat_1(k1_tarski(k4_tarski('#skF_1','#skF_2'))) != k1_tarski('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_24])).

tff(c_119,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_116])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:30:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.67/1.15  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.67/1.16  
% 1.67/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.67/1.16  %$ v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k3_mcart_1 > k1_enumset1 > k4_tarski > k2_tarski > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 1.67/1.16  
% 1.67/1.16  %Foreground sorts:
% 1.67/1.16  
% 1.67/1.16  
% 1.67/1.16  %Background operators:
% 1.67/1.16  
% 1.67/1.16  
% 1.67/1.16  %Foreground operators:
% 1.67/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.67/1.16  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.67/1.16  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.67/1.16  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 1.67/1.16  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.67/1.16  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.67/1.16  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.67/1.16  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.67/1.16  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.67/1.16  tff('#skF_2', type, '#skF_2': $i).
% 1.67/1.16  tff('#skF_3', type, '#skF_3': $i).
% 1.67/1.16  tff('#skF_1', type, '#skF_1': $i).
% 1.67/1.16  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.67/1.16  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 1.67/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.67/1.16  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.67/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.67/1.16  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.67/1.16  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.67/1.16  
% 1.67/1.17  tff(f_27, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 1.67/1.17  tff(f_41, axiom, (![A, B, C, D]: v1_relat_1(k2_tarski(k4_tarski(A, B), k4_tarski(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc7_relat_1)).
% 1.67/1.17  tff(f_49, axiom, (![A, B, C]: (v1_relat_1(C) => ((C = k1_tarski(k4_tarski(A, B))) => ((k1_relat_1(C) = k1_tarski(A)) & (k2_relat_1(C) = k1_tarski(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_relat_1)).
% 1.67/1.17  tff(f_51, axiom, (![A, B, C]: (k3_mcart_1(A, B, C) = k4_tarski(k4_tarski(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_mcart_1)).
% 1.67/1.17  tff(f_54, negated_conjecture, ~(![A, B, C]: (k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(A, B, C)))) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_mcart_1)).
% 1.67/1.17  tff(c_2, plain, (![A_1]: (k2_tarski(A_1, A_1)=k1_tarski(A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.67/1.17  tff(c_43, plain, (![A_42, B_43, C_44, D_45]: (v1_relat_1(k2_tarski(k4_tarski(A_42, B_43), k4_tarski(C_44, D_45))))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.67/1.17  tff(c_47, plain, (![A_42, B_43]: (v1_relat_1(k1_tarski(k4_tarski(A_42, B_43))))), inference(superposition, [status(thm), theory('equality')], [c_2, c_43])).
% 1.67/1.17  tff(c_20, plain, (![A_33, B_34]: (k1_relat_1(k1_tarski(k4_tarski(A_33, B_34)))=k1_tarski(A_33) | ~v1_relat_1(k1_tarski(k4_tarski(A_33, B_34))))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.67/1.17  tff(c_103, plain, (![A_33, B_34]: (k1_relat_1(k1_tarski(k4_tarski(A_33, B_34)))=k1_tarski(A_33))), inference(demodulation, [status(thm), theory('equality')], [c_47, c_20])).
% 1.67/1.17  tff(c_22, plain, (![A_36, B_37, C_38]: (k4_tarski(k4_tarski(A_36, B_37), C_38)=k3_mcart_1(A_36, B_37, C_38))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.67/1.17  tff(c_104, plain, (![A_77, B_78]: (k1_relat_1(k1_tarski(k4_tarski(A_77, B_78)))=k1_tarski(A_77))), inference(demodulation, [status(thm), theory('equality')], [c_47, c_20])).
% 1.67/1.17  tff(c_113, plain, (![A_36, B_37, C_38]: (k1_relat_1(k1_tarski(k3_mcart_1(A_36, B_37, C_38)))=k1_tarski(k4_tarski(A_36, B_37)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_104])).
% 1.67/1.17  tff(c_24, plain, (k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1('#skF_1', '#skF_2', '#skF_3'))))!=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.67/1.17  tff(c_116, plain, (k1_relat_1(k1_tarski(k4_tarski('#skF_1', '#skF_2')))!=k1_tarski('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_113, c_24])).
% 1.67/1.17  tff(c_119, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_103, c_116])).
% 1.67/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.67/1.17  
% 1.67/1.17  Inference rules
% 1.67/1.17  ----------------------
% 1.67/1.17  #Ref     : 0
% 1.67/1.17  #Sup     : 22
% 1.67/1.17  #Fact    : 0
% 1.67/1.17  #Define  : 0
% 1.67/1.17  #Split   : 0
% 1.67/1.17  #Chain   : 0
% 1.67/1.17  #Close   : 0
% 1.67/1.17  
% 1.67/1.17  Ordering : KBO
% 1.67/1.17  
% 1.67/1.17  Simplification rules
% 1.67/1.17  ----------------------
% 1.67/1.17  #Subsume      : 0
% 1.67/1.17  #Demod        : 5
% 1.67/1.17  #Tautology    : 14
% 1.67/1.17  #SimpNegUnit  : 0
% 1.67/1.17  #BackRed      : 1
% 1.67/1.17  
% 1.67/1.17  #Partial instantiations: 0
% 1.67/1.17  #Strategies tried      : 1
% 1.67/1.17  
% 1.67/1.17  Timing (in seconds)
% 1.67/1.17  ----------------------
% 1.67/1.17  Preprocessing        : 0.31
% 1.67/1.17  Parsing              : 0.16
% 1.67/1.17  CNF conversion       : 0.02
% 1.67/1.17  Main loop            : 0.11
% 1.67/1.17  Inferencing          : 0.04
% 1.67/1.17  Reduction            : 0.04
% 1.67/1.17  Demodulation         : 0.03
% 1.67/1.17  BG Simplification    : 0.01
% 1.67/1.17  Subsumption          : 0.01
% 1.67/1.17  Abstraction          : 0.01
% 1.67/1.17  MUC search           : 0.00
% 1.67/1.17  Cooper               : 0.00
% 1.67/1.17  Total                : 0.44
% 1.67/1.17  Index Insertion      : 0.00
% 1.67/1.17  Index Deletion       : 0.00
% 1.67/1.17  Index Matching       : 0.00
% 1.67/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
