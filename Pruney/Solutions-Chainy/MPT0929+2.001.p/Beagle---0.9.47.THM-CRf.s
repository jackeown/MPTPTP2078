%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:25 EST 2020

% Result     : Theorem 1.64s
% Output     : CNFRefutation 1.64s
% Verified   : 
% Statistics : Number of formulae       :   43 (  55 expanded)
%              Number of leaves         :   28 (  35 expanded)
%              Depth                    :    5
%              Number of atoms          :   28 (  47 expanded)
%              Number of equality atoms :   27 (  46 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k4_tarski > #nlpp > k2_mcart_1 > k20_mcart_1 > k1_mcart_1 > k19_mcart_1 > k18_mcart_1 > k17_mcart_1 > #skF_11 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_9 > #skF_8 > #skF_4 > #skF_12

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k17_mcart_1,type,(
    k17_mcart_1: $i > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

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

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k20_mcart_1,type,(
    k20_mcart_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k18_mcart_1,type,(
    k18_mcart_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(k19_mcart_1,type,(
    k19_mcart_1: $i > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff(f_37,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_31,axiom,(
    ! [A] : k19_mcart_1(A) = k1_mcart_1(k2_mcart_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_mcart_1)).

tff(f_33,axiom,(
    ! [A] : k20_mcart_1(A) = k2_mcart_1(k2_mcart_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d17_mcart_1)).

tff(f_29,axiom,(
    ! [A] : k18_mcart_1(A) = k2_mcart_1(k1_mcart_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d15_mcart_1)).

tff(f_27,axiom,(
    ! [A] : k17_mcart_1(A) = k1_mcart_1(k1_mcart_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d14_mcart_1)).

tff(f_46,negated_conjecture,(
    ~ ! [A,B,C,D,E,F] :
        ( k17_mcart_1(k4_tarski(k4_tarski(A,B),C)) = A
        & k18_mcart_1(k4_tarski(k4_tarski(A,B),C)) = B
        & k19_mcart_1(k4_tarski(F,k4_tarski(D,E))) = D
        & k20_mcart_1(k4_tarski(F,k4_tarski(D,E))) = E ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t89_mcart_1)).

tff(c_10,plain,(
    ! [A_5,B_6] : k1_mcart_1(k4_tarski(A_5,B_6)) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_12,plain,(
    ! [A_5,B_6] : k2_mcart_1(k4_tarski(A_5,B_6)) = B_6 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_72,plain,(
    ! [A_12] : k1_mcart_1(k2_mcart_1(A_12)) = k19_mcart_1(A_12) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_93,plain,(
    ! [A_5,B_6] : k19_mcart_1(k4_tarski(A_5,B_6)) = k1_mcart_1(B_6) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_72])).

tff(c_51,plain,(
    ! [A_11] : k2_mcart_1(k2_mcart_1(A_11)) = k20_mcart_1(A_11) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_69,plain,(
    ! [A_5,B_6] : k20_mcart_1(k4_tarski(A_5,B_6)) = k2_mcart_1(B_6) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_51])).

tff(c_96,plain,(
    ! [A_13,B_14] : k1_mcart_1(k4_tarski(A_13,B_14)) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_4,plain,(
    ! [A_2] : k2_mcart_1(k1_mcart_1(A_2)) = k18_mcart_1(A_2) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_102,plain,(
    ! [A_13,B_14] : k18_mcart_1(k4_tarski(A_13,B_14)) = k2_mcart_1(A_13) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_4])).

tff(c_2,plain,(
    ! [A_1] : k1_mcart_1(k1_mcart_1(A_1)) = k17_mcart_1(A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_105,plain,(
    ! [A_13,B_14] : k17_mcart_1(k4_tarski(A_13,B_14)) = k1_mcart_1(A_13) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_2])).

tff(c_14,plain,
    ( k17_mcart_1(k4_tarski(k4_tarski('#skF_10','#skF_11'),'#skF_12')) != '#skF_10'
    | k18_mcart_1(k4_tarski(k4_tarski('#skF_7','#skF_8'),'#skF_9')) != '#skF_8'
    | k19_mcart_1(k4_tarski('#skF_6',k4_tarski('#skF_4','#skF_5'))) != '#skF_4'
    | k20_mcart_1(k4_tarski('#skF_3',k4_tarski('#skF_1','#skF_2'))) != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_139,plain,(
    k19_mcart_1(k4_tarski('#skF_6',k4_tarski('#skF_4','#skF_5'))) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_69,c_12,c_102,c_10,c_105,c_14])).

tff(c_140,plain,(
    k1_mcart_1(k4_tarski('#skF_4','#skF_5')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_139])).

tff(c_143,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_140])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:18:44 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.64/1.12  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.64/1.12  
% 1.64/1.12  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.64/1.13  %$ k4_tarski > #nlpp > k2_mcart_1 > k20_mcart_1 > k1_mcart_1 > k19_mcart_1 > k18_mcart_1 > k17_mcart_1 > #skF_11 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_9 > #skF_8 > #skF_4 > #skF_12
% 1.64/1.13  
% 1.64/1.13  %Foreground sorts:
% 1.64/1.13  
% 1.64/1.13  
% 1.64/1.13  %Background operators:
% 1.64/1.13  
% 1.64/1.13  
% 1.64/1.13  %Foreground operators:
% 1.64/1.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.64/1.13  tff('#skF_11', type, '#skF_11': $i).
% 1.64/1.13  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.64/1.13  tff(k17_mcart_1, type, k17_mcart_1: $i > $i).
% 1.64/1.13  tff('#skF_7', type, '#skF_7': $i).
% 1.64/1.13  tff('#skF_10', type, '#skF_10': $i).
% 1.64/1.13  tff('#skF_5', type, '#skF_5': $i).
% 1.64/1.13  tff('#skF_6', type, '#skF_6': $i).
% 1.64/1.13  tff('#skF_2', type, '#skF_2': $i).
% 1.64/1.13  tff('#skF_3', type, '#skF_3': $i).
% 1.64/1.13  tff('#skF_1', type, '#skF_1': $i).
% 1.64/1.13  tff('#skF_9', type, '#skF_9': $i).
% 1.64/1.13  tff('#skF_8', type, '#skF_8': $i).
% 1.64/1.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.64/1.13  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 1.64/1.13  tff(k20_mcart_1, type, k20_mcart_1: $i > $i).
% 1.64/1.13  tff('#skF_4', type, '#skF_4': $i).
% 1.64/1.13  tff(k18_mcart_1, type, k18_mcart_1: $i > $i).
% 1.64/1.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.64/1.13  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 1.64/1.13  tff(k19_mcart_1, type, k19_mcart_1: $i > $i).
% 1.64/1.13  tff('#skF_12', type, '#skF_12': $i).
% 1.64/1.13  
% 1.64/1.14  tff(f_37, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_mcart_1)).
% 1.64/1.14  tff(f_31, axiom, (![A]: (k19_mcart_1(A) = k1_mcart_1(k2_mcart_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_mcart_1)).
% 1.64/1.14  tff(f_33, axiom, (![A]: (k20_mcart_1(A) = k2_mcart_1(k2_mcart_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d17_mcart_1)).
% 1.64/1.14  tff(f_29, axiom, (![A]: (k18_mcart_1(A) = k2_mcart_1(k1_mcart_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d15_mcart_1)).
% 1.64/1.14  tff(f_27, axiom, (![A]: (k17_mcart_1(A) = k1_mcart_1(k1_mcart_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d14_mcart_1)).
% 1.64/1.14  tff(f_46, negated_conjecture, ~(![A, B, C, D, E, F]: ((((k17_mcart_1(k4_tarski(k4_tarski(A, B), C)) = A) & (k18_mcart_1(k4_tarski(k4_tarski(A, B), C)) = B)) & (k19_mcart_1(k4_tarski(F, k4_tarski(D, E))) = D)) & (k20_mcart_1(k4_tarski(F, k4_tarski(D, E))) = E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t89_mcart_1)).
% 1.64/1.14  tff(c_10, plain, (![A_5, B_6]: (k1_mcart_1(k4_tarski(A_5, B_6))=A_5)), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.64/1.14  tff(c_12, plain, (![A_5, B_6]: (k2_mcart_1(k4_tarski(A_5, B_6))=B_6)), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.64/1.14  tff(c_72, plain, (![A_12]: (k1_mcart_1(k2_mcart_1(A_12))=k19_mcart_1(A_12))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.64/1.14  tff(c_93, plain, (![A_5, B_6]: (k19_mcart_1(k4_tarski(A_5, B_6))=k1_mcart_1(B_6))), inference(superposition, [status(thm), theory('equality')], [c_12, c_72])).
% 1.64/1.14  tff(c_51, plain, (![A_11]: (k2_mcart_1(k2_mcart_1(A_11))=k20_mcart_1(A_11))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.64/1.14  tff(c_69, plain, (![A_5, B_6]: (k20_mcart_1(k4_tarski(A_5, B_6))=k2_mcart_1(B_6))), inference(superposition, [status(thm), theory('equality')], [c_12, c_51])).
% 1.64/1.14  tff(c_96, plain, (![A_13, B_14]: (k1_mcart_1(k4_tarski(A_13, B_14))=A_13)), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.64/1.14  tff(c_4, plain, (![A_2]: (k2_mcart_1(k1_mcart_1(A_2))=k18_mcart_1(A_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.64/1.14  tff(c_102, plain, (![A_13, B_14]: (k18_mcart_1(k4_tarski(A_13, B_14))=k2_mcart_1(A_13))), inference(superposition, [status(thm), theory('equality')], [c_96, c_4])).
% 1.64/1.14  tff(c_2, plain, (![A_1]: (k1_mcart_1(k1_mcart_1(A_1))=k17_mcart_1(A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.64/1.14  tff(c_105, plain, (![A_13, B_14]: (k17_mcart_1(k4_tarski(A_13, B_14))=k1_mcart_1(A_13))), inference(superposition, [status(thm), theory('equality')], [c_96, c_2])).
% 1.64/1.14  tff(c_14, plain, (k17_mcart_1(k4_tarski(k4_tarski('#skF_10', '#skF_11'), '#skF_12'))!='#skF_10' | k18_mcart_1(k4_tarski(k4_tarski('#skF_7', '#skF_8'), '#skF_9'))!='#skF_8' | k19_mcart_1(k4_tarski('#skF_6', k4_tarski('#skF_4', '#skF_5')))!='#skF_4' | k20_mcart_1(k4_tarski('#skF_3', k4_tarski('#skF_1', '#skF_2')))!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.64/1.14  tff(c_139, plain, (k19_mcart_1(k4_tarski('#skF_6', k4_tarski('#skF_4', '#skF_5')))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_12, c_69, c_12, c_102, c_10, c_105, c_14])).
% 1.64/1.14  tff(c_140, plain, (k1_mcart_1(k4_tarski('#skF_4', '#skF_5'))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_93, c_139])).
% 1.64/1.14  tff(c_143, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_140])).
% 1.64/1.14  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.64/1.14  
% 1.64/1.14  Inference rules
% 1.64/1.14  ----------------------
% 1.64/1.14  #Ref     : 0
% 1.64/1.14  #Sup     : 32
% 1.64/1.14  #Fact    : 0
% 1.64/1.14  #Define  : 0
% 1.64/1.14  #Split   : 0
% 1.64/1.14  #Chain   : 0
% 1.64/1.14  #Close   : 0
% 1.64/1.14  
% 1.64/1.14  Ordering : KBO
% 1.64/1.14  
% 1.64/1.14  Simplification rules
% 1.64/1.14  ----------------------
% 1.64/1.14  #Subsume      : 0
% 1.64/1.14  #Demod        : 8
% 1.64/1.14  #Tautology    : 18
% 1.64/1.14  #SimpNegUnit  : 0
% 1.64/1.14  #BackRed      : 1
% 1.64/1.14  
% 1.64/1.14  #Partial instantiations: 0
% 1.64/1.14  #Strategies tried      : 1
% 1.64/1.14  
% 1.64/1.14  Timing (in seconds)
% 1.64/1.14  ----------------------
% 1.64/1.14  Preprocessing        : 0.25
% 1.64/1.14  Parsing              : 0.14
% 1.64/1.14  CNF conversion       : 0.02
% 1.64/1.14  Main loop            : 0.11
% 1.64/1.14  Inferencing          : 0.05
% 1.64/1.14  Reduction            : 0.03
% 1.64/1.14  Demodulation         : 0.03
% 1.64/1.14  BG Simplification    : 0.01
% 1.64/1.14  Subsumption          : 0.01
% 1.64/1.14  Abstraction          : 0.01
% 1.64/1.14  MUC search           : 0.00
% 1.64/1.14  Cooper               : 0.00
% 1.64/1.14  Total                : 0.39
% 1.64/1.14  Index Insertion      : 0.00
% 1.64/1.14  Index Deletion       : 0.00
% 1.64/1.14  Index Matching       : 0.00
% 1.64/1.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
