%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:06 EST 2020

% Result     : Theorem 1.63s
% Output     : CNFRefutation 1.83s
% Verified   : 
% Statistics : Number of formulae       :   47 (  83 expanded)
%              Number of leaves         :   20 (  37 expanded)
%              Depth                    :    6
%              Number of atoms          :   47 ( 131 expanded)
%              Number of equality atoms :   37 ( 102 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(f_53,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r2_hidden(A,k2_zfmisc_1(k1_tarski(B),k2_tarski(C,D)))
       => ( k1_mcart_1(A) = B
          & ( k2_mcart_1(A) = C
            | k2_mcart_1(A) = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_mcart_1)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k1_tarski(A),k2_tarski(B,C)) = k2_tarski(k4_tarski(A,B),k4_tarski(A,C))
      & k2_zfmisc_1(k2_tarski(A,B),k1_tarski(C)) = k2_tarski(k4_tarski(A,C),k4_tarski(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_44,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

tff(c_32,plain,
    ( k2_mcart_1('#skF_3') != '#skF_6'
    | k1_mcart_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_73,plain,(
    k1_mcart_1('#skF_3') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_22,plain,(
    ! [A_8,B_9,C_10] : k2_zfmisc_1(k1_tarski(A_8),k2_tarski(B_9,C_10)) = k2_tarski(k4_tarski(A_8,B_9),k4_tarski(A_8,C_10)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_30,plain,(
    r2_hidden('#skF_3',k2_zfmisc_1(k1_tarski('#skF_4'),k2_tarski('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_35,plain,(
    r2_hidden('#skF_3',k2_tarski(k4_tarski('#skF_4','#skF_5'),k4_tarski('#skF_4','#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_30])).

tff(c_74,plain,(
    ! [D_23,B_24,A_25] :
      ( D_23 = B_24
      | D_23 = A_25
      | ~ r2_hidden(D_23,k2_tarski(A_25,B_24)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_87,plain,
    ( k4_tarski('#skF_4','#skF_6') = '#skF_3'
    | k4_tarski('#skF_4','#skF_5') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_35,c_74])).

tff(c_92,plain,(
    k4_tarski('#skF_4','#skF_5') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_87])).

tff(c_26,plain,(
    ! [A_11,B_12] : k1_mcart_1(k4_tarski(A_11,B_12)) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_98,plain,(
    k1_mcart_1('#skF_3') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_26])).

tff(c_105,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_73,c_98])).

tff(c_106,plain,(
    k4_tarski('#skF_4','#skF_6') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_87])).

tff(c_113,plain,(
    k1_mcart_1('#skF_3') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_26])).

tff(c_120,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_73,c_113])).

tff(c_121,plain,(
    k2_mcart_1('#skF_3') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_122,plain,(
    k1_mcart_1('#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_34,plain,
    ( k2_mcart_1('#skF_3') != '#skF_5'
    | k1_mcart_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_128,plain,(
    k2_mcart_1('#skF_3') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_34])).

tff(c_129,plain,(
    ! [D_26,B_27,A_28] :
      ( D_26 = B_27
      | D_26 = A_28
      | ~ r2_hidden(D_26,k2_tarski(A_28,B_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_142,plain,
    ( k4_tarski('#skF_4','#skF_6') = '#skF_3'
    | k4_tarski('#skF_4','#skF_5') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_35,c_129])).

tff(c_147,plain,(
    k4_tarski('#skF_4','#skF_5') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_142])).

tff(c_28,plain,(
    ! [A_11,B_12] : k2_mcart_1(k4_tarski(A_11,B_12)) = B_12 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_156,plain,(
    k2_mcart_1('#skF_3') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_147,c_28])).

tff(c_161,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_128,c_156])).

tff(c_162,plain,(
    k4_tarski('#skF_4','#skF_6') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_142])).

tff(c_172,plain,(
    k2_mcart_1('#skF_3') = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_162,c_28])).

tff(c_177,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_121,c_172])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:16:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.63/1.17  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.83/1.17  
% 1.83/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.83/1.17  %$ r2_hidden > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4
% 1.83/1.17  
% 1.83/1.17  %Foreground sorts:
% 1.83/1.17  
% 1.83/1.17  
% 1.83/1.17  %Background operators:
% 1.83/1.17  
% 1.83/1.17  
% 1.83/1.17  %Foreground operators:
% 1.83/1.17  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.83/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.83/1.17  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.83/1.17  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.83/1.17  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.83/1.17  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.83/1.17  tff('#skF_5', type, '#skF_5': $i).
% 1.83/1.17  tff('#skF_6', type, '#skF_6': $i).
% 1.83/1.17  tff('#skF_3', type, '#skF_3': $i).
% 1.83/1.17  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.83/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.83/1.17  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 1.83/1.17  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.83/1.17  tff('#skF_4', type, '#skF_4': $i).
% 1.83/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.83/1.17  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 1.83/1.17  
% 1.83/1.19  tff(f_53, negated_conjecture, ~(![A, B, C, D]: (r2_hidden(A, k2_zfmisc_1(k1_tarski(B), k2_tarski(C, D))) => ((k1_mcart_1(A) = B) & ((k2_mcart_1(A) = C) | (k2_mcart_1(A) = D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_mcart_1)).
% 1.83/1.19  tff(f_40, axiom, (![A, B, C]: ((k2_zfmisc_1(k1_tarski(A), k2_tarski(B, C)) = k2_tarski(k4_tarski(A, B), k4_tarski(A, C))) & (k2_zfmisc_1(k2_tarski(A, B), k1_tarski(C)) = k2_tarski(k4_tarski(A, C), k4_tarski(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_zfmisc_1)).
% 1.83/1.19  tff(f_34, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 1.83/1.19  tff(f_44, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 1.83/1.19  tff(c_32, plain, (k2_mcart_1('#skF_3')!='#skF_6' | k1_mcart_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.83/1.19  tff(c_73, plain, (k1_mcart_1('#skF_3')!='#skF_4'), inference(splitLeft, [status(thm)], [c_32])).
% 1.83/1.19  tff(c_22, plain, (![A_8, B_9, C_10]: (k2_zfmisc_1(k1_tarski(A_8), k2_tarski(B_9, C_10))=k2_tarski(k4_tarski(A_8, B_9), k4_tarski(A_8, C_10)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.83/1.19  tff(c_30, plain, (r2_hidden('#skF_3', k2_zfmisc_1(k1_tarski('#skF_4'), k2_tarski('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.83/1.19  tff(c_35, plain, (r2_hidden('#skF_3', k2_tarski(k4_tarski('#skF_4', '#skF_5'), k4_tarski('#skF_4', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_30])).
% 1.83/1.19  tff(c_74, plain, (![D_23, B_24, A_25]: (D_23=B_24 | D_23=A_25 | ~r2_hidden(D_23, k2_tarski(A_25, B_24)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.83/1.19  tff(c_87, plain, (k4_tarski('#skF_4', '#skF_6')='#skF_3' | k4_tarski('#skF_4', '#skF_5')='#skF_3'), inference(resolution, [status(thm)], [c_35, c_74])).
% 1.83/1.19  tff(c_92, plain, (k4_tarski('#skF_4', '#skF_5')='#skF_3'), inference(splitLeft, [status(thm)], [c_87])).
% 1.83/1.19  tff(c_26, plain, (![A_11, B_12]: (k1_mcart_1(k4_tarski(A_11, B_12))=A_11)), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.83/1.19  tff(c_98, plain, (k1_mcart_1('#skF_3')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_92, c_26])).
% 1.83/1.19  tff(c_105, plain, $false, inference(negUnitSimplification, [status(thm)], [c_73, c_98])).
% 1.83/1.19  tff(c_106, plain, (k4_tarski('#skF_4', '#skF_6')='#skF_3'), inference(splitRight, [status(thm)], [c_87])).
% 1.83/1.19  tff(c_113, plain, (k1_mcart_1('#skF_3')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_106, c_26])).
% 1.83/1.19  tff(c_120, plain, $false, inference(negUnitSimplification, [status(thm)], [c_73, c_113])).
% 1.83/1.19  tff(c_121, plain, (k2_mcart_1('#skF_3')!='#skF_6'), inference(splitRight, [status(thm)], [c_32])).
% 1.83/1.19  tff(c_122, plain, (k1_mcart_1('#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_32])).
% 1.83/1.19  tff(c_34, plain, (k2_mcart_1('#skF_3')!='#skF_5' | k1_mcart_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.83/1.19  tff(c_128, plain, (k2_mcart_1('#skF_3')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_122, c_34])).
% 1.83/1.19  tff(c_129, plain, (![D_26, B_27, A_28]: (D_26=B_27 | D_26=A_28 | ~r2_hidden(D_26, k2_tarski(A_28, B_27)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.83/1.19  tff(c_142, plain, (k4_tarski('#skF_4', '#skF_6')='#skF_3' | k4_tarski('#skF_4', '#skF_5')='#skF_3'), inference(resolution, [status(thm)], [c_35, c_129])).
% 1.83/1.19  tff(c_147, plain, (k4_tarski('#skF_4', '#skF_5')='#skF_3'), inference(splitLeft, [status(thm)], [c_142])).
% 1.83/1.19  tff(c_28, plain, (![A_11, B_12]: (k2_mcart_1(k4_tarski(A_11, B_12))=B_12)), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.83/1.19  tff(c_156, plain, (k2_mcart_1('#skF_3')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_147, c_28])).
% 1.83/1.19  tff(c_161, plain, $false, inference(negUnitSimplification, [status(thm)], [c_128, c_156])).
% 1.83/1.19  tff(c_162, plain, (k4_tarski('#skF_4', '#skF_6')='#skF_3'), inference(splitRight, [status(thm)], [c_142])).
% 1.83/1.19  tff(c_172, plain, (k2_mcart_1('#skF_3')='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_162, c_28])).
% 1.83/1.19  tff(c_177, plain, $false, inference(negUnitSimplification, [status(thm)], [c_121, c_172])).
% 1.83/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.83/1.19  
% 1.83/1.19  Inference rules
% 1.83/1.19  ----------------------
% 1.83/1.19  #Ref     : 0
% 1.83/1.19  #Sup     : 34
% 1.83/1.19  #Fact    : 0
% 1.83/1.19  #Define  : 0
% 1.83/1.19  #Split   : 3
% 1.83/1.19  #Chain   : 0
% 1.83/1.19  #Close   : 0
% 1.83/1.19  
% 1.83/1.19  Ordering : KBO
% 1.83/1.19  
% 1.83/1.19  Simplification rules
% 1.83/1.19  ----------------------
% 1.83/1.19  #Subsume      : 1
% 1.83/1.19  #Demod        : 13
% 1.83/1.19  #Tautology    : 23
% 1.83/1.19  #SimpNegUnit  : 4
% 1.83/1.19  #BackRed      : 4
% 1.83/1.19  
% 1.83/1.19  #Partial instantiations: 0
% 1.83/1.19  #Strategies tried      : 1
% 1.83/1.19  
% 1.83/1.19  Timing (in seconds)
% 1.83/1.19  ----------------------
% 1.83/1.19  Preprocessing        : 0.30
% 1.83/1.19  Parsing              : 0.15
% 1.83/1.19  CNF conversion       : 0.02
% 1.83/1.19  Main loop            : 0.13
% 1.83/1.19  Inferencing          : 0.04
% 1.83/1.19  Reduction            : 0.05
% 1.83/1.19  Demodulation         : 0.04
% 1.83/1.19  BG Simplification    : 0.01
% 1.83/1.19  Subsumption          : 0.02
% 1.83/1.19  Abstraction          : 0.01
% 1.83/1.19  MUC search           : 0.00
% 1.83/1.19  Cooper               : 0.00
% 1.83/1.19  Total                : 0.46
% 1.83/1.19  Index Insertion      : 0.00
% 1.83/1.19  Index Deletion       : 0.00
% 1.83/1.19  Index Matching       : 0.00
% 1.83/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
