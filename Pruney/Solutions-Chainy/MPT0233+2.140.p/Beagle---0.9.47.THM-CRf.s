%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:39 EST 2020

% Result     : Theorem 1.61s
% Output     : CNFRefutation 1.61s
% Verified   : 
% Statistics : Number of formulae       :   39 (  84 expanded)
%              Number of leaves         :   16 (  37 expanded)
%              Depth                    :    9
%              Number of atoms          :   43 ( 159 expanded)
%              Number of equality atoms :   18 (  76 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_tarski > #nlpp > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_51,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ~ ( r1_tarski(k2_tarski(A,B),k2_tarski(C,D))
          & A != C
          & A != D ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(c_28,plain,(
    '#skF_6' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_26,plain,(
    '#skF_7' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_30,plain,(
    r1_tarski(k2_tarski('#skF_4','#skF_5'),k2_tarski('#skF_6','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_10,plain,(
    ! [D_11,A_6] : r2_hidden(D_11,k2_tarski(A_6,D_11)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_41,plain,(
    ! [C_21,B_22,A_23] :
      ( r2_hidden(C_21,B_22)
      | ~ r2_hidden(C_21,A_23)
      | ~ r1_tarski(A_23,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_67,plain,(
    ! [D_27,B_28,A_29] :
      ( r2_hidden(D_27,B_28)
      | ~ r1_tarski(k2_tarski(A_29,D_27),B_28) ) ),
    inference(resolution,[status(thm)],[c_10,c_41])).

tff(c_77,plain,(
    r2_hidden('#skF_5',k2_tarski('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_30,c_67])).

tff(c_8,plain,(
    ! [D_11,B_7,A_6] :
      ( D_11 = B_7
      | D_11 = A_6
      | ~ r2_hidden(D_11,k2_tarski(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_83,plain,
    ( '#skF_7' = '#skF_5'
    | '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_77,c_8])).

tff(c_85,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_83])).

tff(c_87,plain,(
    r1_tarski(k2_tarski('#skF_4','#skF_6'),k2_tarski('#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_30])).

tff(c_12,plain,(
    ! [D_11,B_7] : r2_hidden(D_11,k2_tarski(D_11,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_99,plain,(
    ! [D_33,B_34,B_35] :
      ( r2_hidden(D_33,B_34)
      | ~ r1_tarski(k2_tarski(D_33,B_35),B_34) ) ),
    inference(resolution,[status(thm)],[c_12,c_41])).

tff(c_107,plain,(
    r2_hidden('#skF_4',k2_tarski('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_87,c_99])).

tff(c_112,plain,
    ( '#skF_7' = '#skF_4'
    | '#skF_6' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_107,c_8])).

tff(c_118,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_26,c_112])).

tff(c_119,plain,(
    '#skF_7' = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_83])).

tff(c_123,plain,(
    '#skF_5' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_26])).

tff(c_122,plain,(
    r1_tarski(k2_tarski('#skF_4','#skF_5'),k2_tarski('#skF_6','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_30])).

tff(c_134,plain,(
    ! [D_36,B_37,B_38] :
      ( r2_hidden(D_36,B_37)
      | ~ r1_tarski(k2_tarski(D_36,B_38),B_37) ) ),
    inference(resolution,[status(thm)],[c_12,c_41])).

tff(c_142,plain,(
    r2_hidden('#skF_4',k2_tarski('#skF_6','#skF_5')) ),
    inference(resolution,[status(thm)],[c_122,c_134])).

tff(c_147,plain,
    ( '#skF_5' = '#skF_4'
    | '#skF_6' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_142,c_8])).

tff(c_153,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_123,c_147])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:51:08 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.61/1.15  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.61/1.15  
% 1.61/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.61/1.16  %$ r2_hidden > r1_tarski > k2_tarski > #nlpp > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 1.61/1.16  
% 1.61/1.16  %Foreground sorts:
% 1.61/1.16  
% 1.61/1.16  
% 1.61/1.16  %Background operators:
% 1.61/1.16  
% 1.61/1.16  
% 1.61/1.16  %Foreground operators:
% 1.61/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.61/1.16  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.61/1.16  tff('#skF_7', type, '#skF_7': $i).
% 1.61/1.16  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.61/1.16  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.61/1.16  tff('#skF_5', type, '#skF_5': $i).
% 1.61/1.16  tff('#skF_6', type, '#skF_6': $i).
% 1.61/1.16  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.61/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.61/1.16  tff('#skF_4', type, '#skF_4': $i).
% 1.61/1.16  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 1.61/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.61/1.16  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.61/1.16  
% 1.61/1.17  tff(f_51, negated_conjecture, ~(![A, B, C, D]: ~((r1_tarski(k2_tarski(A, B), k2_tarski(C, D)) & ~(A = C)) & ~(A = D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_zfmisc_1)).
% 1.61/1.17  tff(f_41, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 1.61/1.17  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 1.61/1.17  tff(c_28, plain, ('#skF_6'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.61/1.17  tff(c_26, plain, ('#skF_7'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.61/1.17  tff(c_30, plain, (r1_tarski(k2_tarski('#skF_4', '#skF_5'), k2_tarski('#skF_6', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.61/1.17  tff(c_10, plain, (![D_11, A_6]: (r2_hidden(D_11, k2_tarski(A_6, D_11)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.61/1.17  tff(c_41, plain, (![C_21, B_22, A_23]: (r2_hidden(C_21, B_22) | ~r2_hidden(C_21, A_23) | ~r1_tarski(A_23, B_22))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.61/1.17  tff(c_67, plain, (![D_27, B_28, A_29]: (r2_hidden(D_27, B_28) | ~r1_tarski(k2_tarski(A_29, D_27), B_28))), inference(resolution, [status(thm)], [c_10, c_41])).
% 1.61/1.17  tff(c_77, plain, (r2_hidden('#skF_5', k2_tarski('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_30, c_67])).
% 1.61/1.17  tff(c_8, plain, (![D_11, B_7, A_6]: (D_11=B_7 | D_11=A_6 | ~r2_hidden(D_11, k2_tarski(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.61/1.17  tff(c_83, plain, ('#skF_7'='#skF_5' | '#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_77, c_8])).
% 1.61/1.17  tff(c_85, plain, ('#skF_5'='#skF_6'), inference(splitLeft, [status(thm)], [c_83])).
% 1.61/1.17  tff(c_87, plain, (r1_tarski(k2_tarski('#skF_4', '#skF_6'), k2_tarski('#skF_6', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_85, c_30])).
% 1.61/1.17  tff(c_12, plain, (![D_11, B_7]: (r2_hidden(D_11, k2_tarski(D_11, B_7)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.61/1.17  tff(c_99, plain, (![D_33, B_34, B_35]: (r2_hidden(D_33, B_34) | ~r1_tarski(k2_tarski(D_33, B_35), B_34))), inference(resolution, [status(thm)], [c_12, c_41])).
% 1.61/1.17  tff(c_107, plain, (r2_hidden('#skF_4', k2_tarski('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_87, c_99])).
% 1.61/1.17  tff(c_112, plain, ('#skF_7'='#skF_4' | '#skF_6'='#skF_4'), inference(resolution, [status(thm)], [c_107, c_8])).
% 1.61/1.17  tff(c_118, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_26, c_112])).
% 1.61/1.17  tff(c_119, plain, ('#skF_7'='#skF_5'), inference(splitRight, [status(thm)], [c_83])).
% 1.61/1.17  tff(c_123, plain, ('#skF_5'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_119, c_26])).
% 1.61/1.17  tff(c_122, plain, (r1_tarski(k2_tarski('#skF_4', '#skF_5'), k2_tarski('#skF_6', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_119, c_30])).
% 1.61/1.17  tff(c_134, plain, (![D_36, B_37, B_38]: (r2_hidden(D_36, B_37) | ~r1_tarski(k2_tarski(D_36, B_38), B_37))), inference(resolution, [status(thm)], [c_12, c_41])).
% 1.61/1.17  tff(c_142, plain, (r2_hidden('#skF_4', k2_tarski('#skF_6', '#skF_5'))), inference(resolution, [status(thm)], [c_122, c_134])).
% 1.61/1.17  tff(c_147, plain, ('#skF_5'='#skF_4' | '#skF_6'='#skF_4'), inference(resolution, [status(thm)], [c_142, c_8])).
% 1.61/1.17  tff(c_153, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_123, c_147])).
% 1.61/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.61/1.17  
% 1.61/1.17  Inference rules
% 1.61/1.17  ----------------------
% 1.61/1.17  #Ref     : 0
% 1.61/1.17  #Sup     : 25
% 1.61/1.17  #Fact    : 0
% 1.61/1.17  #Define  : 0
% 1.61/1.17  #Split   : 1
% 1.61/1.17  #Chain   : 0
% 1.61/1.17  #Close   : 0
% 1.61/1.17  
% 1.61/1.17  Ordering : KBO
% 1.61/1.17  
% 1.61/1.17  Simplification rules
% 1.61/1.17  ----------------------
% 1.61/1.17  #Subsume      : 0
% 1.61/1.17  #Demod        : 12
% 1.61/1.17  #Tautology    : 13
% 1.61/1.17  #SimpNegUnit  : 2
% 1.61/1.17  #BackRed      : 5
% 1.61/1.17  
% 1.61/1.17  #Partial instantiations: 0
% 1.61/1.17  #Strategies tried      : 1
% 1.61/1.17  
% 1.61/1.17  Timing (in seconds)
% 1.61/1.17  ----------------------
% 1.61/1.17  Preprocessing        : 0.26
% 1.61/1.17  Parsing              : 0.12
% 1.61/1.17  CNF conversion       : 0.02
% 1.61/1.17  Main loop            : 0.14
% 1.61/1.17  Inferencing          : 0.05
% 1.61/1.17  Reduction            : 0.04
% 1.61/1.17  Demodulation         : 0.03
% 1.61/1.17  BG Simplification    : 0.01
% 1.61/1.17  Subsumption          : 0.03
% 1.61/1.17  Abstraction          : 0.01
% 1.61/1.17  MUC search           : 0.00
% 1.61/1.17  Cooper               : 0.00
% 1.61/1.17  Total                : 0.42
% 1.61/1.17  Index Insertion      : 0.00
% 1.61/1.17  Index Deletion       : 0.00
% 1.61/1.17  Index Matching       : 0.00
% 1.61/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
