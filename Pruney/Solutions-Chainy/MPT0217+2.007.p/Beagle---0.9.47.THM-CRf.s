%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:46 EST 2020

% Result     : Theorem 1.59s
% Output     : CNFRefutation 1.76s
% Verified   : 
% Statistics : Number of formulae       :   32 (  73 expanded)
%              Number of leaves         :   14 (  33 expanded)
%              Depth                    :    9
%              Number of atoms          :   29 ( 127 expanded)
%              Number of equality atoms :   21 ( 101 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k6_enumset1 > k2_tarski > #nlpp > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_46,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ~ ( k2_tarski(A,B) = k2_tarski(C,D)
          & A != C
          & A != D ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(c_22,plain,(
    '#skF_6' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_26,plain,(
    k2_tarski('#skF_5','#skF_6') = k2_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_4,plain,(
    ! [D_6,A_1] : r2_hidden(D_6,k2_tarski(A_1,D_6)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_32,plain,(
    r2_hidden('#skF_6',k2_tarski('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_4])).

tff(c_2,plain,(
    ! [D_6,B_2,A_1] :
      ( D_6 = B_2
      | D_6 = A_1
      | ~ r2_hidden(D_6,k2_tarski(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_55,plain,
    ( '#skF_6' = '#skF_4'
    | '#skF_6' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_32,c_2])).

tff(c_58,plain,(
    '#skF_6' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_55])).

tff(c_61,plain,(
    '#skF_3' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_22])).

tff(c_24,plain,(
    '#skF_5' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_6,plain,(
    ! [D_6,B_2] : r2_hidden(D_6,k2_tarski(D_6,B_2)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_35,plain,(
    r2_hidden('#skF_5',k2_tarski('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_6])).

tff(c_69,plain,
    ( '#skF_5' = '#skF_4'
    | '#skF_5' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_35,c_2])).

tff(c_72,plain,(
    '#skF_5' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_69])).

tff(c_60,plain,(
    k2_tarski('#skF_5','#skF_4') = k2_tarski('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_26])).

tff(c_80,plain,(
    k2_tarski('#skF_3','#skF_4') = k2_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_60])).

tff(c_90,plain,(
    r2_hidden('#skF_3',k2_tarski('#skF_4','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_6])).

tff(c_97,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_90,c_2])).

tff(c_101,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_61,c_61,c_97])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n009.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:39:56 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.59/1.15  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.59/1.16  
% 1.59/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.59/1.16  %$ r2_hidden > k6_enumset1 > k2_tarski > #nlpp > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4
% 1.59/1.16  
% 1.59/1.16  %Foreground sorts:
% 1.59/1.16  
% 1.59/1.16  
% 1.59/1.16  %Background operators:
% 1.59/1.16  
% 1.59/1.16  
% 1.59/1.16  %Foreground operators:
% 1.59/1.16  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.59/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.59/1.16  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.59/1.16  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.59/1.16  tff('#skF_5', type, '#skF_5': $i).
% 1.59/1.16  tff('#skF_6', type, '#skF_6': $i).
% 1.59/1.16  tff('#skF_3', type, '#skF_3': $i).
% 1.59/1.16  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.59/1.16  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 1.59/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.59/1.16  tff('#skF_4', type, '#skF_4': $i).
% 1.59/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.59/1.16  
% 1.76/1.18  tff(f_46, negated_conjecture, ~(![A, B, C, D]: ~(((k2_tarski(A, B) = k2_tarski(C, D)) & ~(A = C)) & ~(A = D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_zfmisc_1)).
% 1.76/1.18  tff(f_34, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 1.76/1.18  tff(c_22, plain, ('#skF_6'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.76/1.18  tff(c_26, plain, (k2_tarski('#skF_5', '#skF_6')=k2_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.76/1.18  tff(c_4, plain, (![D_6, A_1]: (r2_hidden(D_6, k2_tarski(A_1, D_6)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.76/1.18  tff(c_32, plain, (r2_hidden('#skF_6', k2_tarski('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_26, c_4])).
% 1.76/1.18  tff(c_2, plain, (![D_6, B_2, A_1]: (D_6=B_2 | D_6=A_1 | ~r2_hidden(D_6, k2_tarski(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.76/1.18  tff(c_55, plain, ('#skF_6'='#skF_4' | '#skF_6'='#skF_3'), inference(resolution, [status(thm)], [c_32, c_2])).
% 1.76/1.18  tff(c_58, plain, ('#skF_6'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_22, c_55])).
% 1.76/1.18  tff(c_61, plain, ('#skF_3'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_22])).
% 1.76/1.18  tff(c_24, plain, ('#skF_5'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.76/1.18  tff(c_6, plain, (![D_6, B_2]: (r2_hidden(D_6, k2_tarski(D_6, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.76/1.18  tff(c_35, plain, (r2_hidden('#skF_5', k2_tarski('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_26, c_6])).
% 1.76/1.18  tff(c_69, plain, ('#skF_5'='#skF_4' | '#skF_5'='#skF_3'), inference(resolution, [status(thm)], [c_35, c_2])).
% 1.76/1.18  tff(c_72, plain, ('#skF_5'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_24, c_69])).
% 1.76/1.18  tff(c_60, plain, (k2_tarski('#skF_5', '#skF_4')=k2_tarski('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_26])).
% 1.76/1.18  tff(c_80, plain, (k2_tarski('#skF_3', '#skF_4')=k2_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_60])).
% 1.76/1.18  tff(c_90, plain, (r2_hidden('#skF_3', k2_tarski('#skF_4', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_80, c_6])).
% 1.76/1.18  tff(c_97, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_90, c_2])).
% 1.76/1.18  tff(c_101, plain, $false, inference(negUnitSimplification, [status(thm)], [c_61, c_61, c_97])).
% 1.76/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.76/1.18  
% 1.76/1.18  Inference rules
% 1.76/1.18  ----------------------
% 1.76/1.18  #Ref     : 0
% 1.76/1.18  #Sup     : 19
% 1.76/1.18  #Fact    : 0
% 1.76/1.18  #Define  : 0
% 1.76/1.18  #Split   : 0
% 1.76/1.18  #Chain   : 0
% 1.76/1.18  #Close   : 0
% 1.76/1.18  
% 1.76/1.18  Ordering : KBO
% 1.76/1.18  
% 1.76/1.18  Simplification rules
% 1.76/1.18  ----------------------
% 1.76/1.18  #Subsume      : 1
% 1.76/1.18  #Demod        : 9
% 1.76/1.18  #Tautology    : 13
% 1.76/1.18  #SimpNegUnit  : 3
% 1.76/1.18  #BackRed      : 5
% 1.76/1.18  
% 1.76/1.18  #Partial instantiations: 0
% 1.76/1.18  #Strategies tried      : 1
% 1.76/1.18  
% 1.76/1.18  Timing (in seconds)
% 1.76/1.18  ----------------------
% 1.76/1.18  Preprocessing        : 0.27
% 1.76/1.18  Parsing              : 0.13
% 1.76/1.18  CNF conversion       : 0.02
% 1.76/1.18  Main loop            : 0.13
% 1.76/1.18  Inferencing          : 0.04
% 1.76/1.18  Reduction            : 0.05
% 1.76/1.18  Demodulation         : 0.03
% 1.76/1.18  BG Simplification    : 0.01
% 1.76/1.18  Subsumption          : 0.03
% 1.76/1.18  Abstraction          : 0.01
% 1.76/1.18  MUC search           : 0.00
% 1.76/1.18  Cooper               : 0.00
% 1.76/1.19  Total                : 0.43
% 1.76/1.19  Index Insertion      : 0.00
% 1.76/1.19  Index Deletion       : 0.00
% 1.76/1.19  Index Matching       : 0.00
% 1.76/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
