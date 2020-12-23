%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:45 EST 2020

% Result     : Theorem 1.60s
% Output     : CNFRefutation 1.80s
% Verified   : 
% Statistics : Number of formulae       :   33 (  73 expanded)
%              Number of leaves         :   14 (  33 expanded)
%              Depth                    :    9
%              Number of atoms          :   32 ( 127 expanded)
%              Number of equality atoms :   23 ( 101 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k1_enumset1 > k2_tarski > #nlpp > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

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

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(c_24,plain,(
    '#skF_5' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_26,plain,(
    k2_tarski('#skF_5','#skF_6') = k2_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_6,plain,(
    ! [D_6,B_2] : r2_hidden(D_6,k2_tarski(D_6,B_2)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_35,plain,(
    r2_hidden('#skF_5',k2_tarski('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_6])).

tff(c_48,plain,(
    ! [D_15,B_16,A_17] :
      ( D_15 = B_16
      | D_15 = A_17
      | ~ r2_hidden(D_15,k2_tarski(A_17,B_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_51,plain,
    ( '#skF_5' = '#skF_4'
    | '#skF_5' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_35,c_48])).

tff(c_66,plain,(
    '#skF_5' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_51])).

tff(c_76,plain,(
    '#skF_3' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_24])).

tff(c_22,plain,(
    '#skF_6' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_4,plain,(
    ! [D_6,A_1] : r2_hidden(D_6,k2_tarski(A_1,D_6)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_32,plain,(
    r2_hidden('#skF_6',k2_tarski('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_4])).

tff(c_54,plain,
    ( '#skF_6' = '#skF_4'
    | '#skF_6' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_32,c_48])).

tff(c_69,plain,(
    '#skF_6' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_54])).

tff(c_75,plain,(
    k2_tarski('#skF_3','#skF_4') = k2_tarski('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_26])).

tff(c_89,plain,(
    k2_tarski('#skF_3','#skF_4') = k2_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_75])).

tff(c_99,plain,(
    r2_hidden('#skF_3',k2_tarski('#skF_4','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_6])).

tff(c_2,plain,(
    ! [D_6,B_2,A_1] :
      ( D_6 = B_2
      | D_6 = A_1
      | ~ r2_hidden(D_6,k2_tarski(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_106,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_99,c_2])).

tff(c_110,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_76,c_106])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n017.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:51:16 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.60/1.17  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.80/1.18  
% 1.80/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.80/1.18  %$ r2_hidden > k1_enumset1 > k2_tarski > #nlpp > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4
% 1.80/1.18  
% 1.80/1.18  %Foreground sorts:
% 1.80/1.18  
% 1.80/1.18  
% 1.80/1.18  %Background operators:
% 1.80/1.18  
% 1.80/1.18  
% 1.80/1.18  %Foreground operators:
% 1.80/1.18  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.80/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.80/1.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.80/1.18  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.80/1.18  tff('#skF_5', type, '#skF_5': $i).
% 1.80/1.18  tff('#skF_6', type, '#skF_6': $i).
% 1.80/1.18  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.80/1.18  tff('#skF_3', type, '#skF_3': $i).
% 1.80/1.18  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.80/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.80/1.18  tff('#skF_4', type, '#skF_4': $i).
% 1.80/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.80/1.18  
% 1.80/1.19  tff(f_46, negated_conjecture, ~(![A, B, C, D]: ~(((k2_tarski(A, B) = k2_tarski(C, D)) & ~(A = C)) & ~(A = D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_zfmisc_1)).
% 1.80/1.19  tff(f_34, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 1.80/1.19  tff(c_24, plain, ('#skF_5'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.80/1.19  tff(c_26, plain, (k2_tarski('#skF_5', '#skF_6')=k2_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.80/1.19  tff(c_6, plain, (![D_6, B_2]: (r2_hidden(D_6, k2_tarski(D_6, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.80/1.19  tff(c_35, plain, (r2_hidden('#skF_5', k2_tarski('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_26, c_6])).
% 1.80/1.19  tff(c_48, plain, (![D_15, B_16, A_17]: (D_15=B_16 | D_15=A_17 | ~r2_hidden(D_15, k2_tarski(A_17, B_16)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.80/1.19  tff(c_51, plain, ('#skF_5'='#skF_4' | '#skF_5'='#skF_3'), inference(resolution, [status(thm)], [c_35, c_48])).
% 1.80/1.19  tff(c_66, plain, ('#skF_5'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_24, c_51])).
% 1.80/1.19  tff(c_76, plain, ('#skF_3'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_24])).
% 1.80/1.19  tff(c_22, plain, ('#skF_6'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.80/1.19  tff(c_4, plain, (![D_6, A_1]: (r2_hidden(D_6, k2_tarski(A_1, D_6)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.80/1.19  tff(c_32, plain, (r2_hidden('#skF_6', k2_tarski('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_26, c_4])).
% 1.80/1.19  tff(c_54, plain, ('#skF_6'='#skF_4' | '#skF_6'='#skF_3'), inference(resolution, [status(thm)], [c_32, c_48])).
% 1.80/1.19  tff(c_69, plain, ('#skF_6'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_22, c_54])).
% 1.80/1.19  tff(c_75, plain, (k2_tarski('#skF_3', '#skF_4')=k2_tarski('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_26])).
% 1.80/1.19  tff(c_89, plain, (k2_tarski('#skF_3', '#skF_4')=k2_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_69, c_75])).
% 1.80/1.19  tff(c_99, plain, (r2_hidden('#skF_3', k2_tarski('#skF_4', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_89, c_6])).
% 1.80/1.19  tff(c_2, plain, (![D_6, B_2, A_1]: (D_6=B_2 | D_6=A_1 | ~r2_hidden(D_6, k2_tarski(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.80/1.19  tff(c_106, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_99, c_2])).
% 1.80/1.19  tff(c_110, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_76, c_106])).
% 1.80/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.80/1.19  
% 1.80/1.19  Inference rules
% 1.80/1.19  ----------------------
% 1.80/1.19  #Ref     : 0
% 1.80/1.19  #Sup     : 21
% 1.80/1.19  #Fact    : 0
% 1.80/1.19  #Define  : 0
% 1.80/1.19  #Split   : 0
% 1.80/1.19  #Chain   : 0
% 1.80/1.19  #Close   : 0
% 1.80/1.19  
% 1.80/1.19  Ordering : KBO
% 1.80/1.19  
% 1.80/1.19  Simplification rules
% 1.80/1.19  ----------------------
% 1.80/1.19  #Subsume      : 1
% 1.80/1.19  #Demod        : 9
% 1.80/1.19  #Tautology    : 15
% 1.80/1.19  #SimpNegUnit  : 3
% 1.80/1.19  #BackRed      : 5
% 1.80/1.19  
% 1.80/1.19  #Partial instantiations: 0
% 1.80/1.19  #Strategies tried      : 1
% 1.80/1.19  
% 1.80/1.19  Timing (in seconds)
% 1.80/1.19  ----------------------
% 1.80/1.19  Preprocessing        : 0.30
% 1.80/1.19  Parsing              : 0.15
% 1.80/1.19  CNF conversion       : 0.02
% 1.80/1.19  Main loop            : 0.10
% 1.80/1.19  Inferencing          : 0.03
% 1.80/1.19  Reduction            : 0.03
% 1.80/1.19  Demodulation         : 0.02
% 1.80/1.19  BG Simplification    : 0.01
% 1.80/1.19  Subsumption          : 0.02
% 1.80/1.19  Abstraction          : 0.01
% 1.80/1.19  MUC search           : 0.00
% 1.80/1.19  Cooper               : 0.00
% 1.80/1.19  Total                : 0.42
% 1.80/1.19  Index Insertion      : 0.00
% 1.80/1.19  Index Deletion       : 0.00
% 1.80/1.19  Index Matching       : 0.00
% 1.80/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
