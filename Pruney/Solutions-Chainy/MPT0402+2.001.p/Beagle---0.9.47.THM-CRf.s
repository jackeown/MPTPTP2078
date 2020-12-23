%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:40 EST 2020

% Result     : Theorem 4.47s
% Output     : CNFRefutation 4.47s
% Verified   : 
% Statistics : Number of formulae       :   37 (  47 expanded)
%              Number of leaves         :   20 (  27 expanded)
%              Depth                    :   10
%              Number of atoms          :   59 (  92 expanded)
%              Number of equality atoms :   18 (  18 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_setfam_1 > k1_enumset1 > k2_tarski > #nlpp > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_2 > #skF_6 > #skF_8 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_setfam_1,type,(
    r1_setfam_1: ( $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(f_67,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_setfam_1(C,k2_tarski(A,B))
       => ! [D] :
            ~ ( r2_hidden(D,C)
              & ~ r1_tarski(D,A)
              & ~ r1_tarski(D,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_setfam_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( r1_setfam_1(A,B)
    <=> ! [C] :
          ~ ( r2_hidden(C,A)
            & ! [D] :
                ~ ( r2_hidden(D,B)
                  & r1_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_setfam_1)).

tff(f_42,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_40,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(c_38,plain,(
    ~ r1_tarski('#skF_8','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_36,plain,(
    ~ r1_tarski('#skF_8','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_40,plain,(
    r2_hidden('#skF_8','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_42,plain,(
    r1_setfam_1('#skF_7',k2_tarski('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_30,plain,(
    ! [A_10,B_11,C_20] :
      ( r2_hidden('#skF_4'(A_10,B_11,C_20),B_11)
      | ~ r2_hidden(C_20,A_10)
      | ~ r1_setfam_1(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_26,plain,(
    ! [A_8,B_9] : k1_enumset1(A_8,A_8,B_9) = k2_tarski(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_75,plain,(
    ! [E_46,C_47,B_48,A_49] :
      ( E_46 = C_47
      | E_46 = B_48
      | E_46 = A_49
      | ~ r2_hidden(E_46,k1_enumset1(A_49,B_48,C_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_105,plain,(
    ! [E_53,B_54,A_55] :
      ( E_53 = B_54
      | E_53 = A_55
      | E_53 = A_55
      | ~ r2_hidden(E_53,k2_tarski(A_55,B_54)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_75])).

tff(c_1536,plain,(
    ! [A_231,A_232,B_233,C_234] :
      ( '#skF_4'(A_231,k2_tarski(A_232,B_233),C_234) = B_233
      | '#skF_4'(A_231,k2_tarski(A_232,B_233),C_234) = A_232
      | ~ r2_hidden(C_234,A_231)
      | ~ r1_setfam_1(A_231,k2_tarski(A_232,B_233)) ) ),
    inference(resolution,[status(thm)],[c_30,c_105])).

tff(c_1555,plain,(
    ! [C_235] :
      ( '#skF_4'('#skF_7',k2_tarski('#skF_5','#skF_6'),C_235) = '#skF_6'
      | '#skF_4'('#skF_7',k2_tarski('#skF_5','#skF_6'),C_235) = '#skF_5'
      | ~ r2_hidden(C_235,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_42,c_1536])).

tff(c_28,plain,(
    ! [C_20,A_10,B_11] :
      ( r1_tarski(C_20,'#skF_4'(A_10,B_11,C_20))
      | ~ r2_hidden(C_20,A_10)
      | ~ r1_setfam_1(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1568,plain,(
    ! [C_235] :
      ( r1_tarski(C_235,'#skF_5')
      | ~ r2_hidden(C_235,'#skF_7')
      | ~ r1_setfam_1('#skF_7',k2_tarski('#skF_5','#skF_6'))
      | '#skF_4'('#skF_7',k2_tarski('#skF_5','#skF_6'),C_235) = '#skF_6'
      | ~ r2_hidden(C_235,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1555,c_28])).

tff(c_1581,plain,(
    ! [C_236] :
      ( r1_tarski(C_236,'#skF_5')
      | '#skF_4'('#skF_7',k2_tarski('#skF_5','#skF_6'),C_236) = '#skF_6'
      | ~ r2_hidden(C_236,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1568])).

tff(c_1597,plain,(
    ! [C_236] :
      ( r1_tarski(C_236,'#skF_6')
      | ~ r2_hidden(C_236,'#skF_7')
      | ~ r1_setfam_1('#skF_7',k2_tarski('#skF_5','#skF_6'))
      | r1_tarski(C_236,'#skF_5')
      | ~ r2_hidden(C_236,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1581,c_28])).

tff(c_1788,plain,(
    ! [C_243] :
      ( r1_tarski(C_243,'#skF_6')
      | r1_tarski(C_243,'#skF_5')
      | ~ r2_hidden(C_243,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1597])).

tff(c_1807,plain,
    ( r1_tarski('#skF_8','#skF_6')
    | r1_tarski('#skF_8','#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_1788])).

tff(c_1815,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_36,c_1807])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:32:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.47/1.80  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.47/1.81  
% 4.47/1.81  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.47/1.81  %$ r2_hidden > r1_tarski > r1_setfam_1 > k1_enumset1 > k2_tarski > #nlpp > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_2 > #skF_6 > #skF_8 > #skF_1
% 4.47/1.81  
% 4.47/1.81  %Foreground sorts:
% 4.47/1.81  
% 4.47/1.81  
% 4.47/1.81  %Background operators:
% 4.47/1.81  
% 4.47/1.81  
% 4.47/1.81  %Foreground operators:
% 4.47/1.81  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.47/1.81  tff(r1_setfam_1, type, r1_setfam_1: ($i * $i) > $o).
% 4.47/1.81  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.47/1.81  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 4.47/1.81  tff('#skF_7', type, '#skF_7': $i).
% 4.47/1.81  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.47/1.81  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.47/1.81  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.47/1.81  tff('#skF_5', type, '#skF_5': $i).
% 4.47/1.81  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 4.47/1.81  tff('#skF_6', type, '#skF_6': $i).
% 4.47/1.81  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.47/1.81  tff('#skF_8', type, '#skF_8': $i).
% 4.47/1.81  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.47/1.81  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.47/1.81  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 4.47/1.81  
% 4.47/1.82  tff(f_67, negated_conjecture, ~(![A, B, C]: (r1_setfam_1(C, k2_tarski(A, B)) => (![D]: ~((r2_hidden(D, C) & ~r1_tarski(D, A)) & ~r1_tarski(D, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_setfam_1)).
% 4.47/1.82  tff(f_54, axiom, (![A, B]: (r1_setfam_1(A, B) <=> (![C]: ~(r2_hidden(C, A) & (![D]: ~(r2_hidden(D, B) & r1_tarski(C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_setfam_1)).
% 4.47/1.82  tff(f_42, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 4.47/1.82  tff(f_40, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 4.47/1.82  tff(c_38, plain, (~r1_tarski('#skF_8', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.47/1.82  tff(c_36, plain, (~r1_tarski('#skF_8', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.47/1.82  tff(c_40, plain, (r2_hidden('#skF_8', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.47/1.82  tff(c_42, plain, (r1_setfam_1('#skF_7', k2_tarski('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.47/1.82  tff(c_30, plain, (![A_10, B_11, C_20]: (r2_hidden('#skF_4'(A_10, B_11, C_20), B_11) | ~r2_hidden(C_20, A_10) | ~r1_setfam_1(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.47/1.82  tff(c_26, plain, (![A_8, B_9]: (k1_enumset1(A_8, A_8, B_9)=k2_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.47/1.82  tff(c_75, plain, (![E_46, C_47, B_48, A_49]: (E_46=C_47 | E_46=B_48 | E_46=A_49 | ~r2_hidden(E_46, k1_enumset1(A_49, B_48, C_47)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.47/1.82  tff(c_105, plain, (![E_53, B_54, A_55]: (E_53=B_54 | E_53=A_55 | E_53=A_55 | ~r2_hidden(E_53, k2_tarski(A_55, B_54)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_75])).
% 4.47/1.82  tff(c_1536, plain, (![A_231, A_232, B_233, C_234]: ('#skF_4'(A_231, k2_tarski(A_232, B_233), C_234)=B_233 | '#skF_4'(A_231, k2_tarski(A_232, B_233), C_234)=A_232 | ~r2_hidden(C_234, A_231) | ~r1_setfam_1(A_231, k2_tarski(A_232, B_233)))), inference(resolution, [status(thm)], [c_30, c_105])).
% 4.47/1.82  tff(c_1555, plain, (![C_235]: ('#skF_4'('#skF_7', k2_tarski('#skF_5', '#skF_6'), C_235)='#skF_6' | '#skF_4'('#skF_7', k2_tarski('#skF_5', '#skF_6'), C_235)='#skF_5' | ~r2_hidden(C_235, '#skF_7'))), inference(resolution, [status(thm)], [c_42, c_1536])).
% 4.47/1.82  tff(c_28, plain, (![C_20, A_10, B_11]: (r1_tarski(C_20, '#skF_4'(A_10, B_11, C_20)) | ~r2_hidden(C_20, A_10) | ~r1_setfam_1(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.47/1.82  tff(c_1568, plain, (![C_235]: (r1_tarski(C_235, '#skF_5') | ~r2_hidden(C_235, '#skF_7') | ~r1_setfam_1('#skF_7', k2_tarski('#skF_5', '#skF_6')) | '#skF_4'('#skF_7', k2_tarski('#skF_5', '#skF_6'), C_235)='#skF_6' | ~r2_hidden(C_235, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_1555, c_28])).
% 4.47/1.82  tff(c_1581, plain, (![C_236]: (r1_tarski(C_236, '#skF_5') | '#skF_4'('#skF_7', k2_tarski('#skF_5', '#skF_6'), C_236)='#skF_6' | ~r2_hidden(C_236, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_1568])).
% 4.47/1.82  tff(c_1597, plain, (![C_236]: (r1_tarski(C_236, '#skF_6') | ~r2_hidden(C_236, '#skF_7') | ~r1_setfam_1('#skF_7', k2_tarski('#skF_5', '#skF_6')) | r1_tarski(C_236, '#skF_5') | ~r2_hidden(C_236, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_1581, c_28])).
% 4.47/1.82  tff(c_1788, plain, (![C_243]: (r1_tarski(C_243, '#skF_6') | r1_tarski(C_243, '#skF_5') | ~r2_hidden(C_243, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_1597])).
% 4.47/1.82  tff(c_1807, plain, (r1_tarski('#skF_8', '#skF_6') | r1_tarski('#skF_8', '#skF_5')), inference(resolution, [status(thm)], [c_40, c_1788])).
% 4.47/1.82  tff(c_1815, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_36, c_1807])).
% 4.47/1.82  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.47/1.82  
% 4.47/1.82  Inference rules
% 4.47/1.82  ----------------------
% 4.47/1.82  #Ref     : 1
% 4.47/1.82  #Sup     : 451
% 4.47/1.82  #Fact    : 11
% 4.47/1.82  #Define  : 0
% 4.47/1.82  #Split   : 1
% 4.47/1.82  #Chain   : 0
% 4.47/1.82  #Close   : 0
% 4.47/1.82  
% 4.47/1.82  Ordering : KBO
% 4.47/1.82  
% 4.47/1.82  Simplification rules
% 4.47/1.82  ----------------------
% 4.47/1.82  #Subsume      : 145
% 4.47/1.82  #Demod        : 69
% 4.47/1.82  #Tautology    : 71
% 4.47/1.82  #SimpNegUnit  : 3
% 4.47/1.82  #BackRed      : 0
% 4.47/1.82  
% 4.47/1.82  #Partial instantiations: 0
% 4.47/1.82  #Strategies tried      : 1
% 4.47/1.82  
% 4.47/1.82  Timing (in seconds)
% 4.47/1.82  ----------------------
% 4.47/1.82  Preprocessing        : 0.28
% 4.47/1.82  Parsing              : 0.13
% 4.47/1.82  CNF conversion       : 0.02
% 4.47/1.82  Main loop            : 0.77
% 4.47/1.82  Inferencing          : 0.28
% 4.47/1.82  Reduction            : 0.18
% 4.47/1.82  Demodulation         : 0.12
% 4.47/1.82  BG Simplification    : 0.05
% 4.47/1.82  Subsumption          : 0.22
% 4.47/1.82  Abstraction          : 0.07
% 4.47/1.82  MUC search           : 0.00
% 4.47/1.82  Cooper               : 0.00
% 4.47/1.82  Total                : 1.07
% 4.47/1.82  Index Insertion      : 0.00
% 4.47/1.82  Index Deletion       : 0.00
% 4.47/1.82  Index Matching       : 0.00
% 4.47/1.82  BG Taut test         : 0.00
%------------------------------------------------------------------------------
