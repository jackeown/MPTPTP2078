%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:09 EST 2020

% Result     : Theorem 2.03s
% Output     : CNFRefutation 2.03s
% Verified   : 
% Statistics : Number of formulae       :   36 (  42 expanded)
%              Number of leaves         :   20 (  25 expanded)
%              Depth                    :    7
%              Number of atoms          :   39 (  55 expanded)
%              Number of equality atoms :   21 (  33 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_63,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( r1_tarski(k1_tarski(A),k2_tarski(B,C))
          & A != B
          & A != C ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_zfmisc_1)).

tff(f_49,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_51,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_47,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(c_40,plain,(
    '#skF_5' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_38,plain,(
    '#skF_6' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_42,plain,(
    r1_tarski(k1_tarski('#skF_4'),k2_tarski('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_32,plain,(
    ! [A_13] : k2_tarski(A_13,A_13) = k1_tarski(A_13) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_55,plain,(
    ! [A_29,B_30] : k1_enumset1(A_29,A_29,B_30) = k2_tarski(A_29,B_30) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_14,plain,(
    ! [E_12,B_7,C_8] : r2_hidden(E_12,k1_enumset1(E_12,B_7,C_8)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_73,plain,(
    ! [A_31,B_32] : r2_hidden(A_31,k2_tarski(A_31,B_32)) ),
    inference(superposition,[status(thm),theory(equality)],[c_55,c_14])).

tff(c_76,plain,(
    ! [A_13] : r2_hidden(A_13,k1_tarski(A_13)) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_73])).

tff(c_101,plain,(
    ! [C_44,B_45,A_46] :
      ( r2_hidden(C_44,B_45)
      | ~ r2_hidden(C_44,A_46)
      | ~ r1_tarski(A_46,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_123,plain,(
    ! [A_47,B_48] :
      ( r2_hidden(A_47,B_48)
      | ~ r1_tarski(k1_tarski(A_47),B_48) ) ),
    inference(resolution,[status(thm)],[c_76,c_101])).

tff(c_133,plain,(
    r2_hidden('#skF_4',k2_tarski('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_42,c_123])).

tff(c_34,plain,(
    ! [A_14,B_15] : k1_enumset1(A_14,A_14,B_15) = k2_tarski(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_194,plain,(
    ! [E_68,C_69,B_70,A_71] :
      ( E_68 = C_69
      | E_68 = B_70
      | E_68 = A_71
      | ~ r2_hidden(E_68,k1_enumset1(A_71,B_70,C_69)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_232,plain,(
    ! [E_75,B_76,A_77] :
      ( E_75 = B_76
      | E_75 = A_77
      | E_75 = A_77
      | ~ r2_hidden(E_75,k2_tarski(A_77,B_76)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_194])).

tff(c_239,plain,
    ( '#skF_6' = '#skF_4'
    | '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_133,c_232])).

tff(c_257,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_40,c_38,c_239])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.34  % Computer   : n002.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % DateTime   : Tue Dec  1 18:09:36 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.03/1.23  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.03/1.23  
% 2.03/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.03/1.23  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3 > #skF_1
% 2.03/1.23  
% 2.03/1.23  %Foreground sorts:
% 2.03/1.23  
% 2.03/1.23  
% 2.03/1.23  %Background operators:
% 2.03/1.23  
% 2.03/1.23  
% 2.03/1.23  %Foreground operators:
% 2.03/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.03/1.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.03/1.23  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.03/1.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.03/1.23  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.03/1.23  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.03/1.23  tff('#skF_5', type, '#skF_5': $i).
% 2.03/1.23  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.03/1.23  tff('#skF_6', type, '#skF_6': $i).
% 2.03/1.23  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.03/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.03/1.23  tff('#skF_4', type, '#skF_4': $i).
% 2.03/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.03/1.23  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 2.03/1.23  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.03/1.23  
% 2.03/1.24  tff(f_63, negated_conjecture, ~(![A, B, C]: ~((r1_tarski(k1_tarski(A), k2_tarski(B, C)) & ~(A = B)) & ~(A = C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_zfmisc_1)).
% 2.03/1.24  tff(f_49, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.03/1.24  tff(f_51, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.03/1.24  tff(f_47, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 2.03/1.24  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.03/1.24  tff(c_40, plain, ('#skF_5'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.03/1.24  tff(c_38, plain, ('#skF_6'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.03/1.24  tff(c_42, plain, (r1_tarski(k1_tarski('#skF_4'), k2_tarski('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.03/1.24  tff(c_32, plain, (![A_13]: (k2_tarski(A_13, A_13)=k1_tarski(A_13))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.03/1.24  tff(c_55, plain, (![A_29, B_30]: (k1_enumset1(A_29, A_29, B_30)=k2_tarski(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.03/1.24  tff(c_14, plain, (![E_12, B_7, C_8]: (r2_hidden(E_12, k1_enumset1(E_12, B_7, C_8)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.03/1.24  tff(c_73, plain, (![A_31, B_32]: (r2_hidden(A_31, k2_tarski(A_31, B_32)))), inference(superposition, [status(thm), theory('equality')], [c_55, c_14])).
% 2.03/1.24  tff(c_76, plain, (![A_13]: (r2_hidden(A_13, k1_tarski(A_13)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_73])).
% 2.03/1.24  tff(c_101, plain, (![C_44, B_45, A_46]: (r2_hidden(C_44, B_45) | ~r2_hidden(C_44, A_46) | ~r1_tarski(A_46, B_45))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.03/1.24  tff(c_123, plain, (![A_47, B_48]: (r2_hidden(A_47, B_48) | ~r1_tarski(k1_tarski(A_47), B_48))), inference(resolution, [status(thm)], [c_76, c_101])).
% 2.03/1.24  tff(c_133, plain, (r2_hidden('#skF_4', k2_tarski('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_42, c_123])).
% 2.03/1.24  tff(c_34, plain, (![A_14, B_15]: (k1_enumset1(A_14, A_14, B_15)=k2_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.03/1.24  tff(c_194, plain, (![E_68, C_69, B_70, A_71]: (E_68=C_69 | E_68=B_70 | E_68=A_71 | ~r2_hidden(E_68, k1_enumset1(A_71, B_70, C_69)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.03/1.24  tff(c_232, plain, (![E_75, B_76, A_77]: (E_75=B_76 | E_75=A_77 | E_75=A_77 | ~r2_hidden(E_75, k2_tarski(A_77, B_76)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_194])).
% 2.03/1.24  tff(c_239, plain, ('#skF_6'='#skF_4' | '#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_133, c_232])).
% 2.03/1.24  tff(c_257, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_40, c_38, c_239])).
% 2.03/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.03/1.24  
% 2.03/1.24  Inference rules
% 2.03/1.24  ----------------------
% 2.03/1.24  #Ref     : 0
% 2.03/1.24  #Sup     : 47
% 2.03/1.24  #Fact    : 0
% 2.03/1.24  #Define  : 0
% 2.03/1.24  #Split   : 0
% 2.03/1.24  #Chain   : 0
% 2.03/1.24  #Close   : 0
% 2.03/1.24  
% 2.03/1.24  Ordering : KBO
% 2.03/1.24  
% 2.03/1.24  Simplification rules
% 2.03/1.24  ----------------------
% 2.03/1.24  #Subsume      : 5
% 2.03/1.24  #Demod        : 9
% 2.03/1.24  #Tautology    : 19
% 2.03/1.24  #SimpNegUnit  : 1
% 2.03/1.24  #BackRed      : 0
% 2.03/1.24  
% 2.03/1.24  #Partial instantiations: 0
% 2.03/1.24  #Strategies tried      : 1
% 2.03/1.24  
% 2.03/1.24  Timing (in seconds)
% 2.03/1.24  ----------------------
% 2.07/1.25  Preprocessing        : 0.28
% 2.07/1.25  Parsing              : 0.14
% 2.07/1.25  CNF conversion       : 0.02
% 2.07/1.25  Main loop            : 0.18
% 2.07/1.25  Inferencing          : 0.06
% 2.07/1.25  Reduction            : 0.05
% 2.07/1.25  Demodulation         : 0.04
% 2.07/1.25  BG Simplification    : 0.02
% 2.07/1.25  Subsumption          : 0.03
% 2.07/1.25  Abstraction          : 0.01
% 2.07/1.25  MUC search           : 0.00
% 2.07/1.25  Cooper               : 0.00
% 2.07/1.25  Total                : 0.48
% 2.07/1.25  Index Insertion      : 0.00
% 2.07/1.25  Index Deletion       : 0.00
% 2.07/1.25  Index Matching       : 0.00
% 2.07/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
