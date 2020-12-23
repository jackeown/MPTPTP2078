%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:43 EST 2020

% Result     : Theorem 1.91s
% Output     : CNFRefutation 1.91s
% Verified   : 
% Statistics : Number of formulae       :   33 (  41 expanded)
%              Number of leaves         :   19 (  24 expanded)
%              Depth                    :    8
%              Number of atoms          :   26 (  43 expanded)
%              Number of equality atoms :   16 (  30 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_3 > #skF_5 > #skF_2 > #skF_6 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_58,negated_conjecture,(
    ~ ! [A,B,C] :
        ( k1_tarski(A) = k2_tarski(B,C)
       => B = C ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_40,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(c_44,plain,(
    '#skF_7' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_46,plain,(
    k2_tarski('#skF_6','#skF_7') = k1_tarski('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_70,plain,(
    ! [A_32,B_33] : k1_enumset1(A_32,A_32,B_33) = k2_tarski(A_32,B_33) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_8,plain,(
    ! [E_7,B_2,C_3] : r2_hidden(E_7,k1_enumset1(E_7,B_2,C_3)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_97,plain,(
    ! [A_37,B_38] : r2_hidden(A_37,k2_tarski(A_37,B_38)) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_8])).

tff(c_103,plain,(
    r2_hidden('#skF_6',k1_tarski('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_97])).

tff(c_26,plain,(
    ! [C_12,A_8] :
      ( C_12 = A_8
      | ~ r2_hidden(C_12,k1_tarski(A_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_108,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_103,c_26])).

tff(c_110,plain,(
    k2_tarski('#skF_6','#skF_7') = k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_46])).

tff(c_4,plain,(
    ! [E_7,A_1,B_2] : r2_hidden(E_7,k1_enumset1(A_1,B_2,E_7)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_79,plain,(
    ! [B_33,A_32] : r2_hidden(B_33,k2_tarski(A_32,B_33)) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_4])).

tff(c_260,plain,(
    r2_hidden('#skF_7',k1_tarski('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_79])).

tff(c_282,plain,(
    '#skF_7' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_260,c_26])).

tff(c_315,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_282])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n019.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:07:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.91/1.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.91/1.30  
% 1.91/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.91/1.31  %$ r2_hidden > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_3 > #skF_5 > #skF_2 > #skF_6 > #skF_1 > #skF_4
% 1.91/1.31  
% 1.91/1.31  %Foreground sorts:
% 1.91/1.31  
% 1.91/1.31  
% 1.91/1.31  %Background operators:
% 1.91/1.31  
% 1.91/1.31  
% 1.91/1.31  %Foreground operators:
% 1.91/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.91/1.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.91/1.31  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.91/1.31  tff('#skF_7', type, '#skF_7': $i).
% 1.91/1.31  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.91/1.31  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.91/1.31  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.91/1.31  tff('#skF_5', type, '#skF_5': $i).
% 1.91/1.31  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 1.91/1.31  tff('#skF_6', type, '#skF_6': $i).
% 1.91/1.31  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.91/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.91/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.91/1.31  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 1.91/1.31  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 1.91/1.31  
% 1.91/1.31  tff(f_58, negated_conjecture, ~(![A, B, C]: ((k1_tarski(A) = k2_tarski(B, C)) => (B = C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_zfmisc_1)).
% 1.91/1.31  tff(f_51, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 1.91/1.31  tff(f_40, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 1.91/1.31  tff(f_47, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 1.91/1.31  tff(c_44, plain, ('#skF_7'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.91/1.31  tff(c_46, plain, (k2_tarski('#skF_6', '#skF_7')=k1_tarski('#skF_5')), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.91/1.31  tff(c_70, plain, (![A_32, B_33]: (k1_enumset1(A_32, A_32, B_33)=k2_tarski(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.91/1.31  tff(c_8, plain, (![E_7, B_2, C_3]: (r2_hidden(E_7, k1_enumset1(E_7, B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.91/1.31  tff(c_97, plain, (![A_37, B_38]: (r2_hidden(A_37, k2_tarski(A_37, B_38)))), inference(superposition, [status(thm), theory('equality')], [c_70, c_8])).
% 1.91/1.31  tff(c_103, plain, (r2_hidden('#skF_6', k1_tarski('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_46, c_97])).
% 1.91/1.31  tff(c_26, plain, (![C_12, A_8]: (C_12=A_8 | ~r2_hidden(C_12, k1_tarski(A_8)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.91/1.31  tff(c_108, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_103, c_26])).
% 1.91/1.31  tff(c_110, plain, (k2_tarski('#skF_6', '#skF_7')=k1_tarski('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_108, c_46])).
% 1.91/1.31  tff(c_4, plain, (![E_7, A_1, B_2]: (r2_hidden(E_7, k1_enumset1(A_1, B_2, E_7)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.91/1.31  tff(c_79, plain, (![B_33, A_32]: (r2_hidden(B_33, k2_tarski(A_32, B_33)))), inference(superposition, [status(thm), theory('equality')], [c_70, c_4])).
% 1.91/1.31  tff(c_260, plain, (r2_hidden('#skF_7', k1_tarski('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_110, c_79])).
% 1.91/1.31  tff(c_282, plain, ('#skF_7'='#skF_6'), inference(resolution, [status(thm)], [c_260, c_26])).
% 1.91/1.31  tff(c_315, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_282])).
% 1.91/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.91/1.31  
% 1.91/1.31  Inference rules
% 1.91/1.31  ----------------------
% 1.91/1.31  #Ref     : 0
% 1.91/1.31  #Sup     : 38
% 1.91/1.31  #Fact    : 0
% 1.91/1.31  #Define  : 0
% 1.91/1.31  #Split   : 0
% 1.91/1.31  #Chain   : 0
% 1.91/1.31  #Close   : 0
% 1.91/1.31  
% 1.91/1.31  Ordering : KBO
% 1.91/1.31  
% 1.91/1.31  Simplification rules
% 1.91/1.31  ----------------------
% 1.91/1.32  #Subsume      : 0
% 1.91/1.32  #Demod        : 16
% 1.91/1.32  #Tautology    : 20
% 1.91/1.32  #SimpNegUnit  : 1
% 1.91/1.32  #BackRed      : 2
% 1.91/1.32  
% 1.91/1.32  #Partial instantiations: 176
% 1.91/1.32  #Strategies tried      : 1
% 1.91/1.32  
% 1.91/1.32  Timing (in seconds)
% 1.91/1.32  ----------------------
% 1.91/1.32  Preprocessing        : 0.32
% 1.91/1.32  Parsing              : 0.16
% 1.91/1.32  CNF conversion       : 0.03
% 1.91/1.32  Main loop            : 0.19
% 1.91/1.32  Inferencing          : 0.09
% 1.91/1.32  Reduction            : 0.05
% 1.91/1.32  Demodulation         : 0.04
% 1.91/1.32  BG Simplification    : 0.02
% 1.91/1.32  Subsumption          : 0.03
% 1.91/1.32  Abstraction          : 0.01
% 1.91/1.32  MUC search           : 0.00
% 1.91/1.32  Cooper               : 0.00
% 1.91/1.32  Total                : 0.53
% 1.91/1.32  Index Insertion      : 0.00
% 1.91/1.32  Index Deletion       : 0.00
% 1.91/1.32  Index Matching       : 0.00
% 1.91/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
