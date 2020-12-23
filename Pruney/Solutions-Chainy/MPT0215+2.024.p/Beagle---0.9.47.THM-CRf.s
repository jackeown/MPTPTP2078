%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:41 EST 2020

% Result     : Theorem 1.63s
% Output     : CNFRefutation 1.76s
% Verified   : 
% Statistics : Number of formulae       :   25 (  29 expanded)
%              Number of leaves         :   16 (  19 expanded)
%              Depth                    :    4
%              Number of atoms          :   20 (  29 expanded)
%              Number of equality atoms :   14 (  22 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff(f_45,negated_conjecture,(
    ~ ! [A,B,C] :
        ( k1_tarski(A) = k2_tarski(B,C)
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_36,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(c_26,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_28,plain,(
    k2_tarski('#skF_4','#skF_5') = k1_tarski('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_42,plain,(
    ! [D_14,B_15] : r2_hidden(D_14,k2_tarski(D_14,B_15)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_48,plain,(
    r2_hidden('#skF_4',k1_tarski('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_42])).

tff(c_20,plain,(
    ! [A_7] : k2_tarski(A_7,A_7) = k1_tarski(A_7) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_76,plain,(
    ! [D_24,B_25,A_26] :
      ( D_24 = B_25
      | D_24 = A_26
      | ~ r2_hidden(D_24,k2_tarski(A_26,B_25)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_93,plain,(
    ! [D_27,A_28] :
      ( D_27 = A_28
      | D_27 = A_28
      | ~ r2_hidden(D_27,k1_tarski(A_28)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_76])).

tff(c_99,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_48,c_93])).

tff(c_107,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_26,c_99])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n014.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:50:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.63/1.15  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.76/1.15  
% 1.76/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.76/1.15  %$ r2_hidden > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4
% 1.76/1.15  
% 1.76/1.15  %Foreground sorts:
% 1.76/1.15  
% 1.76/1.15  
% 1.76/1.15  %Background operators:
% 1.76/1.15  
% 1.76/1.15  
% 1.76/1.15  %Foreground operators:
% 1.76/1.15  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.76/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.76/1.15  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.76/1.15  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.76/1.15  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.76/1.15  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.76/1.15  tff('#skF_5', type, '#skF_5': $i).
% 1.76/1.15  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.76/1.15  tff('#skF_3', type, '#skF_3': $i).
% 1.76/1.15  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.76/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.76/1.15  tff('#skF_4', type, '#skF_4': $i).
% 1.76/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.76/1.15  
% 1.76/1.16  tff(f_45, negated_conjecture, ~(![A, B, C]: ((k1_tarski(A) = k2_tarski(B, C)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_zfmisc_1)).
% 1.76/1.16  tff(f_34, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 1.76/1.16  tff(f_36, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 1.76/1.16  tff(c_26, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.76/1.16  tff(c_28, plain, (k2_tarski('#skF_4', '#skF_5')=k1_tarski('#skF_3')), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.76/1.16  tff(c_42, plain, (![D_14, B_15]: (r2_hidden(D_14, k2_tarski(D_14, B_15)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.76/1.16  tff(c_48, plain, (r2_hidden('#skF_4', k1_tarski('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_28, c_42])).
% 1.76/1.16  tff(c_20, plain, (![A_7]: (k2_tarski(A_7, A_7)=k1_tarski(A_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.76/1.16  tff(c_76, plain, (![D_24, B_25, A_26]: (D_24=B_25 | D_24=A_26 | ~r2_hidden(D_24, k2_tarski(A_26, B_25)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.76/1.16  tff(c_93, plain, (![D_27, A_28]: (D_27=A_28 | D_27=A_28 | ~r2_hidden(D_27, k1_tarski(A_28)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_76])).
% 1.76/1.16  tff(c_99, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_48, c_93])).
% 1.76/1.16  tff(c_107, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_26, c_99])).
% 1.76/1.16  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.76/1.16  
% 1.76/1.16  Inference rules
% 1.76/1.16  ----------------------
% 1.76/1.16  #Ref     : 0
% 1.76/1.16  #Sup     : 19
% 1.76/1.16  #Fact    : 0
% 1.76/1.16  #Define  : 0
% 1.76/1.16  #Split   : 0
% 1.76/1.16  #Chain   : 0
% 1.76/1.16  #Close   : 0
% 1.76/1.16  
% 1.76/1.16  Ordering : KBO
% 1.76/1.16  
% 1.76/1.16  Simplification rules
% 1.76/1.16  ----------------------
% 1.76/1.16  #Subsume      : 0
% 1.76/1.16  #Demod        : 1
% 1.76/1.16  #Tautology    : 11
% 1.76/1.16  #SimpNegUnit  : 1
% 1.76/1.16  #BackRed      : 0
% 1.76/1.16  
% 1.76/1.16  #Partial instantiations: 0
% 1.76/1.16  #Strategies tried      : 1
% 1.76/1.16  
% 1.76/1.16  Timing (in seconds)
% 1.76/1.16  ----------------------
% 1.76/1.16  Preprocessing        : 0.29
% 1.76/1.16  Parsing              : 0.14
% 1.76/1.16  CNF conversion       : 0.02
% 1.76/1.16  Main loop            : 0.10
% 1.76/1.16  Inferencing          : 0.04
% 1.76/1.16  Reduction            : 0.03
% 1.76/1.17  Demodulation         : 0.02
% 1.76/1.17  BG Simplification    : 0.01
% 1.76/1.17  Subsumption          : 0.02
% 1.76/1.17  Abstraction          : 0.01
% 1.76/1.17  MUC search           : 0.00
% 1.76/1.17  Cooper               : 0.00
% 1.76/1.17  Total                : 0.41
% 1.76/1.17  Index Insertion      : 0.00
% 1.76/1.17  Index Deletion       : 0.00
% 1.76/1.17  Index Matching       : 0.00
% 1.76/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
