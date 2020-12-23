%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:41 EST 2020

% Result     : Theorem 1.74s
% Output     : CNFRefutation 1.84s
% Verified   : 
% Statistics : Number of formulae       :   26 (  30 expanded)
%              Number of leaves         :   17 (  20 expanded)
%              Depth                    :    4
%              Number of atoms          :   20 (  29 expanded)
%              Number of equality atoms :   14 (  22 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k1_enumset1 > k2_tarski > #nlpp > k1_tarski > #skF_4 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(f_58,negated_conjecture,(
    ~ ! [A,B,C] :
        ( k1_tarski(A) = k2_tarski(B,C)
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_51,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(c_48,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_50,plain,(
    k2_tarski('#skF_6','#skF_7') = k1_tarski('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_64,plain,(
    ! [D_18,B_19] : r2_hidden(D_18,k2_tarski(D_18,B_19)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_70,plain,(
    r2_hidden('#skF_6',k1_tarski('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_64])).

tff(c_44,plain,(
    ! [A_14] : k2_tarski(A_14,A_14) = k1_tarski(A_14) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_104,plain,(
    ! [D_34,B_35,A_36] :
      ( D_34 = B_35
      | D_34 = A_36
      | ~ r2_hidden(D_34,k2_tarski(A_36,B_35)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_121,plain,(
    ! [D_37,A_38] :
      ( D_37 = A_38
      | D_37 = A_38
      | ~ r2_hidden(D_37,k1_tarski(A_38)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_104])).

tff(c_127,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_70,c_121])).

tff(c_135,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_48,c_127])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:07:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.74/1.15  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.74/1.15  
% 1.74/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.84/1.15  %$ r2_hidden > k1_enumset1 > k2_tarski > #nlpp > k1_tarski > #skF_4 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_1
% 1.84/1.15  
% 1.84/1.15  %Foreground sorts:
% 1.84/1.15  
% 1.84/1.15  
% 1.84/1.15  %Background operators:
% 1.84/1.15  
% 1.84/1.15  
% 1.84/1.15  %Foreground operators:
% 1.84/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.84/1.15  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.84/1.15  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.84/1.15  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 1.84/1.15  tff('#skF_7', type, '#skF_7': $i).
% 1.84/1.15  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.84/1.15  tff('#skF_5', type, '#skF_5': $i).
% 1.84/1.15  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 1.84/1.15  tff('#skF_6', type, '#skF_6': $i).
% 1.84/1.15  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.84/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.84/1.15  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 1.84/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.84/1.15  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 1.84/1.15  
% 1.84/1.16  tff(f_58, negated_conjecture, ~(![A, B, C]: ((k1_tarski(A) = k2_tarski(B, C)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_zfmisc_1)).
% 1.84/1.16  tff(f_49, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 1.84/1.16  tff(f_51, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 1.84/1.16  tff(c_48, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.84/1.16  tff(c_50, plain, (k2_tarski('#skF_6', '#skF_7')=k1_tarski('#skF_5')), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.84/1.16  tff(c_64, plain, (![D_18, B_19]: (r2_hidden(D_18, k2_tarski(D_18, B_19)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.84/1.16  tff(c_70, plain, (r2_hidden('#skF_6', k1_tarski('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_50, c_64])).
% 1.84/1.16  tff(c_44, plain, (![A_14]: (k2_tarski(A_14, A_14)=k1_tarski(A_14))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.84/1.16  tff(c_104, plain, (![D_34, B_35, A_36]: (D_34=B_35 | D_34=A_36 | ~r2_hidden(D_34, k2_tarski(A_36, B_35)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.84/1.16  tff(c_121, plain, (![D_37, A_38]: (D_37=A_38 | D_37=A_38 | ~r2_hidden(D_37, k1_tarski(A_38)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_104])).
% 1.84/1.16  tff(c_127, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_70, c_121])).
% 1.84/1.16  tff(c_135, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_48, c_127])).
% 1.84/1.16  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.84/1.16  
% 1.84/1.16  Inference rules
% 1.84/1.16  ----------------------
% 1.84/1.16  #Ref     : 0
% 1.84/1.16  #Sup     : 20
% 1.84/1.16  #Fact    : 0
% 1.84/1.16  #Define  : 0
% 1.84/1.16  #Split   : 0
% 1.84/1.16  #Chain   : 0
% 1.84/1.16  #Close   : 0
% 1.84/1.16  
% 1.84/1.16  Ordering : KBO
% 1.84/1.16  
% 1.84/1.16  Simplification rules
% 1.84/1.16  ----------------------
% 1.84/1.16  #Subsume      : 0
% 1.84/1.16  #Demod        : 4
% 1.84/1.16  #Tautology    : 12
% 1.84/1.16  #SimpNegUnit  : 1
% 1.84/1.16  #BackRed      : 0
% 1.84/1.16  
% 1.84/1.16  #Partial instantiations: 0
% 1.84/1.16  #Strategies tried      : 1
% 1.84/1.16  
% 1.84/1.16  Timing (in seconds)
% 1.84/1.16  ----------------------
% 1.84/1.16  Preprocessing        : 0.29
% 1.84/1.16  Parsing              : 0.14
% 1.84/1.16  CNF conversion       : 0.02
% 1.84/1.16  Main loop            : 0.12
% 1.84/1.16  Inferencing          : 0.03
% 1.84/1.16  Reduction            : 0.04
% 1.84/1.16  Demodulation         : 0.03
% 1.84/1.16  BG Simplification    : 0.02
% 1.84/1.16  Subsumption          : 0.03
% 1.84/1.16  Abstraction          : 0.01
% 1.84/1.16  MUC search           : 0.00
% 1.84/1.16  Cooper               : 0.00
% 1.84/1.16  Total                : 0.43
% 1.84/1.16  Index Insertion      : 0.00
% 1.84/1.16  Index Deletion       : 0.00
% 1.84/1.16  Index Matching       : 0.00
% 1.84/1.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
