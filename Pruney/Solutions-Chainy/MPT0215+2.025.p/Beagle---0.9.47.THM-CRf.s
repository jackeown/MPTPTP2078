%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:41 EST 2020

% Result     : Theorem 1.64s
% Output     : CNFRefutation 1.64s
% Verified   : 
% Statistics : Number of formulae       :   24 (  28 expanded)
%              Number of leaves         :   15 (  18 expanded)
%              Depth                    :    4
%              Number of atoms          :   20 (  29 expanded)
%              Number of equality atoms :   14 (  22 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4

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

tff(f_43,negated_conjecture,(
    ~ ! [A,B,C] :
        ( k1_tarski(A) = k2_tarski(B,C)
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_36,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(c_24,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_26,plain,(
    k2_tarski('#skF_4','#skF_5') = k1_tarski('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_40,plain,(
    ! [D_11,B_12] : r2_hidden(D_11,k2_tarski(D_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_46,plain,(
    r2_hidden('#skF_4',k1_tarski('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_40])).

tff(c_20,plain,(
    ! [A_7] : k2_tarski(A_7,A_7) = k1_tarski(A_7) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_65,plain,(
    ! [D_18,B_19,A_20] :
      ( D_18 = B_19
      | D_18 = A_20
      | ~ r2_hidden(D_18,k2_tarski(A_20,B_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_82,plain,(
    ! [D_21,A_22] :
      ( D_21 = A_22
      | D_21 = A_22
      | ~ r2_hidden(D_21,k1_tarski(A_22)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_65])).

tff(c_88,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_46,c_82])).

tff(c_96,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_24,c_88])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:26:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.64/1.18  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.64/1.18  
% 1.64/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.64/1.18  %$ r2_hidden > k2_enumset1 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4
% 1.64/1.18  
% 1.64/1.18  %Foreground sorts:
% 1.64/1.18  
% 1.64/1.18  
% 1.64/1.18  %Background operators:
% 1.64/1.18  
% 1.64/1.18  
% 1.64/1.18  %Foreground operators:
% 1.64/1.18  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.64/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.64/1.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.64/1.18  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.64/1.18  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.64/1.18  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.64/1.18  tff('#skF_5', type, '#skF_5': $i).
% 1.64/1.18  tff('#skF_3', type, '#skF_3': $i).
% 1.64/1.18  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.64/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.64/1.18  tff('#skF_4', type, '#skF_4': $i).
% 1.64/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.64/1.18  
% 1.64/1.19  tff(f_43, negated_conjecture, ~(![A, B, C]: ((k1_tarski(A) = k2_tarski(B, C)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_zfmisc_1)).
% 1.64/1.19  tff(f_34, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 1.64/1.19  tff(f_36, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 1.64/1.19  tff(c_24, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.64/1.19  tff(c_26, plain, (k2_tarski('#skF_4', '#skF_5')=k1_tarski('#skF_3')), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.64/1.19  tff(c_40, plain, (![D_11, B_12]: (r2_hidden(D_11, k2_tarski(D_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.64/1.19  tff(c_46, plain, (r2_hidden('#skF_4', k1_tarski('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_26, c_40])).
% 1.64/1.19  tff(c_20, plain, (![A_7]: (k2_tarski(A_7, A_7)=k1_tarski(A_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.64/1.19  tff(c_65, plain, (![D_18, B_19, A_20]: (D_18=B_19 | D_18=A_20 | ~r2_hidden(D_18, k2_tarski(A_20, B_19)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.64/1.19  tff(c_82, plain, (![D_21, A_22]: (D_21=A_22 | D_21=A_22 | ~r2_hidden(D_21, k1_tarski(A_22)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_65])).
% 1.64/1.19  tff(c_88, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_46, c_82])).
% 1.64/1.19  tff(c_96, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_24, c_88])).
% 1.64/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.64/1.19  
% 1.64/1.19  Inference rules
% 1.64/1.19  ----------------------
% 1.64/1.19  #Ref     : 0
% 1.64/1.19  #Sup     : 17
% 1.64/1.19  #Fact    : 0
% 1.64/1.19  #Define  : 0
% 1.64/1.19  #Split   : 0
% 1.64/1.19  #Chain   : 0
% 1.64/1.19  #Close   : 0
% 1.64/1.19  
% 1.64/1.19  Ordering : KBO
% 1.64/1.19  
% 1.64/1.19  Simplification rules
% 1.64/1.19  ----------------------
% 1.64/1.19  #Subsume      : 0
% 1.64/1.19  #Demod        : 1
% 1.64/1.19  #Tautology    : 9
% 1.64/1.19  #SimpNegUnit  : 1
% 1.64/1.19  #BackRed      : 0
% 1.64/1.19  
% 1.64/1.19  #Partial instantiations: 0
% 1.64/1.19  #Strategies tried      : 1
% 1.64/1.19  
% 1.64/1.19  Timing (in seconds)
% 1.64/1.19  ----------------------
% 1.64/1.19  Preprocessing        : 0.29
% 1.64/1.19  Parsing              : 0.15
% 1.64/1.19  CNF conversion       : 0.02
% 1.64/1.19  Main loop            : 0.09
% 1.64/1.19  Inferencing          : 0.03
% 1.64/1.19  Reduction            : 0.03
% 1.64/1.19  Demodulation         : 0.02
% 1.64/1.19  BG Simplification    : 0.01
% 1.64/1.19  Subsumption          : 0.02
% 1.64/1.19  Abstraction          : 0.01
% 1.64/1.19  MUC search           : 0.00
% 1.64/1.19  Cooper               : 0.00
% 1.64/1.19  Total                : 0.40
% 1.64/1.19  Index Insertion      : 0.00
% 1.64/1.19  Index Deletion       : 0.00
% 1.64/1.19  Index Matching       : 0.00
% 1.64/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
