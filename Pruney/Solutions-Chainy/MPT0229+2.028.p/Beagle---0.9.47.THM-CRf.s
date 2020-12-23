%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:57 EST 2020

% Result     : Theorem 1.85s
% Output     : CNFRefutation 1.85s
% Verified   : 
% Statistics : Number of formulae       :   30 (  36 expanded)
%              Number of leaves         :   18 (  22 expanded)
%              Depth                    :    6
%              Number of atoms          :   29 (  40 expanded)
%              Number of equality atoms :   12 (  20 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

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

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(f_52,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k1_tarski(A),k1_tarski(B))
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_zfmisc_1)).

tff(f_43,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

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

tff(c_32,plain,(
    '#skF_5' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_34,plain,(
    r1_tarski(k1_tarski('#skF_4'),k1_tarski('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_26,plain,(
    ! [A_12] : k2_tarski(A_12,A_12) = k1_tarski(A_12) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_44,plain,(
    ! [D_19,B_20] : r2_hidden(D_19,k2_tarski(D_19,B_20)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_47,plain,(
    ! [A_12] : r2_hidden(A_12,k1_tarski(A_12)) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_44])).

tff(c_80,plain,(
    ! [C_34,B_35,A_36] :
      ( r2_hidden(C_34,B_35)
      | ~ r2_hidden(C_34,A_36)
      | ~ r1_tarski(A_36,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_93,plain,(
    ! [A_37,B_38] :
      ( r2_hidden(A_37,B_38)
      | ~ r1_tarski(k1_tarski(A_37),B_38) ) ),
    inference(resolution,[status(thm)],[c_47,c_80])).

tff(c_103,plain,(
    r2_hidden('#skF_4',k1_tarski('#skF_5')) ),
    inference(resolution,[status(thm)],[c_34,c_93])).

tff(c_114,plain,(
    ! [D_40,B_41,A_42] :
      ( D_40 = B_41
      | D_40 = A_42
      | ~ r2_hidden(D_40,k2_tarski(A_42,B_41)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_153,plain,(
    ! [D_49,A_50] :
      ( D_49 = A_50
      | D_49 = A_50
      | ~ r2_hidden(D_49,k1_tarski(A_50)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_114])).

tff(c_156,plain,(
    '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_103,c_153])).

tff(c_167,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_32,c_156])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:59:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.85/1.19  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.85/1.19  
% 1.85/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.85/1.20  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 1.85/1.20  
% 1.85/1.20  %Foreground sorts:
% 1.85/1.20  
% 1.85/1.20  
% 1.85/1.20  %Background operators:
% 1.85/1.20  
% 1.85/1.20  
% 1.85/1.20  %Foreground operators:
% 1.85/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.85/1.20  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.85/1.20  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.85/1.20  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.85/1.20  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.85/1.20  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.85/1.20  tff('#skF_5', type, '#skF_5': $i).
% 1.85/1.20  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.85/1.20  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.85/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.85/1.20  tff('#skF_4', type, '#skF_4': $i).
% 1.85/1.20  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 1.85/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.85/1.20  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.85/1.20  
% 1.85/1.20  tff(f_52, negated_conjecture, ~(![A, B]: (r1_tarski(k1_tarski(A), k1_tarski(B)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_zfmisc_1)).
% 1.85/1.20  tff(f_43, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 1.85/1.20  tff(f_41, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 1.85/1.20  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 1.85/1.20  tff(c_32, plain, ('#skF_5'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.85/1.20  tff(c_34, plain, (r1_tarski(k1_tarski('#skF_4'), k1_tarski('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.85/1.20  tff(c_26, plain, (![A_12]: (k2_tarski(A_12, A_12)=k1_tarski(A_12))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.85/1.20  tff(c_44, plain, (![D_19, B_20]: (r2_hidden(D_19, k2_tarski(D_19, B_20)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.85/1.20  tff(c_47, plain, (![A_12]: (r2_hidden(A_12, k1_tarski(A_12)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_44])).
% 1.85/1.20  tff(c_80, plain, (![C_34, B_35, A_36]: (r2_hidden(C_34, B_35) | ~r2_hidden(C_34, A_36) | ~r1_tarski(A_36, B_35))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.85/1.20  tff(c_93, plain, (![A_37, B_38]: (r2_hidden(A_37, B_38) | ~r1_tarski(k1_tarski(A_37), B_38))), inference(resolution, [status(thm)], [c_47, c_80])).
% 1.85/1.20  tff(c_103, plain, (r2_hidden('#skF_4', k1_tarski('#skF_5'))), inference(resolution, [status(thm)], [c_34, c_93])).
% 1.85/1.20  tff(c_114, plain, (![D_40, B_41, A_42]: (D_40=B_41 | D_40=A_42 | ~r2_hidden(D_40, k2_tarski(A_42, B_41)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.85/1.20  tff(c_153, plain, (![D_49, A_50]: (D_49=A_50 | D_49=A_50 | ~r2_hidden(D_49, k1_tarski(A_50)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_114])).
% 1.85/1.20  tff(c_156, plain, ('#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_103, c_153])).
% 1.85/1.20  tff(c_167, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_32, c_156])).
% 1.85/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.85/1.20  
% 1.85/1.20  Inference rules
% 1.85/1.20  ----------------------
% 1.85/1.20  #Ref     : 0
% 1.85/1.20  #Sup     : 28
% 1.85/1.20  #Fact    : 0
% 1.85/1.20  #Define  : 0
% 1.85/1.20  #Split   : 0
% 1.85/1.20  #Chain   : 0
% 1.85/1.20  #Close   : 0
% 1.85/1.20  
% 1.85/1.20  Ordering : KBO
% 1.85/1.20  
% 1.85/1.20  Simplification rules
% 1.85/1.20  ----------------------
% 1.85/1.20  #Subsume      : 2
% 1.85/1.20  #Demod        : 5
% 1.85/1.20  #Tautology    : 13
% 1.85/1.20  #SimpNegUnit  : 1
% 1.85/1.20  #BackRed      : 0
% 1.85/1.20  
% 1.85/1.20  #Partial instantiations: 0
% 1.85/1.20  #Strategies tried      : 1
% 1.85/1.20  
% 1.85/1.20  Timing (in seconds)
% 1.85/1.20  ----------------------
% 1.85/1.21  Preprocessing        : 0.30
% 1.85/1.21  Parsing              : 0.16
% 1.85/1.21  CNF conversion       : 0.02
% 1.85/1.21  Main loop            : 0.13
% 1.85/1.21  Inferencing          : 0.05
% 1.85/1.21  Reduction            : 0.04
% 1.85/1.21  Demodulation         : 0.03
% 1.85/1.21  BG Simplification    : 0.01
% 1.85/1.21  Subsumption          : 0.02
% 1.85/1.21  Abstraction          : 0.01
% 1.85/1.21  MUC search           : 0.00
% 1.85/1.21  Cooper               : 0.00
% 1.85/1.21  Total                : 0.45
% 1.85/1.21  Index Insertion      : 0.00
% 1.85/1.21  Index Deletion       : 0.00
% 1.85/1.21  Index Matching       : 0.00
% 1.85/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
