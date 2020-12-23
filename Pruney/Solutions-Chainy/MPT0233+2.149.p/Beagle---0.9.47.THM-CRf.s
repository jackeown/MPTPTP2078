%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:40 EST 2020

% Result     : Theorem 1.85s
% Output     : CNFRefutation 1.85s
% Verified   : 
% Statistics : Number of formulae       :   34 (  39 expanded)
%              Number of leaves         :   18 (  23 expanded)
%              Depth                    :    8
%              Number of atoms          :   43 (  58 expanded)
%              Number of equality atoms :   10 (  14 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_57,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ~ ( r1_tarski(k2_tarski(A,B),k2_tarski(C,D))
          & A != C
          & A != D ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B] : r1_tarski(k1_tarski(A),k2_tarski(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ~ ( r1_tarski(k1_tarski(A),k2_tarski(B,C))
        & A != B
        & A != C ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_zfmisc_1)).

tff(c_18,plain,(
    '#skF_2' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_16,plain,(
    '#skF_5' != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_12,plain,(
    ! [A_11,B_12] : r1_tarski(k1_tarski(A_11),k2_tarski(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_20,plain,(
    r1_tarski(k2_tarski('#skF_2','#skF_3'),k2_tarski('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_39,plain,(
    ! [C_25,B_26,A_27] :
      ( r2_hidden(C_25,B_26)
      | ~ r2_hidden(C_25,A_27)
      | ~ r1_tarski(A_27,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_58,plain,(
    ! [A_34,B_35,B_36] :
      ( r2_hidden('#skF_1'(A_34,B_35),B_36)
      | ~ r1_tarski(A_34,B_36)
      | r1_tarski(A_34,B_35) ) ),
    inference(resolution,[status(thm)],[c_6,c_39])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_67,plain,(
    ! [A_37,B_38,B_39,B_40] :
      ( r2_hidden('#skF_1'(A_37,B_38),B_39)
      | ~ r1_tarski(B_40,B_39)
      | ~ r1_tarski(A_37,B_40)
      | r1_tarski(A_37,B_38) ) ),
    inference(resolution,[status(thm)],[c_58,c_2])).

tff(c_95,plain,(
    ! [A_48,B_49] :
      ( r2_hidden('#skF_1'(A_48,B_49),k2_tarski('#skF_4','#skF_5'))
      | ~ r1_tarski(A_48,k2_tarski('#skF_2','#skF_3'))
      | r1_tarski(A_48,B_49) ) ),
    inference(resolution,[status(thm)],[c_20,c_67])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_110,plain,(
    ! [A_53] :
      ( ~ r1_tarski(A_53,k2_tarski('#skF_2','#skF_3'))
      | r1_tarski(A_53,k2_tarski('#skF_4','#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_95,c_4])).

tff(c_126,plain,(
    r1_tarski(k1_tarski('#skF_2'),k2_tarski('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_12,c_110])).

tff(c_14,plain,(
    ! [C_15,A_13,B_14] :
      ( C_15 = A_13
      | B_14 = A_13
      | ~ r1_tarski(k1_tarski(A_13),k2_tarski(B_14,C_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_131,plain,
    ( '#skF_5' = '#skF_2'
    | '#skF_2' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_126,c_14])).

tff(c_136,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_16,c_131])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:33:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.85/1.18  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.85/1.18  
% 1.85/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.85/1.18  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 1.85/1.18  
% 1.85/1.18  %Foreground sorts:
% 1.85/1.18  
% 1.85/1.18  
% 1.85/1.18  %Background operators:
% 1.85/1.18  
% 1.85/1.18  
% 1.85/1.18  %Foreground operators:
% 1.85/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.85/1.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.85/1.18  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.85/1.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.85/1.18  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.85/1.18  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.85/1.18  tff('#skF_5', type, '#skF_5': $i).
% 1.85/1.18  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.85/1.18  tff('#skF_2', type, '#skF_2': $i).
% 1.85/1.18  tff('#skF_3', type, '#skF_3': $i).
% 1.85/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.85/1.18  tff('#skF_4', type, '#skF_4': $i).
% 1.85/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.85/1.18  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.85/1.18  
% 1.85/1.19  tff(f_57, negated_conjecture, ~(![A, B, C, D]: ~((r1_tarski(k2_tarski(A, B), k2_tarski(C, D)) & ~(A = C)) & ~(A = D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_zfmisc_1)).
% 1.85/1.19  tff(f_38, axiom, (![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 1.85/1.19  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 1.85/1.19  tff(f_47, axiom, (![A, B, C]: ~((r1_tarski(k1_tarski(A), k2_tarski(B, C)) & ~(A = B)) & ~(A = C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_zfmisc_1)).
% 1.85/1.19  tff(c_18, plain, ('#skF_2'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.85/1.19  tff(c_16, plain, ('#skF_5'!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.85/1.19  tff(c_12, plain, (![A_11, B_12]: (r1_tarski(k1_tarski(A_11), k2_tarski(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.85/1.19  tff(c_20, plain, (r1_tarski(k2_tarski('#skF_2', '#skF_3'), k2_tarski('#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.85/1.19  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.85/1.19  tff(c_39, plain, (![C_25, B_26, A_27]: (r2_hidden(C_25, B_26) | ~r2_hidden(C_25, A_27) | ~r1_tarski(A_27, B_26))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.85/1.19  tff(c_58, plain, (![A_34, B_35, B_36]: (r2_hidden('#skF_1'(A_34, B_35), B_36) | ~r1_tarski(A_34, B_36) | r1_tarski(A_34, B_35))), inference(resolution, [status(thm)], [c_6, c_39])).
% 1.85/1.19  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.85/1.19  tff(c_67, plain, (![A_37, B_38, B_39, B_40]: (r2_hidden('#skF_1'(A_37, B_38), B_39) | ~r1_tarski(B_40, B_39) | ~r1_tarski(A_37, B_40) | r1_tarski(A_37, B_38))), inference(resolution, [status(thm)], [c_58, c_2])).
% 1.85/1.19  tff(c_95, plain, (![A_48, B_49]: (r2_hidden('#skF_1'(A_48, B_49), k2_tarski('#skF_4', '#skF_5')) | ~r1_tarski(A_48, k2_tarski('#skF_2', '#skF_3')) | r1_tarski(A_48, B_49))), inference(resolution, [status(thm)], [c_20, c_67])).
% 1.85/1.19  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.85/1.19  tff(c_110, plain, (![A_53]: (~r1_tarski(A_53, k2_tarski('#skF_2', '#skF_3')) | r1_tarski(A_53, k2_tarski('#skF_4', '#skF_5')))), inference(resolution, [status(thm)], [c_95, c_4])).
% 1.85/1.19  tff(c_126, plain, (r1_tarski(k1_tarski('#skF_2'), k2_tarski('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_12, c_110])).
% 1.85/1.19  tff(c_14, plain, (![C_15, A_13, B_14]: (C_15=A_13 | B_14=A_13 | ~r1_tarski(k1_tarski(A_13), k2_tarski(B_14, C_15)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.85/1.19  tff(c_131, plain, ('#skF_5'='#skF_2' | '#skF_2'='#skF_4'), inference(resolution, [status(thm)], [c_126, c_14])).
% 1.85/1.19  tff(c_136, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_16, c_131])).
% 1.85/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.85/1.19  
% 1.85/1.19  Inference rules
% 1.85/1.19  ----------------------
% 1.85/1.19  #Ref     : 0
% 1.85/1.19  #Sup     : 24
% 1.85/1.19  #Fact    : 0
% 1.85/1.19  #Define  : 0
% 1.85/1.19  #Split   : 0
% 1.85/1.19  #Chain   : 0
% 1.85/1.19  #Close   : 0
% 1.85/1.19  
% 1.85/1.19  Ordering : KBO
% 1.85/1.19  
% 1.85/1.19  Simplification rules
% 1.85/1.19  ----------------------
% 1.85/1.19  #Subsume      : 1
% 1.85/1.19  #Demod        : 1
% 1.85/1.19  #Tautology    : 8
% 1.85/1.19  #SimpNegUnit  : 1
% 1.85/1.19  #BackRed      : 0
% 1.85/1.19  
% 1.85/1.19  #Partial instantiations: 0
% 1.85/1.19  #Strategies tried      : 1
% 1.85/1.19  
% 1.85/1.19  Timing (in seconds)
% 1.85/1.19  ----------------------
% 1.85/1.19  Preprocessing        : 0.28
% 1.85/1.19  Parsing              : 0.15
% 1.85/1.19  CNF conversion       : 0.02
% 1.85/1.19  Main loop            : 0.15
% 1.85/1.19  Inferencing          : 0.06
% 1.85/1.19  Reduction            : 0.04
% 1.85/1.19  Demodulation         : 0.03
% 1.85/1.19  BG Simplification    : 0.01
% 1.85/1.19  Subsumption          : 0.03
% 1.85/1.19  Abstraction          : 0.01
% 1.85/1.19  MUC search           : 0.00
% 1.85/1.19  Cooper               : 0.00
% 1.85/1.19  Total                : 0.45
% 1.85/1.19  Index Insertion      : 0.00
% 1.85/1.19  Index Deletion       : 0.00
% 1.85/1.19  Index Matching       : 0.00
% 1.85/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
