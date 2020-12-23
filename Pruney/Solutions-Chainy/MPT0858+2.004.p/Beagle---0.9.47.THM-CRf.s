%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:56 EST 2020

% Result     : Theorem 1.96s
% Output     : CNFRefutation 1.96s
% Verified   : 
% Statistics : Number of formulae       :   35 (  43 expanded)
%              Number of leaves         :   21 (  25 expanded)
%              Depth                    :    4
%              Number of atoms          :   35 (  53 expanded)
%              Number of equality atoms :   19 (  32 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4

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

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(f_59,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r2_hidden(A,k2_zfmisc_1(k1_tarski(B),k1_tarski(C)))
       => ( k1_mcart_1(A) = B
          & k2_mcart_1(A) = C ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_mcart_1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(k1_tarski(B),C))
     => ( k1_mcart_1(A) = B
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_mcart_1)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_36,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(c_34,plain,
    ( k2_mcart_1('#skF_3') != '#skF_5'
    | k1_mcart_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_56,plain,(
    k1_mcart_1('#skF_3') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_36,plain,(
    r2_hidden('#skF_3',k2_zfmisc_1(k1_tarski('#skF_4'),k1_tarski('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_75,plain,(
    ! [A_30,B_31,C_32] :
      ( k1_mcart_1(A_30) = B_31
      | ~ r2_hidden(A_30,k2_zfmisc_1(k1_tarski(B_31),C_32)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_78,plain,(
    k1_mcart_1('#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_36,c_75])).

tff(c_82,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_78])).

tff(c_83,plain,(
    k2_mcart_1('#skF_3') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_129,plain,(
    ! [A_46,C_47,B_48] :
      ( r2_hidden(k2_mcart_1(A_46),C_47)
      | ~ r2_hidden(A_46,k2_zfmisc_1(B_48,C_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_132,plain,(
    r2_hidden(k2_mcart_1('#skF_3'),k1_tarski('#skF_5')) ),
    inference(resolution,[status(thm)],[c_36,c_129])).

tff(c_20,plain,(
    ! [A_7] : k2_tarski(A_7,A_7) = k1_tarski(A_7) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_104,plain,(
    ! [D_38,B_39,A_40] :
      ( D_38 = B_39
      | D_38 = A_40
      | ~ r2_hidden(D_38,k2_tarski(A_40,B_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_113,plain,(
    ! [D_38,A_7] :
      ( D_38 = A_7
      | D_38 = A_7
      | ~ r2_hidden(D_38,k1_tarski(A_7)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_104])).

tff(c_135,plain,(
    k2_mcart_1('#skF_3') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_132,c_113])).

tff(c_139,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_83,c_83,c_135])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n016.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 18:58:49 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.96/1.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.96/1.25  
% 1.96/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.96/1.25  %$ r2_hidden > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4
% 1.96/1.25  
% 1.96/1.25  %Foreground sorts:
% 1.96/1.25  
% 1.96/1.25  
% 1.96/1.25  %Background operators:
% 1.96/1.25  
% 1.96/1.25  
% 1.96/1.25  %Foreground operators:
% 1.96/1.25  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.96/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.96/1.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.96/1.25  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.96/1.25  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.96/1.25  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.96/1.25  tff('#skF_5', type, '#skF_5': $i).
% 1.96/1.25  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.96/1.25  tff('#skF_3', type, '#skF_3': $i).
% 1.96/1.25  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.96/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.96/1.25  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 1.96/1.25  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.96/1.25  tff('#skF_4', type, '#skF_4': $i).
% 1.96/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.96/1.25  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 1.96/1.25  
% 1.96/1.26  tff(f_59, negated_conjecture, ~(![A, B, C]: (r2_hidden(A, k2_zfmisc_1(k1_tarski(B), k1_tarski(C))) => ((k1_mcart_1(A) = B) & (k2_mcart_1(A) = C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_mcart_1)).
% 1.96/1.26  tff(f_52, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(k1_tarski(B), C)) => ((k1_mcart_1(A) = B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_mcart_1)).
% 1.96/1.26  tff(f_46, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_mcart_1)).
% 1.96/1.26  tff(f_36, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 1.96/1.26  tff(f_34, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 1.96/1.26  tff(c_34, plain, (k2_mcart_1('#skF_3')!='#skF_5' | k1_mcart_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.96/1.26  tff(c_56, plain, (k1_mcart_1('#skF_3')!='#skF_4'), inference(splitLeft, [status(thm)], [c_34])).
% 1.96/1.26  tff(c_36, plain, (r2_hidden('#skF_3', k2_zfmisc_1(k1_tarski('#skF_4'), k1_tarski('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.96/1.26  tff(c_75, plain, (![A_30, B_31, C_32]: (k1_mcart_1(A_30)=B_31 | ~r2_hidden(A_30, k2_zfmisc_1(k1_tarski(B_31), C_32)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.96/1.26  tff(c_78, plain, (k1_mcart_1('#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_36, c_75])).
% 1.96/1.26  tff(c_82, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_78])).
% 1.96/1.26  tff(c_83, plain, (k2_mcart_1('#skF_3')!='#skF_5'), inference(splitRight, [status(thm)], [c_34])).
% 1.96/1.26  tff(c_129, plain, (![A_46, C_47, B_48]: (r2_hidden(k2_mcart_1(A_46), C_47) | ~r2_hidden(A_46, k2_zfmisc_1(B_48, C_47)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.96/1.26  tff(c_132, plain, (r2_hidden(k2_mcart_1('#skF_3'), k1_tarski('#skF_5'))), inference(resolution, [status(thm)], [c_36, c_129])).
% 1.96/1.26  tff(c_20, plain, (![A_7]: (k2_tarski(A_7, A_7)=k1_tarski(A_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.96/1.26  tff(c_104, plain, (![D_38, B_39, A_40]: (D_38=B_39 | D_38=A_40 | ~r2_hidden(D_38, k2_tarski(A_40, B_39)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.96/1.26  tff(c_113, plain, (![D_38, A_7]: (D_38=A_7 | D_38=A_7 | ~r2_hidden(D_38, k1_tarski(A_7)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_104])).
% 1.96/1.26  tff(c_135, plain, (k2_mcart_1('#skF_3')='#skF_5'), inference(resolution, [status(thm)], [c_132, c_113])).
% 1.96/1.26  tff(c_139, plain, $false, inference(negUnitSimplification, [status(thm)], [c_83, c_83, c_135])).
% 1.96/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.96/1.26  
% 1.96/1.26  Inference rules
% 1.96/1.26  ----------------------
% 1.96/1.26  #Ref     : 0
% 1.96/1.26  #Sup     : 21
% 1.96/1.26  #Fact    : 0
% 1.96/1.26  #Define  : 0
% 1.96/1.26  #Split   : 1
% 1.96/1.26  #Chain   : 0
% 1.96/1.26  #Close   : 0
% 1.96/1.26  
% 1.96/1.26  Ordering : KBO
% 1.96/1.26  
% 1.96/1.26  Simplification rules
% 1.96/1.26  ----------------------
% 1.96/1.26  #Subsume      : 1
% 1.96/1.26  #Demod        : 4
% 1.96/1.26  #Tautology    : 16
% 1.96/1.26  #SimpNegUnit  : 2
% 1.96/1.26  #BackRed      : 0
% 1.96/1.26  
% 1.96/1.26  #Partial instantiations: 0
% 1.96/1.26  #Strategies tried      : 1
% 1.96/1.26  
% 1.96/1.26  Timing (in seconds)
% 1.96/1.26  ----------------------
% 1.96/1.26  Preprocessing        : 0.31
% 1.96/1.26  Parsing              : 0.16
% 1.96/1.26  CNF conversion       : 0.02
% 1.96/1.26  Main loop            : 0.12
% 1.96/1.26  Inferencing          : 0.04
% 1.96/1.26  Reduction            : 0.04
% 1.96/1.26  Demodulation         : 0.03
% 1.96/1.26  BG Simplification    : 0.01
% 1.96/1.26  Subsumption          : 0.02
% 1.96/1.26  Abstraction          : 0.01
% 1.96/1.26  MUC search           : 0.00
% 1.96/1.26  Cooper               : 0.00
% 1.96/1.26  Total                : 0.45
% 1.96/1.26  Index Insertion      : 0.00
% 1.96/1.26  Index Deletion       : 0.00
% 1.96/1.26  Index Matching       : 0.00
% 1.96/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
