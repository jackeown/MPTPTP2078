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
% DateTime   : Thu Dec  3 10:09:00 EST 2020

% Result     : Theorem 1.75s
% Output     : CNFRefutation 1.81s
% Verified   : 
% Statistics : Number of formulae       :   32 (  41 expanded)
%              Number of leaves         :   17 (  23 expanded)
%              Depth                    :    4
%              Number of atoms          :   33 (  61 expanded)
%              Number of equality atoms :   13 (  25 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_mcart_1 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

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

tff(f_49,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r2_hidden(A,k2_zfmisc_1(B,k2_tarski(C,D)))
       => ( r2_hidden(k1_mcart_1(A),B)
          & ( k2_mcart_1(A) = C
            | k2_mcart_1(A) = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_mcart_1)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(c_26,plain,
    ( k2_mcart_1('#skF_3') != '#skF_6'
    | ~ r2_hidden(k1_mcart_1('#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_31,plain,(
    ~ r2_hidden(k1_mcart_1('#skF_3'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_24,plain,(
    r2_hidden('#skF_3',k2_zfmisc_1('#skF_4',k2_tarski('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_58,plain,(
    ! [A_20,B_21,C_22] :
      ( r2_hidden(k1_mcart_1(A_20),B_21)
      | ~ r2_hidden(A_20,k2_zfmisc_1(B_21,C_22)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_60,plain,(
    r2_hidden(k1_mcart_1('#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_58])).

tff(c_64,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_31,c_60])).

tff(c_66,plain,(
    r2_hidden(k1_mcart_1('#skF_3'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_28,plain,
    ( k2_mcart_1('#skF_3') != '#skF_5'
    | ~ r2_hidden(k1_mcart_1('#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_68,plain,(
    k2_mcart_1('#skF_3') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_28])).

tff(c_65,plain,(
    k2_mcart_1('#skF_3') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_80,plain,(
    ! [A_26,C_27,B_28] :
      ( r2_hidden(k2_mcart_1(A_26),C_27)
      | ~ r2_hidden(A_26,k2_zfmisc_1(B_28,C_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_83,plain,(
    r2_hidden(k2_mcart_1('#skF_3'),k2_tarski('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_24,c_80])).

tff(c_2,plain,(
    ! [D_6,B_2,A_1] :
      ( D_6 = B_2
      | D_6 = A_1
      | ~ r2_hidden(D_6,k2_tarski(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_86,plain,
    ( k2_mcart_1('#skF_3') = '#skF_6'
    | k2_mcart_1('#skF_3') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_83,c_2])).

tff(c_90,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_65,c_86])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:31:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.75/1.17  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.75/1.17  
% 1.75/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.75/1.18  %$ r2_hidden > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_mcart_1 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4
% 1.75/1.18  
% 1.75/1.18  %Foreground sorts:
% 1.75/1.18  
% 1.75/1.18  
% 1.75/1.18  %Background operators:
% 1.75/1.18  
% 1.75/1.18  
% 1.75/1.18  %Foreground operators:
% 1.75/1.18  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.75/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.75/1.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.75/1.18  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.75/1.18  tff('#skF_5', type, '#skF_5': $i).
% 1.75/1.18  tff('#skF_6', type, '#skF_6': $i).
% 1.75/1.18  tff('#skF_3', type, '#skF_3': $i).
% 1.75/1.18  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.75/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.75/1.18  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 1.75/1.18  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.75/1.18  tff('#skF_4', type, '#skF_4': $i).
% 1.75/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.75/1.18  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 1.75/1.18  
% 1.81/1.19  tff(f_49, negated_conjecture, ~(![A, B, C, D]: (r2_hidden(A, k2_zfmisc_1(B, k2_tarski(C, D))) => (r2_hidden(k1_mcart_1(A), B) & ((k2_mcart_1(A) = C) | (k2_mcart_1(A) = D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_mcart_1)).
% 1.81/1.19  tff(f_40, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 1.81/1.19  tff(f_34, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 1.81/1.19  tff(c_26, plain, (k2_mcart_1('#skF_3')!='#skF_6' | ~r2_hidden(k1_mcart_1('#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.81/1.19  tff(c_31, plain, (~r2_hidden(k1_mcart_1('#skF_3'), '#skF_4')), inference(splitLeft, [status(thm)], [c_26])).
% 1.81/1.19  tff(c_24, plain, (r2_hidden('#skF_3', k2_zfmisc_1('#skF_4', k2_tarski('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.81/1.19  tff(c_58, plain, (![A_20, B_21, C_22]: (r2_hidden(k1_mcart_1(A_20), B_21) | ~r2_hidden(A_20, k2_zfmisc_1(B_21, C_22)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.81/1.19  tff(c_60, plain, (r2_hidden(k1_mcart_1('#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_24, c_58])).
% 1.81/1.19  tff(c_64, plain, $false, inference(negUnitSimplification, [status(thm)], [c_31, c_60])).
% 1.81/1.19  tff(c_66, plain, (r2_hidden(k1_mcart_1('#skF_3'), '#skF_4')), inference(splitRight, [status(thm)], [c_26])).
% 1.81/1.19  tff(c_28, plain, (k2_mcart_1('#skF_3')!='#skF_5' | ~r2_hidden(k1_mcart_1('#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.81/1.19  tff(c_68, plain, (k2_mcart_1('#skF_3')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_28])).
% 1.81/1.19  tff(c_65, plain, (k2_mcart_1('#skF_3')!='#skF_6'), inference(splitRight, [status(thm)], [c_26])).
% 1.81/1.19  tff(c_80, plain, (![A_26, C_27, B_28]: (r2_hidden(k2_mcart_1(A_26), C_27) | ~r2_hidden(A_26, k2_zfmisc_1(B_28, C_27)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.81/1.19  tff(c_83, plain, (r2_hidden(k2_mcart_1('#skF_3'), k2_tarski('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_24, c_80])).
% 1.81/1.19  tff(c_2, plain, (![D_6, B_2, A_1]: (D_6=B_2 | D_6=A_1 | ~r2_hidden(D_6, k2_tarski(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.81/1.19  tff(c_86, plain, (k2_mcart_1('#skF_3')='#skF_6' | k2_mcart_1('#skF_3')='#skF_5'), inference(resolution, [status(thm)], [c_83, c_2])).
% 1.81/1.19  tff(c_90, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_65, c_86])).
% 1.81/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.81/1.19  
% 1.81/1.19  Inference rules
% 1.81/1.19  ----------------------
% 1.81/1.19  #Ref     : 0
% 1.81/1.19  #Sup     : 11
% 1.81/1.19  #Fact    : 0
% 1.81/1.19  #Define  : 0
% 1.81/1.19  #Split   : 2
% 1.81/1.19  #Chain   : 0
% 1.81/1.19  #Close   : 0
% 1.81/1.19  
% 1.81/1.19  Ordering : KBO
% 1.81/1.19  
% 1.81/1.19  Simplification rules
% 1.81/1.19  ----------------------
% 1.81/1.19  #Subsume      : 1
% 1.81/1.19  #Demod        : 3
% 1.81/1.19  #Tautology    : 7
% 1.81/1.19  #SimpNegUnit  : 2
% 1.81/1.19  #BackRed      : 1
% 1.81/1.19  
% 1.81/1.19  #Partial instantiations: 0
% 1.81/1.19  #Strategies tried      : 1
% 1.81/1.19  
% 1.81/1.19  Timing (in seconds)
% 1.81/1.19  ----------------------
% 1.81/1.19  Preprocessing        : 0.29
% 1.81/1.19  Parsing              : 0.15
% 1.81/1.19  CNF conversion       : 0.02
% 1.81/1.19  Main loop            : 0.11
% 1.81/1.19  Inferencing          : 0.03
% 1.81/1.19  Reduction            : 0.03
% 1.81/1.19  Demodulation         : 0.02
% 1.81/1.19  BG Simplification    : 0.01
% 1.81/1.19  Subsumption          : 0.02
% 1.81/1.19  Abstraction          : 0.01
% 1.81/1.19  MUC search           : 0.00
% 1.81/1.19  Cooper               : 0.00
% 1.81/1.19  Total                : 0.42
% 1.81/1.20  Index Insertion      : 0.00
% 1.81/1.20  Index Deletion       : 0.00
% 1.81/1.20  Index Matching       : 0.00
% 1.81/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
