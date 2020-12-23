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
% DateTime   : Thu Dec  3 10:08:54 EST 2020

% Result     : Theorem 1.56s
% Output     : CNFRefutation 1.72s
% Verified   : 
% Statistics : Number of formulae       :   28 (  34 expanded)
%              Number of leaves         :   16 (  20 expanded)
%              Depth                    :    4
%              Number of atoms          :   25 (  40 expanded)
%              Number of equality atoms :    7 (  11 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_45,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r2_hidden(A,k2_zfmisc_1(B,k1_tarski(C)))
       => ( r2_hidden(k1_mcart_1(A),B)
          & k2_mcart_1(A) = C ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_mcart_1)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(c_18,plain,
    ( k2_mcart_1('#skF_3') != '#skF_5'
    | ~ r2_hidden(k1_mcart_1('#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_28,plain,(
    ~ r2_hidden(k1_mcart_1('#skF_3'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_18])).

tff(c_20,plain,(
    r2_hidden('#skF_3',k2_zfmisc_1('#skF_4',k1_tarski('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_29,plain,(
    ! [A_12,B_13,C_14] :
      ( r2_hidden(k1_mcart_1(A_12),B_13)
      | ~ r2_hidden(A_12,k2_zfmisc_1(B_13,C_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_31,plain,(
    r2_hidden(k1_mcart_1('#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_29])).

tff(c_35,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_31])).

tff(c_36,plain,(
    k2_mcart_1('#skF_3') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_43,plain,(
    ! [A_18,C_19,B_20] :
      ( r2_hidden(k2_mcart_1(A_18),C_19)
      | ~ r2_hidden(A_18,k2_zfmisc_1(B_20,C_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_46,plain,(
    r2_hidden(k2_mcart_1('#skF_3'),k1_tarski('#skF_5')) ),
    inference(resolution,[status(thm)],[c_20,c_43])).

tff(c_2,plain,(
    ! [C_5,A_1] :
      ( C_5 = A_1
      | ~ r2_hidden(C_5,k1_tarski(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_49,plain,(
    k2_mcart_1('#skF_3') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_46,c_2])).

tff(c_53,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_49])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:40:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.56/1.17  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.56/1.18  
% 1.56/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.72/1.18  %$ r2_hidden > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 1.72/1.18  
% 1.72/1.18  %Foreground sorts:
% 1.72/1.18  
% 1.72/1.18  
% 1.72/1.18  %Background operators:
% 1.72/1.18  
% 1.72/1.18  
% 1.72/1.18  %Foreground operators:
% 1.72/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.72/1.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.72/1.18  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.72/1.18  tff('#skF_5', type, '#skF_5': $i).
% 1.72/1.18  tff('#skF_3', type, '#skF_3': $i).
% 1.72/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.72/1.18  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 1.72/1.18  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.72/1.18  tff('#skF_4', type, '#skF_4': $i).
% 1.72/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.72/1.18  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.72/1.18  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 1.72/1.18  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.72/1.18  
% 1.72/1.19  tff(f_45, negated_conjecture, ~(![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, k1_tarski(C))) => (r2_hidden(k1_mcart_1(A), B) & (k2_mcart_1(A) = C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_mcart_1)).
% 1.72/1.19  tff(f_38, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_mcart_1)).
% 1.72/1.19  tff(f_32, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 1.72/1.19  tff(c_18, plain, (k2_mcart_1('#skF_3')!='#skF_5' | ~r2_hidden(k1_mcart_1('#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.72/1.19  tff(c_28, plain, (~r2_hidden(k1_mcart_1('#skF_3'), '#skF_4')), inference(splitLeft, [status(thm)], [c_18])).
% 1.72/1.19  tff(c_20, plain, (r2_hidden('#skF_3', k2_zfmisc_1('#skF_4', k1_tarski('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.72/1.19  tff(c_29, plain, (![A_12, B_13, C_14]: (r2_hidden(k1_mcart_1(A_12), B_13) | ~r2_hidden(A_12, k2_zfmisc_1(B_13, C_14)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.72/1.19  tff(c_31, plain, (r2_hidden(k1_mcart_1('#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_20, c_29])).
% 1.72/1.19  tff(c_35, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_31])).
% 1.72/1.19  tff(c_36, plain, (k2_mcart_1('#skF_3')!='#skF_5'), inference(splitRight, [status(thm)], [c_18])).
% 1.72/1.19  tff(c_43, plain, (![A_18, C_19, B_20]: (r2_hidden(k2_mcart_1(A_18), C_19) | ~r2_hidden(A_18, k2_zfmisc_1(B_20, C_19)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.72/1.19  tff(c_46, plain, (r2_hidden(k2_mcart_1('#skF_3'), k1_tarski('#skF_5'))), inference(resolution, [status(thm)], [c_20, c_43])).
% 1.72/1.19  tff(c_2, plain, (![C_5, A_1]: (C_5=A_1 | ~r2_hidden(C_5, k1_tarski(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.72/1.19  tff(c_49, plain, (k2_mcart_1('#skF_3')='#skF_5'), inference(resolution, [status(thm)], [c_46, c_2])).
% 1.72/1.19  tff(c_53, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_49])).
% 1.72/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.72/1.19  
% 1.72/1.19  Inference rules
% 1.72/1.19  ----------------------
% 1.72/1.19  #Ref     : 0
% 1.72/1.19  #Sup     : 5
% 1.72/1.19  #Fact    : 0
% 1.72/1.19  #Define  : 0
% 1.72/1.19  #Split   : 1
% 1.72/1.19  #Chain   : 0
% 1.72/1.19  #Close   : 0
% 1.72/1.19  
% 1.72/1.19  Ordering : KBO
% 1.72/1.19  
% 1.72/1.19  Simplification rules
% 1.72/1.19  ----------------------
% 1.72/1.19  #Subsume      : 0
% 1.72/1.19  #Demod        : 1
% 1.72/1.19  #Tautology    : 2
% 1.72/1.19  #SimpNegUnit  : 2
% 1.72/1.19  #BackRed      : 0
% 1.72/1.19  
% 1.72/1.19  #Partial instantiations: 0
% 1.72/1.19  #Strategies tried      : 1
% 1.72/1.19  
% 1.72/1.19  Timing (in seconds)
% 1.72/1.19  ----------------------
% 1.72/1.19  Preprocessing        : 0.28
% 1.72/1.19  Parsing              : 0.15
% 1.72/1.19  CNF conversion       : 0.02
% 1.72/1.19  Main loop            : 0.08
% 1.72/1.19  Inferencing          : 0.03
% 1.72/1.19  Reduction            : 0.02
% 1.72/1.19  Demodulation         : 0.01
% 1.72/1.19  BG Simplification    : 0.01
% 1.72/1.20  Subsumption          : 0.02
% 1.72/1.20  Abstraction          : 0.00
% 1.72/1.20  MUC search           : 0.00
% 1.72/1.20  Cooper               : 0.00
% 1.72/1.20  Total                : 0.40
% 1.72/1.20  Index Insertion      : 0.00
% 1.72/1.20  Index Deletion       : 0.00
% 1.72/1.20  Index Matching       : 0.00
% 1.72/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
