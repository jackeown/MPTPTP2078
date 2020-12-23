%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:56 EST 2020

% Result     : Theorem 1.62s
% Output     : CNFRefutation 1.62s
% Verified   : 
% Statistics : Number of formulae       :   29 (  37 expanded)
%              Number of leaves         :   16 (  21 expanded)
%              Depth                    :    4
%              Number of atoms          :   26 (  46 expanded)
%              Number of equality atoms :   11 (  22 expanded)
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
        ( r2_hidden(A,k2_zfmisc_1(k1_tarski(B),k1_tarski(C)))
       => ( k1_mcart_1(A) = B
          & k2_mcart_1(A) = C ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_mcart_1)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(c_18,plain,
    ( k2_mcart_1('#skF_3') != '#skF_5'
    | k1_mcart_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_22,plain,(
    k1_mcart_1('#skF_3') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_18])).

tff(c_20,plain,(
    r2_hidden('#skF_3',k2_zfmisc_1(k1_tarski('#skF_4'),k1_tarski('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_43,plain,(
    ! [A_15,B_16,C_17] :
      ( r2_hidden(k1_mcart_1(A_15),B_16)
      | ~ r2_hidden(A_15,k2_zfmisc_1(B_16,C_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_46,plain,(
    r2_hidden(k1_mcart_1('#skF_3'),k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_20,c_43])).

tff(c_2,plain,(
    ! [C_5,A_1] :
      ( C_5 = A_1
      | ~ r2_hidden(C_5,k1_tarski(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_49,plain,(
    k1_mcart_1('#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_46,c_2])).

tff(c_53,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_49])).

tff(c_54,plain,(
    k2_mcart_1('#skF_3') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_66,plain,(
    ! [A_20,C_21,B_22] :
      ( r2_hidden(k2_mcart_1(A_20),C_21)
      | ~ r2_hidden(A_20,k2_zfmisc_1(B_22,C_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_69,plain,(
    r2_hidden(k2_mcart_1('#skF_3'),k1_tarski('#skF_5')) ),
    inference(resolution,[status(thm)],[c_20,c_66])).

tff(c_77,plain,(
    k2_mcart_1('#skF_3') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_69,c_2])).

tff(c_81,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_77])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:31:16 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.62/1.11  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.62/1.11  
% 1.62/1.11  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.62/1.12  %$ r2_hidden > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 1.62/1.12  
% 1.62/1.12  %Foreground sorts:
% 1.62/1.12  
% 1.62/1.12  
% 1.62/1.12  %Background operators:
% 1.62/1.12  
% 1.62/1.12  
% 1.62/1.12  %Foreground operators:
% 1.62/1.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.62/1.12  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.62/1.12  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.62/1.12  tff('#skF_5', type, '#skF_5': $i).
% 1.62/1.12  tff('#skF_3', type, '#skF_3': $i).
% 1.62/1.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.62/1.12  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 1.62/1.12  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.62/1.12  tff('#skF_4', type, '#skF_4': $i).
% 1.62/1.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.62/1.12  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.62/1.12  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 1.62/1.12  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.62/1.12  
% 1.62/1.13  tff(f_45, negated_conjecture, ~(![A, B, C]: (r2_hidden(A, k2_zfmisc_1(k1_tarski(B), k1_tarski(C))) => ((k1_mcart_1(A) = B) & (k2_mcart_1(A) = C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_mcart_1)).
% 1.62/1.13  tff(f_38, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 1.62/1.13  tff(f_32, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 1.62/1.13  tff(c_18, plain, (k2_mcart_1('#skF_3')!='#skF_5' | k1_mcart_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.62/1.13  tff(c_22, plain, (k1_mcart_1('#skF_3')!='#skF_4'), inference(splitLeft, [status(thm)], [c_18])).
% 1.62/1.13  tff(c_20, plain, (r2_hidden('#skF_3', k2_zfmisc_1(k1_tarski('#skF_4'), k1_tarski('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.62/1.13  tff(c_43, plain, (![A_15, B_16, C_17]: (r2_hidden(k1_mcart_1(A_15), B_16) | ~r2_hidden(A_15, k2_zfmisc_1(B_16, C_17)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.62/1.13  tff(c_46, plain, (r2_hidden(k1_mcart_1('#skF_3'), k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_20, c_43])).
% 1.62/1.13  tff(c_2, plain, (![C_5, A_1]: (C_5=A_1 | ~r2_hidden(C_5, k1_tarski(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.62/1.13  tff(c_49, plain, (k1_mcart_1('#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_46, c_2])).
% 1.62/1.13  tff(c_53, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_49])).
% 1.62/1.13  tff(c_54, plain, (k2_mcart_1('#skF_3')!='#skF_5'), inference(splitRight, [status(thm)], [c_18])).
% 1.62/1.13  tff(c_66, plain, (![A_20, C_21, B_22]: (r2_hidden(k2_mcart_1(A_20), C_21) | ~r2_hidden(A_20, k2_zfmisc_1(B_22, C_21)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.62/1.13  tff(c_69, plain, (r2_hidden(k2_mcart_1('#skF_3'), k1_tarski('#skF_5'))), inference(resolution, [status(thm)], [c_20, c_66])).
% 1.62/1.13  tff(c_77, plain, (k2_mcart_1('#skF_3')='#skF_5'), inference(resolution, [status(thm)], [c_69, c_2])).
% 1.62/1.13  tff(c_81, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_77])).
% 1.62/1.13  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.62/1.13  
% 1.62/1.13  Inference rules
% 1.62/1.13  ----------------------
% 1.62/1.13  #Ref     : 0
% 1.62/1.13  #Sup     : 13
% 1.62/1.13  #Fact    : 0
% 1.62/1.13  #Define  : 0
% 1.62/1.13  #Split   : 1
% 1.62/1.13  #Chain   : 0
% 1.62/1.13  #Close   : 0
% 1.62/1.13  
% 1.62/1.13  Ordering : KBO
% 1.62/1.13  
% 1.62/1.13  Simplification rules
% 1.62/1.13  ----------------------
% 1.62/1.13  #Subsume      : 0
% 1.62/1.13  #Demod        : 4
% 1.62/1.13  #Tautology    : 8
% 1.62/1.13  #SimpNegUnit  : 2
% 1.62/1.13  #BackRed      : 1
% 1.62/1.13  
% 1.62/1.13  #Partial instantiations: 0
% 1.62/1.13  #Strategies tried      : 1
% 1.62/1.13  
% 1.62/1.13  Timing (in seconds)
% 1.62/1.13  ----------------------
% 1.62/1.13  Preprocessing        : 0.27
% 1.62/1.13  Parsing              : 0.15
% 1.62/1.13  CNF conversion       : 0.02
% 1.62/1.13  Main loop            : 0.10
% 1.62/1.13  Inferencing          : 0.03
% 1.62/1.13  Reduction            : 0.03
% 1.62/1.13  Demodulation         : 0.02
% 1.62/1.13  BG Simplification    : 0.01
% 1.62/1.13  Subsumption          : 0.02
% 1.62/1.13  Abstraction          : 0.00
% 1.62/1.13  MUC search           : 0.00
% 1.62/1.13  Cooper               : 0.00
% 1.62/1.13  Total                : 0.39
% 1.62/1.13  Index Insertion      : 0.00
% 1.62/1.13  Index Deletion       : 0.00
% 1.62/1.13  Index Matching       : 0.00
% 1.62/1.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
