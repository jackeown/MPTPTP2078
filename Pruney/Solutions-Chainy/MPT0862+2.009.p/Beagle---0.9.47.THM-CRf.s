%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:05 EST 2020

% Result     : Theorem 1.82s
% Output     : CNFRefutation 1.91s
% Verified   : 
% Statistics : Number of formulae       :   37 (  46 expanded)
%              Number of leaves         :   22 (  28 expanded)
%              Depth                    :    4
%              Number of atoms          :   33 (  61 expanded)
%              Number of equality atoms :   21 (  41 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

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
    ~ ! [A,B,C,D] :
        ( r2_hidden(A,k2_zfmisc_1(k1_tarski(B),k2_tarski(C,D)))
       => ( k1_mcart_1(A) = B
          & ( k2_mcart_1(A) = C
            | k2_mcart_1(A) = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_mcart_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(k1_tarski(B),C))
     => ( k1_mcart_1(A) = B
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_mcart_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(c_38,plain,
    ( k2_mcart_1('#skF_3') != '#skF_5'
    | k1_mcart_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_58,plain,(
    k1_mcart_1('#skF_3') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_34,plain,(
    r2_hidden('#skF_3',k2_zfmisc_1(k1_tarski('#skF_4'),k2_tarski('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_88,plain,(
    ! [A_38,B_39,C_40] :
      ( k1_mcart_1(A_38) = B_39
      | ~ r2_hidden(A_38,k2_zfmisc_1(k1_tarski(B_39),C_40)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_91,plain,(
    k1_mcart_1('#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_34,c_88])).

tff(c_95,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_91])).

tff(c_96,plain,(
    k2_mcart_1('#skF_3') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_97,plain,(
    k1_mcart_1('#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_36,plain,
    ( k2_mcart_1('#skF_3') != '#skF_6'
    | k1_mcart_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_103,plain,(
    k2_mcart_1('#skF_3') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_36])).

tff(c_148,plain,(
    ! [A_54,C_55,B_56] :
      ( r2_hidden(k2_mcart_1(A_54),C_55)
      | ~ r2_hidden(A_54,k2_zfmisc_1(k1_tarski(B_56),C_55)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_152,plain,(
    r2_hidden(k2_mcart_1('#skF_3'),k2_tarski('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_34,c_148])).

tff(c_2,plain,(
    ! [D_6,B_2,A_1] :
      ( D_6 = B_2
      | D_6 = A_1
      | ~ r2_hidden(D_6,k2_tarski(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_155,plain,
    ( k2_mcart_1('#skF_3') = '#skF_6'
    | k2_mcart_1('#skF_3') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_152,c_2])).

tff(c_159,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_103,c_155])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:51:39 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.82/1.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.82/1.22  
% 1.82/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.82/1.22  %$ r2_hidden > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4
% 1.82/1.22  
% 1.82/1.22  %Foreground sorts:
% 1.82/1.22  
% 1.82/1.22  
% 1.82/1.22  %Background operators:
% 1.82/1.22  
% 1.82/1.22  
% 1.82/1.22  %Foreground operators:
% 1.82/1.22  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.82/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.82/1.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.82/1.22  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.82/1.22  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.82/1.22  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.82/1.22  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.82/1.22  tff('#skF_5', type, '#skF_5': $i).
% 1.82/1.22  tff('#skF_6', type, '#skF_6': $i).
% 1.82/1.22  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.82/1.22  tff('#skF_3', type, '#skF_3': $i).
% 1.82/1.22  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.82/1.22  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.82/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.82/1.22  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 1.82/1.22  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.82/1.22  tff('#skF_4', type, '#skF_4': $i).
% 1.82/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.82/1.22  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 1.82/1.22  
% 1.91/1.23  tff(f_59, negated_conjecture, ~(![A, B, C, D]: (r2_hidden(A, k2_zfmisc_1(k1_tarski(B), k2_tarski(C, D))) => ((k1_mcart_1(A) = B) & ((k2_mcart_1(A) = C) | (k2_mcart_1(A) = D))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_mcart_1)).
% 1.91/1.23  tff(f_50, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(k1_tarski(B), C)) => ((k1_mcart_1(A) = B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_mcart_1)).
% 1.91/1.23  tff(f_34, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 1.91/1.23  tff(c_38, plain, (k2_mcart_1('#skF_3')!='#skF_5' | k1_mcart_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.91/1.23  tff(c_58, plain, (k1_mcart_1('#skF_3')!='#skF_4'), inference(splitLeft, [status(thm)], [c_38])).
% 1.91/1.23  tff(c_34, plain, (r2_hidden('#skF_3', k2_zfmisc_1(k1_tarski('#skF_4'), k2_tarski('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.91/1.23  tff(c_88, plain, (![A_38, B_39, C_40]: (k1_mcart_1(A_38)=B_39 | ~r2_hidden(A_38, k2_zfmisc_1(k1_tarski(B_39), C_40)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.91/1.23  tff(c_91, plain, (k1_mcart_1('#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_34, c_88])).
% 1.91/1.23  tff(c_95, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_91])).
% 1.91/1.23  tff(c_96, plain, (k2_mcart_1('#skF_3')!='#skF_5'), inference(splitRight, [status(thm)], [c_38])).
% 1.91/1.23  tff(c_97, plain, (k1_mcart_1('#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_38])).
% 1.91/1.23  tff(c_36, plain, (k2_mcart_1('#skF_3')!='#skF_6' | k1_mcart_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.91/1.23  tff(c_103, plain, (k2_mcart_1('#skF_3')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_97, c_36])).
% 1.91/1.23  tff(c_148, plain, (![A_54, C_55, B_56]: (r2_hidden(k2_mcart_1(A_54), C_55) | ~r2_hidden(A_54, k2_zfmisc_1(k1_tarski(B_56), C_55)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.91/1.23  tff(c_152, plain, (r2_hidden(k2_mcart_1('#skF_3'), k2_tarski('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_34, c_148])).
% 1.91/1.23  tff(c_2, plain, (![D_6, B_2, A_1]: (D_6=B_2 | D_6=A_1 | ~r2_hidden(D_6, k2_tarski(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.91/1.23  tff(c_155, plain, (k2_mcart_1('#skF_3')='#skF_6' | k2_mcart_1('#skF_3')='#skF_5'), inference(resolution, [status(thm)], [c_152, c_2])).
% 1.91/1.23  tff(c_159, plain, $false, inference(negUnitSimplification, [status(thm)], [c_96, c_103, c_155])).
% 1.91/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.91/1.23  
% 1.91/1.23  Inference rules
% 1.91/1.23  ----------------------
% 1.91/1.23  #Ref     : 0
% 1.91/1.23  #Sup     : 24
% 1.91/1.23  #Fact    : 0
% 1.91/1.23  #Define  : 0
% 1.91/1.23  #Split   : 1
% 1.91/1.23  #Chain   : 0
% 1.91/1.23  #Close   : 0
% 1.91/1.23  
% 1.91/1.23  Ordering : KBO
% 1.91/1.23  
% 1.91/1.23  Simplification rules
% 1.91/1.23  ----------------------
% 1.91/1.23  #Subsume      : 1
% 1.91/1.23  #Demod        : 3
% 1.91/1.23  #Tautology    : 18
% 1.91/1.23  #SimpNegUnit  : 2
% 1.91/1.23  #BackRed      : 0
% 1.91/1.23  
% 1.91/1.23  #Partial instantiations: 0
% 1.91/1.23  #Strategies tried      : 1
% 1.91/1.23  
% 1.91/1.23  Timing (in seconds)
% 1.91/1.23  ----------------------
% 1.91/1.23  Preprocessing        : 0.29
% 1.91/1.23  Parsing              : 0.15
% 1.91/1.23  CNF conversion       : 0.02
% 1.91/1.23  Main loop            : 0.12
% 1.91/1.23  Inferencing          : 0.04
% 1.91/1.23  Reduction            : 0.04
% 1.91/1.23  Demodulation         : 0.03
% 1.91/1.23  BG Simplification    : 0.01
% 1.91/1.23  Subsumption          : 0.02
% 1.91/1.23  Abstraction          : 0.01
% 1.91/1.23  MUC search           : 0.00
% 1.91/1.23  Cooper               : 0.00
% 1.91/1.23  Total                : 0.44
% 1.91/1.23  Index Insertion      : 0.00
% 1.91/1.23  Index Deletion       : 0.00
% 1.91/1.23  Index Matching       : 0.00
% 1.91/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
