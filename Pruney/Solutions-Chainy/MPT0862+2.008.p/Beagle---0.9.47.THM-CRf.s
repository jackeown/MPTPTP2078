%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:05 EST 2020

% Result     : Theorem 1.93s
% Output     : CNFRefutation 1.93s
% Verified   : 
% Statistics : Number of formulae       :   42 (  57 expanded)
%              Number of leaves         :   21 (  30 expanded)
%              Depth                    :    4
%              Number of atoms          :   44 (  89 expanded)
%              Number of equality atoms :   26 (  59 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

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

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff(f_55,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r2_hidden(A,k2_zfmisc_1(k1_tarski(B),k2_tarski(C,D)))
       => ( k1_mcart_1(A) = B
          & ( k2_mcart_1(A) = C
            | k2_mcart_1(A) = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_mcart_1)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_36,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(c_34,plain,
    ( k2_mcart_1('#skF_3') != '#skF_5'
    | k1_mcart_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_54,plain,(
    k1_mcart_1('#skF_3') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_30,plain,(
    r2_hidden('#skF_3',k2_zfmisc_1(k1_tarski('#skF_4'),k2_tarski('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_64,plain,(
    ! [A_24,B_25,C_26] :
      ( r2_hidden(k1_mcart_1(A_24),B_25)
      | ~ r2_hidden(A_24,k2_zfmisc_1(B_25,C_26)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_67,plain,(
    r2_hidden(k1_mcart_1('#skF_3'),k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_30,c_64])).

tff(c_20,plain,(
    ! [A_7] : k2_tarski(A_7,A_7) = k1_tarski(A_7) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_81,plain,(
    ! [D_33,B_34,A_35] :
      ( D_33 = B_34
      | D_33 = A_35
      | ~ r2_hidden(D_33,k2_tarski(A_35,B_34)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_107,plain,(
    ! [D_39,A_40] :
      ( D_39 = A_40
      | D_39 = A_40
      | ~ r2_hidden(D_39,k1_tarski(A_40)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_81])).

tff(c_110,plain,(
    k1_mcart_1('#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_67,c_107])).

tff(c_117,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_54,c_110])).

tff(c_118,plain,(
    k2_mcart_1('#skF_3') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_119,plain,(
    k1_mcart_1('#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_32,plain,
    ( k2_mcart_1('#skF_3') != '#skF_6'
    | k1_mcart_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_120,plain,(
    k1_mcart_1('#skF_3') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_126,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_120])).

tff(c_127,plain,(
    k2_mcart_1('#skF_3') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_177,plain,(
    ! [A_54,C_55,B_56] :
      ( r2_hidden(k2_mcart_1(A_54),C_55)
      | ~ r2_hidden(A_54,k2_zfmisc_1(B_56,C_55)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_180,plain,(
    r2_hidden(k2_mcart_1('#skF_3'),k2_tarski('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_30,c_177])).

tff(c_2,plain,(
    ! [D_6,B_2,A_1] :
      ( D_6 = B_2
      | D_6 = A_1
      | ~ r2_hidden(D_6,k2_tarski(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_183,plain,
    ( k2_mcart_1('#skF_3') = '#skF_6'
    | k2_mcart_1('#skF_3') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_180,c_2])).

tff(c_187,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_118,c_127,c_183])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:47:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.93/1.19  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.19  
% 1.93/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.19  %$ r2_hidden > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4
% 1.93/1.19  
% 1.93/1.19  %Foreground sorts:
% 1.93/1.19  
% 1.93/1.19  
% 1.93/1.19  %Background operators:
% 1.93/1.19  
% 1.93/1.19  
% 1.93/1.19  %Foreground operators:
% 1.93/1.19  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.93/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.93/1.19  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.93/1.19  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.93/1.19  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.93/1.19  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.93/1.19  tff('#skF_5', type, '#skF_5': $i).
% 1.93/1.19  tff('#skF_6', type, '#skF_6': $i).
% 1.93/1.19  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.93/1.19  tff('#skF_3', type, '#skF_3': $i).
% 1.93/1.19  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.93/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.93/1.19  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 1.93/1.19  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.93/1.19  tff('#skF_4', type, '#skF_4': $i).
% 1.93/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.93/1.19  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 1.93/1.19  
% 1.93/1.20  tff(f_55, negated_conjecture, ~(![A, B, C, D]: (r2_hidden(A, k2_zfmisc_1(k1_tarski(B), k2_tarski(C, D))) => ((k1_mcart_1(A) = B) & ((k2_mcart_1(A) = C) | (k2_mcart_1(A) = D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_mcart_1)).
% 1.93/1.20  tff(f_46, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 1.93/1.20  tff(f_36, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 1.93/1.20  tff(f_34, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 1.93/1.20  tff(c_34, plain, (k2_mcart_1('#skF_3')!='#skF_5' | k1_mcart_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.93/1.20  tff(c_54, plain, (k1_mcart_1('#skF_3')!='#skF_4'), inference(splitLeft, [status(thm)], [c_34])).
% 1.93/1.20  tff(c_30, plain, (r2_hidden('#skF_3', k2_zfmisc_1(k1_tarski('#skF_4'), k2_tarski('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.93/1.20  tff(c_64, plain, (![A_24, B_25, C_26]: (r2_hidden(k1_mcart_1(A_24), B_25) | ~r2_hidden(A_24, k2_zfmisc_1(B_25, C_26)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.93/1.20  tff(c_67, plain, (r2_hidden(k1_mcart_1('#skF_3'), k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_30, c_64])).
% 1.93/1.20  tff(c_20, plain, (![A_7]: (k2_tarski(A_7, A_7)=k1_tarski(A_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.93/1.20  tff(c_81, plain, (![D_33, B_34, A_35]: (D_33=B_34 | D_33=A_35 | ~r2_hidden(D_33, k2_tarski(A_35, B_34)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.93/1.20  tff(c_107, plain, (![D_39, A_40]: (D_39=A_40 | D_39=A_40 | ~r2_hidden(D_39, k1_tarski(A_40)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_81])).
% 1.93/1.20  tff(c_110, plain, (k1_mcart_1('#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_67, c_107])).
% 1.93/1.20  tff(c_117, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_54, c_110])).
% 1.93/1.20  tff(c_118, plain, (k2_mcart_1('#skF_3')!='#skF_5'), inference(splitRight, [status(thm)], [c_34])).
% 1.93/1.20  tff(c_119, plain, (k1_mcart_1('#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_34])).
% 1.93/1.20  tff(c_32, plain, (k2_mcart_1('#skF_3')!='#skF_6' | k1_mcart_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.93/1.20  tff(c_120, plain, (k1_mcart_1('#skF_3')!='#skF_4'), inference(splitLeft, [status(thm)], [c_32])).
% 1.93/1.20  tff(c_126, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_119, c_120])).
% 1.93/1.20  tff(c_127, plain, (k2_mcart_1('#skF_3')!='#skF_6'), inference(splitRight, [status(thm)], [c_32])).
% 1.93/1.20  tff(c_177, plain, (![A_54, C_55, B_56]: (r2_hidden(k2_mcart_1(A_54), C_55) | ~r2_hidden(A_54, k2_zfmisc_1(B_56, C_55)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.93/1.20  tff(c_180, plain, (r2_hidden(k2_mcart_1('#skF_3'), k2_tarski('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_30, c_177])).
% 1.93/1.20  tff(c_2, plain, (![D_6, B_2, A_1]: (D_6=B_2 | D_6=A_1 | ~r2_hidden(D_6, k2_tarski(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.93/1.20  tff(c_183, plain, (k2_mcart_1('#skF_3')='#skF_6' | k2_mcart_1('#skF_3')='#skF_5'), inference(resolution, [status(thm)], [c_180, c_2])).
% 1.93/1.20  tff(c_187, plain, $false, inference(negUnitSimplification, [status(thm)], [c_118, c_127, c_183])).
% 1.93/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.20  
% 1.93/1.20  Inference rules
% 1.93/1.20  ----------------------
% 1.93/1.20  #Ref     : 0
% 1.93/1.20  #Sup     : 33
% 1.93/1.20  #Fact    : 0
% 1.93/1.20  #Define  : 0
% 1.93/1.20  #Split   : 3
% 1.93/1.20  #Chain   : 0
% 1.93/1.20  #Close   : 0
% 1.93/1.20  
% 1.93/1.20  Ordering : KBO
% 1.93/1.20  
% 1.93/1.20  Simplification rules
% 1.93/1.20  ----------------------
% 1.93/1.20  #Subsume      : 1
% 1.93/1.20  #Demod        : 7
% 1.93/1.20  #Tautology    : 25
% 1.93/1.20  #SimpNegUnit  : 2
% 1.93/1.20  #BackRed      : 1
% 1.93/1.20  
% 1.93/1.20  #Partial instantiations: 0
% 1.93/1.20  #Strategies tried      : 1
% 1.93/1.20  
% 1.93/1.20  Timing (in seconds)
% 1.93/1.20  ----------------------
% 1.93/1.20  Preprocessing        : 0.29
% 1.93/1.20  Parsing              : 0.15
% 1.93/1.20  CNF conversion       : 0.02
% 1.93/1.20  Main loop            : 0.15
% 1.93/1.20  Inferencing          : 0.05
% 1.93/1.20  Reduction            : 0.05
% 1.93/1.20  Demodulation         : 0.04
% 1.93/1.20  BG Simplification    : 0.01
% 1.93/1.20  Subsumption          : 0.02
% 1.93/1.20  Abstraction          : 0.01
% 1.93/1.21  MUC search           : 0.00
% 1.93/1.21  Cooper               : 0.00
% 1.93/1.21  Total                : 0.46
% 1.93/1.21  Index Insertion      : 0.00
% 1.93/1.21  Index Deletion       : 0.00
% 1.93/1.21  Index Matching       : 0.00
% 1.93/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
