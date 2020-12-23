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
% DateTime   : Thu Dec  3 10:08:53 EST 2020

% Result     : Theorem 1.68s
% Output     : CNFRefutation 1.85s
% Verified   : 
% Statistics : Number of formulae       :   33 (  42 expanded)
%              Number of leaves         :   19 (  24 expanded)
%              Depth                    :    4
%              Number of atoms          :   32 (  53 expanded)
%              Number of equality atoms :   13 (  20 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k1_enumset1 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4

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

tff(f_51,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r2_hidden(A,k2_zfmisc_1(k1_tarski(B),C))
       => ( k1_mcart_1(A) = B
          & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_mcart_1)).

tff(f_44,axiom,(
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

tff(c_28,plain,
    ( ~ r2_hidden(k2_mcart_1('#skF_3'),'#skF_5')
    | k1_mcart_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_50,plain,(
    k1_mcart_1('#skF_3') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_30,plain,(
    r2_hidden('#skF_3',k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_60,plain,(
    ! [A_21,B_22,C_23] :
      ( r2_hidden(k1_mcart_1(A_21),B_22)
      | ~ r2_hidden(A_21,k2_zfmisc_1(B_22,C_23)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_63,plain,(
    r2_hidden(k1_mcart_1('#skF_3'),k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_30,c_60])).

tff(c_20,plain,(
    ! [A_7] : k2_tarski(A_7,A_7) = k1_tarski(A_7) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_64,plain,(
    ! [D_24,B_25,A_26] :
      ( D_24 = B_25
      | D_24 = A_26
      | ~ r2_hidden(D_24,k2_tarski(A_26,B_25)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_78,plain,(
    ! [D_27,A_28] :
      ( D_27 = A_28
      | D_27 = A_28
      | ~ r2_hidden(D_27,k1_tarski(A_28)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_64])).

tff(c_81,plain,(
    k1_mcart_1('#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_63,c_78])).

tff(c_88,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_50,c_81])).

tff(c_89,plain,(
    ~ r2_hidden(k2_mcart_1('#skF_3'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_129,plain,(
    ! [A_39,C_40,B_41] :
      ( r2_hidden(k2_mcart_1(A_39),C_40)
      | ~ r2_hidden(A_39,k2_zfmisc_1(B_41,C_40)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_131,plain,(
    r2_hidden(k2_mcart_1('#skF_3'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_30,c_129])).

tff(c_135,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_89,c_131])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:51:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.68/1.15  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.68/1.15  
% 1.68/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.68/1.15  %$ r2_hidden > k1_enumset1 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4
% 1.68/1.15  
% 1.68/1.15  %Foreground sorts:
% 1.68/1.15  
% 1.68/1.15  
% 1.68/1.15  %Background operators:
% 1.68/1.15  
% 1.68/1.15  
% 1.68/1.15  %Foreground operators:
% 1.68/1.15  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.68/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.68/1.15  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.68/1.15  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.68/1.15  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.68/1.15  tff('#skF_5', type, '#skF_5': $i).
% 1.68/1.15  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.68/1.15  tff('#skF_3', type, '#skF_3': $i).
% 1.68/1.15  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.68/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.68/1.15  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 1.68/1.15  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.68/1.15  tff('#skF_4', type, '#skF_4': $i).
% 1.68/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.68/1.15  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 1.68/1.15  
% 1.85/1.16  tff(f_51, negated_conjecture, ~(![A, B, C]: (r2_hidden(A, k2_zfmisc_1(k1_tarski(B), C)) => ((k1_mcart_1(A) = B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_mcart_1)).
% 1.85/1.16  tff(f_44, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 1.85/1.16  tff(f_36, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 1.85/1.16  tff(f_34, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 1.85/1.16  tff(c_28, plain, (~r2_hidden(k2_mcart_1('#skF_3'), '#skF_5') | k1_mcart_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.85/1.16  tff(c_50, plain, (k1_mcart_1('#skF_3')!='#skF_4'), inference(splitLeft, [status(thm)], [c_28])).
% 1.85/1.16  tff(c_30, plain, (r2_hidden('#skF_3', k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.85/1.16  tff(c_60, plain, (![A_21, B_22, C_23]: (r2_hidden(k1_mcart_1(A_21), B_22) | ~r2_hidden(A_21, k2_zfmisc_1(B_22, C_23)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.85/1.16  tff(c_63, plain, (r2_hidden(k1_mcart_1('#skF_3'), k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_30, c_60])).
% 1.85/1.16  tff(c_20, plain, (![A_7]: (k2_tarski(A_7, A_7)=k1_tarski(A_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.85/1.16  tff(c_64, plain, (![D_24, B_25, A_26]: (D_24=B_25 | D_24=A_26 | ~r2_hidden(D_24, k2_tarski(A_26, B_25)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.85/1.16  tff(c_78, plain, (![D_27, A_28]: (D_27=A_28 | D_27=A_28 | ~r2_hidden(D_27, k1_tarski(A_28)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_64])).
% 1.85/1.16  tff(c_81, plain, (k1_mcart_1('#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_63, c_78])).
% 1.85/1.16  tff(c_88, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_50, c_81])).
% 1.85/1.16  tff(c_89, plain, (~r2_hidden(k2_mcart_1('#skF_3'), '#skF_5')), inference(splitRight, [status(thm)], [c_28])).
% 1.85/1.16  tff(c_129, plain, (![A_39, C_40, B_41]: (r2_hidden(k2_mcart_1(A_39), C_40) | ~r2_hidden(A_39, k2_zfmisc_1(B_41, C_40)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.85/1.16  tff(c_131, plain, (r2_hidden(k2_mcart_1('#skF_3'), '#skF_5')), inference(resolution, [status(thm)], [c_30, c_129])).
% 1.85/1.16  tff(c_135, plain, $false, inference(negUnitSimplification, [status(thm)], [c_89, c_131])).
% 1.85/1.16  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.85/1.16  
% 1.85/1.16  Inference rules
% 1.85/1.16  ----------------------
% 1.85/1.16  #Ref     : 0
% 1.85/1.16  #Sup     : 22
% 1.85/1.16  #Fact    : 0
% 1.85/1.16  #Define  : 0
% 1.85/1.16  #Split   : 1
% 1.85/1.16  #Chain   : 0
% 1.85/1.16  #Close   : 0
% 1.85/1.16  
% 1.85/1.16  Ordering : KBO
% 1.85/1.16  
% 1.85/1.16  Simplification rules
% 1.85/1.16  ----------------------
% 1.85/1.16  #Subsume      : 0
% 1.85/1.16  #Demod        : 3
% 1.85/1.16  #Tautology    : 15
% 1.85/1.16  #SimpNegUnit  : 2
% 1.85/1.16  #BackRed      : 0
% 1.85/1.16  
% 1.85/1.16  #Partial instantiations: 0
% 1.85/1.16  #Strategies tried      : 1
% 1.85/1.16  
% 1.85/1.16  Timing (in seconds)
% 1.85/1.16  ----------------------
% 1.85/1.16  Preprocessing        : 0.29
% 1.85/1.16  Parsing              : 0.15
% 1.85/1.16  CNF conversion       : 0.02
% 1.85/1.16  Main loop            : 0.12
% 1.85/1.16  Inferencing          : 0.04
% 1.85/1.16  Reduction            : 0.04
% 1.85/1.16  Demodulation         : 0.03
% 1.85/1.16  BG Simplification    : 0.01
% 1.85/1.16  Subsumption          : 0.02
% 1.85/1.16  Abstraction          : 0.01
% 1.85/1.16  MUC search           : 0.00
% 1.85/1.16  Cooper               : 0.00
% 1.85/1.16  Total                : 0.43
% 1.85/1.16  Index Insertion      : 0.00
% 1.85/1.16  Index Deletion       : 0.00
% 1.85/1.16  Index Matching       : 0.00
% 1.85/1.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
