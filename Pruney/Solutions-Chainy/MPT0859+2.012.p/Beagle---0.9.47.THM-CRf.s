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
% DateTime   : Thu Dec  3 10:08:59 EST 2020

% Result     : Theorem 1.98s
% Output     : CNFRefutation 2.11s
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
        ( r2_hidden(A,k2_zfmisc_1(k2_tarski(B,C),D))
       => ( ( k1_mcart_1(A) = B
            | k1_mcart_1(A) = C )
          & r2_hidden(k2_mcart_1(A),D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_mcart_1)).

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
    ( k1_mcart_1('#skF_3') != '#skF_5'
    | ~ r2_hidden(k2_mcart_1('#skF_3'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_31,plain,(
    ~ r2_hidden(k2_mcart_1('#skF_3'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_24,plain,(
    r2_hidden('#skF_3',k2_zfmisc_1(k2_tarski('#skF_4','#skF_5'),'#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_43,plain,(
    ! [A_17,C_18,B_19] :
      ( r2_hidden(k2_mcart_1(A_17),C_18)
      | ~ r2_hidden(A_17,k2_zfmisc_1(B_19,C_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_45,plain,(
    r2_hidden(k2_mcart_1('#skF_3'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_24,c_43])).

tff(c_49,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_31,c_45])).

tff(c_51,plain,(
    r2_hidden(k2_mcart_1('#skF_3'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_28,plain,
    ( k1_mcart_1('#skF_3') != '#skF_4'
    | ~ r2_hidden(k2_mcart_1('#skF_3'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_53,plain,(
    k1_mcart_1('#skF_3') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_28])).

tff(c_50,plain,(
    k1_mcart_1('#skF_3') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_59,plain,(
    ! [A_23,B_24,C_25] :
      ( r2_hidden(k1_mcart_1(A_23),B_24)
      | ~ r2_hidden(A_23,k2_zfmisc_1(B_24,C_25)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_62,plain,(
    r2_hidden(k1_mcart_1('#skF_3'),k2_tarski('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_24,c_59])).

tff(c_63,plain,(
    ! [D_26,B_27,A_28] :
      ( D_26 = B_27
      | D_26 = A_28
      | ~ r2_hidden(D_26,k2_tarski(A_28,B_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_66,plain,
    ( k1_mcart_1('#skF_3') = '#skF_5'
    | k1_mcart_1('#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_62,c_63])).

tff(c_76,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_53,c_50,c_66])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:21:16 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.98/1.45  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.98/1.46  
% 1.98/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.98/1.47  %$ r2_hidden > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_mcart_1 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4
% 1.98/1.47  
% 1.98/1.47  %Foreground sorts:
% 1.98/1.47  
% 1.98/1.47  
% 1.98/1.47  %Background operators:
% 1.98/1.47  
% 1.98/1.47  
% 1.98/1.47  %Foreground operators:
% 1.98/1.47  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.98/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.98/1.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.98/1.47  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.98/1.47  tff('#skF_5', type, '#skF_5': $i).
% 1.98/1.47  tff('#skF_6', type, '#skF_6': $i).
% 1.98/1.47  tff('#skF_3', type, '#skF_3': $i).
% 1.98/1.47  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.98/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.98/1.47  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 1.98/1.47  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.98/1.47  tff('#skF_4', type, '#skF_4': $i).
% 1.98/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.98/1.47  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.11/1.47  
% 2.11/1.48  tff(f_49, negated_conjecture, ~(![A, B, C, D]: (r2_hidden(A, k2_zfmisc_1(k2_tarski(B, C), D)) => (((k1_mcart_1(A) = B) | (k1_mcart_1(A) = C)) & r2_hidden(k2_mcart_1(A), D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_mcart_1)).
% 2.11/1.48  tff(f_40, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 2.11/1.48  tff(f_34, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 2.11/1.48  tff(c_26, plain, (k1_mcart_1('#skF_3')!='#skF_5' | ~r2_hidden(k2_mcart_1('#skF_3'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.11/1.48  tff(c_31, plain, (~r2_hidden(k2_mcart_1('#skF_3'), '#skF_6')), inference(splitLeft, [status(thm)], [c_26])).
% 2.11/1.48  tff(c_24, plain, (r2_hidden('#skF_3', k2_zfmisc_1(k2_tarski('#skF_4', '#skF_5'), '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.11/1.48  tff(c_43, plain, (![A_17, C_18, B_19]: (r2_hidden(k2_mcart_1(A_17), C_18) | ~r2_hidden(A_17, k2_zfmisc_1(B_19, C_18)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.11/1.48  tff(c_45, plain, (r2_hidden(k2_mcart_1('#skF_3'), '#skF_6')), inference(resolution, [status(thm)], [c_24, c_43])).
% 2.11/1.48  tff(c_49, plain, $false, inference(negUnitSimplification, [status(thm)], [c_31, c_45])).
% 2.11/1.48  tff(c_51, plain, (r2_hidden(k2_mcart_1('#skF_3'), '#skF_6')), inference(splitRight, [status(thm)], [c_26])).
% 2.11/1.48  tff(c_28, plain, (k1_mcart_1('#skF_3')!='#skF_4' | ~r2_hidden(k2_mcart_1('#skF_3'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.11/1.48  tff(c_53, plain, (k1_mcart_1('#skF_3')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_51, c_28])).
% 2.11/1.48  tff(c_50, plain, (k1_mcart_1('#skF_3')!='#skF_5'), inference(splitRight, [status(thm)], [c_26])).
% 2.11/1.48  tff(c_59, plain, (![A_23, B_24, C_25]: (r2_hidden(k1_mcart_1(A_23), B_24) | ~r2_hidden(A_23, k2_zfmisc_1(B_24, C_25)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.11/1.48  tff(c_62, plain, (r2_hidden(k1_mcart_1('#skF_3'), k2_tarski('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_24, c_59])).
% 2.11/1.48  tff(c_63, plain, (![D_26, B_27, A_28]: (D_26=B_27 | D_26=A_28 | ~r2_hidden(D_26, k2_tarski(A_28, B_27)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.11/1.48  tff(c_66, plain, (k1_mcart_1('#skF_3')='#skF_5' | k1_mcart_1('#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_62, c_63])).
% 2.11/1.48  tff(c_76, plain, $false, inference(negUnitSimplification, [status(thm)], [c_53, c_50, c_66])).
% 2.11/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.11/1.48  
% 2.11/1.48  Inference rules
% 2.11/1.48  ----------------------
% 2.11/1.48  #Ref     : 0
% 2.11/1.48  #Sup     : 8
% 2.11/1.48  #Fact    : 0
% 2.11/1.48  #Define  : 0
% 2.11/1.48  #Split   : 1
% 2.11/1.48  #Chain   : 0
% 2.11/1.48  #Close   : 0
% 2.11/1.48  
% 2.11/1.48  Ordering : KBO
% 2.11/1.48  
% 2.11/1.48  Simplification rules
% 2.11/1.48  ----------------------
% 2.11/1.48  #Subsume      : 1
% 2.11/1.48  #Demod        : 2
% 2.11/1.48  #Tautology    : 3
% 2.11/1.48  #SimpNegUnit  : 2
% 2.11/1.48  #BackRed      : 0
% 2.11/1.48  
% 2.11/1.48  #Partial instantiations: 0
% 2.11/1.48  #Strategies tried      : 1
% 2.11/1.48  
% 2.11/1.48  Timing (in seconds)
% 2.11/1.48  ----------------------
% 2.11/1.49  Preprocessing        : 0.44
% 2.11/1.49  Parsing              : 0.23
% 2.11/1.49  CNF conversion       : 0.03
% 2.11/1.49  Main loop            : 0.13
% 2.11/1.49  Inferencing          : 0.04
% 2.11/1.49  Reduction            : 0.04
% 2.11/1.49  Demodulation         : 0.02
% 2.11/1.49  BG Simplification    : 0.01
% 2.11/1.49  Subsumption          : 0.03
% 2.11/1.49  Abstraction          : 0.01
% 2.11/1.49  MUC search           : 0.00
% 2.11/1.49  Cooper               : 0.00
% 2.11/1.49  Total                : 0.62
% 2.11/1.49  Index Insertion      : 0.00
% 2.11/1.49  Index Deletion       : 0.00
% 2.11/1.49  Index Matching       : 0.00
% 2.11/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
