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
% DateTime   : Thu Dec  3 10:09:05 EST 2020

% Result     : Theorem 1.92s
% Output     : CNFRefutation 1.92s
% Verified   : 
% Statistics : Number of formulae       :   36 (  46 expanded)
%              Number of leaves         :   19 (  25 expanded)
%              Depth                    :    4
%              Number of atoms          :   38 (  69 expanded)
%              Number of equality atoms :   22 (  46 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

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

tff(f_57,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r2_hidden(A,k2_zfmisc_1(k1_tarski(B),k2_tarski(C,D)))
       => ( k1_mcart_1(A) = B
          & ( k2_mcart_1(A) = C
            | k2_mcart_1(A) = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_mcart_1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(k1_tarski(B),C))
     => ( k1_mcart_1(A) = B
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_mcart_1)).

tff(f_42,axiom,(
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

tff(c_32,plain,
    ( k2_mcart_1('#skF_3') != '#skF_6'
    | k1_mcart_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_54,plain,(
    k1_mcart_1('#skF_3') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_30,plain,(
    r2_hidden('#skF_3',k2_zfmisc_1(k1_tarski('#skF_4'),k2_tarski('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_55,plain,(
    ! [A_20,B_21,C_22] :
      ( k1_mcart_1(A_20) = B_21
      | ~ r2_hidden(A_20,k2_zfmisc_1(k1_tarski(B_21),C_22)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_58,plain,(
    k1_mcart_1('#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_30,c_55])).

tff(c_62,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_58])).

tff(c_64,plain,(
    k1_mcart_1('#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_34,plain,
    ( k2_mcart_1('#skF_3') != '#skF_5'
    | k1_mcart_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_65,plain,(
    k1_mcart_1('#skF_3') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_71,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_65])).

tff(c_72,plain,(
    k2_mcart_1('#skF_3') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_63,plain,(
    k2_mcart_1('#skF_3') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_110,plain,(
    ! [A_34,C_35,B_36] :
      ( r2_hidden(k2_mcart_1(A_34),C_35)
      | ~ r2_hidden(A_34,k2_zfmisc_1(B_36,C_35)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_113,plain,(
    r2_hidden(k2_mcart_1('#skF_3'),k2_tarski('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_30,c_110])).

tff(c_2,plain,(
    ! [D_6,B_2,A_1] :
      ( D_6 = B_2
      | D_6 = A_1
      | ~ r2_hidden(D_6,k2_tarski(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_116,plain,
    ( k2_mcart_1('#skF_3') = '#skF_6'
    | k2_mcart_1('#skF_3') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_113,c_2])).

tff(c_120,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_63,c_116])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:24:31 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.92/1.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.92/1.30  
% 1.92/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.92/1.31  %$ r2_hidden > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4
% 1.92/1.31  
% 1.92/1.31  %Foreground sorts:
% 1.92/1.31  
% 1.92/1.31  
% 1.92/1.31  %Background operators:
% 1.92/1.31  
% 1.92/1.31  
% 1.92/1.31  %Foreground operators:
% 1.92/1.31  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.92/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.92/1.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.92/1.31  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.92/1.31  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.92/1.31  tff('#skF_5', type, '#skF_5': $i).
% 1.92/1.31  tff('#skF_6', type, '#skF_6': $i).
% 1.92/1.31  tff('#skF_3', type, '#skF_3': $i).
% 1.92/1.31  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.92/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.92/1.31  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 1.92/1.31  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.92/1.31  tff('#skF_4', type, '#skF_4': $i).
% 1.92/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.92/1.31  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 1.92/1.31  
% 1.92/1.31  tff(f_57, negated_conjecture, ~(![A, B, C, D]: (r2_hidden(A, k2_zfmisc_1(k1_tarski(B), k2_tarski(C, D))) => ((k1_mcart_1(A) = B) & ((k2_mcart_1(A) = C) | (k2_mcart_1(A) = D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_mcart_1)).
% 1.92/1.31  tff(f_48, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(k1_tarski(B), C)) => ((k1_mcart_1(A) = B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_mcart_1)).
% 1.92/1.31  tff(f_42, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 1.92/1.31  tff(f_34, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 1.92/1.31  tff(c_32, plain, (k2_mcart_1('#skF_3')!='#skF_6' | k1_mcart_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.92/1.31  tff(c_54, plain, (k1_mcart_1('#skF_3')!='#skF_4'), inference(splitLeft, [status(thm)], [c_32])).
% 1.92/1.31  tff(c_30, plain, (r2_hidden('#skF_3', k2_zfmisc_1(k1_tarski('#skF_4'), k2_tarski('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.92/1.31  tff(c_55, plain, (![A_20, B_21, C_22]: (k1_mcart_1(A_20)=B_21 | ~r2_hidden(A_20, k2_zfmisc_1(k1_tarski(B_21), C_22)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.92/1.31  tff(c_58, plain, (k1_mcart_1('#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_30, c_55])).
% 1.92/1.31  tff(c_62, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_58])).
% 1.92/1.31  tff(c_64, plain, (k1_mcart_1('#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_32])).
% 1.92/1.31  tff(c_34, plain, (k2_mcart_1('#skF_3')!='#skF_5' | k1_mcart_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.92/1.31  tff(c_65, plain, (k1_mcart_1('#skF_3')!='#skF_4'), inference(splitLeft, [status(thm)], [c_34])).
% 1.92/1.31  tff(c_71, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_65])).
% 1.92/1.31  tff(c_72, plain, (k2_mcart_1('#skF_3')!='#skF_5'), inference(splitRight, [status(thm)], [c_34])).
% 1.92/1.31  tff(c_63, plain, (k2_mcart_1('#skF_3')!='#skF_6'), inference(splitRight, [status(thm)], [c_32])).
% 1.92/1.31  tff(c_110, plain, (![A_34, C_35, B_36]: (r2_hidden(k2_mcart_1(A_34), C_35) | ~r2_hidden(A_34, k2_zfmisc_1(B_36, C_35)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.92/1.31  tff(c_113, plain, (r2_hidden(k2_mcart_1('#skF_3'), k2_tarski('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_30, c_110])).
% 1.92/1.31  tff(c_2, plain, (![D_6, B_2, A_1]: (D_6=B_2 | D_6=A_1 | ~r2_hidden(D_6, k2_tarski(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.92/1.31  tff(c_116, plain, (k2_mcart_1('#skF_3')='#skF_6' | k2_mcart_1('#skF_3')='#skF_5'), inference(resolution, [status(thm)], [c_113, c_2])).
% 1.92/1.31  tff(c_120, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_63, c_116])).
% 1.92/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.92/1.31  
% 1.92/1.31  Inference rules
% 1.92/1.31  ----------------------
% 1.92/1.32  #Ref     : 0
% 1.92/1.32  #Sup     : 17
% 1.92/1.32  #Fact    : 0
% 1.92/1.32  #Define  : 0
% 1.92/1.32  #Split   : 2
% 1.92/1.32  #Chain   : 0
% 1.92/1.32  #Close   : 0
% 1.92/1.32  
% 1.92/1.32  Ordering : KBO
% 1.92/1.32  
% 1.92/1.32  Simplification rules
% 1.92/1.32  ----------------------
% 1.92/1.32  #Subsume      : 2
% 1.92/1.32  #Demod        : 6
% 1.92/1.32  #Tautology    : 13
% 1.92/1.32  #SimpNegUnit  : 2
% 1.92/1.32  #BackRed      : 0
% 1.92/1.32  
% 1.92/1.32  #Partial instantiations: 0
% 1.92/1.32  #Strategies tried      : 1
% 1.92/1.32  
% 1.92/1.32  Timing (in seconds)
% 1.92/1.32  ----------------------
% 1.92/1.32  Preprocessing        : 0.36
% 1.92/1.32  Parsing              : 0.17
% 1.92/1.32  CNF conversion       : 0.02
% 1.92/1.32  Main loop            : 0.13
% 1.92/1.32  Inferencing          : 0.04
% 1.92/1.32  Reduction            : 0.04
% 1.92/1.32  Demodulation         : 0.03
% 1.92/1.32  BG Simplification    : 0.01
% 1.92/1.32  Subsumption          : 0.03
% 1.92/1.32  Abstraction          : 0.01
% 1.92/1.32  MUC search           : 0.00
% 1.92/1.32  Cooper               : 0.00
% 1.92/1.32  Total                : 0.52
% 1.92/1.32  Index Insertion      : 0.00
% 1.92/1.32  Index Deletion       : 0.00
% 1.92/1.32  Index Matching       : 0.00
% 1.92/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
