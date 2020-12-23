%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:05 EST 2020

% Result     : Theorem 2.24s
% Output     : CNFRefutation 2.24s
% Verified   : 
% Statistics : Number of formulae       :   34 (  42 expanded)
%              Number of leaves         :   19 (  24 expanded)
%              Depth                    :    4
%              Number of atoms          :   36 (  61 expanded)
%              Number of equality atoms :   21 (  40 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(f_57,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r2_hidden(A,k2_zfmisc_1(k1_tarski(B),k2_tarski(C,D)))
       => ( k1_mcart_1(A) = B
          & ( k2_mcart_1(A) = C
            | k2_mcart_1(A) = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_mcart_1)).

tff(f_40,axiom,(
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

tff(f_48,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(A,k2_zfmisc_1(B,k2_tarski(C,D)))
     => ( r2_hidden(k1_mcart_1(A),B)
        & ( k2_mcart_1(A) = C
          | k2_mcart_1(A) = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_mcart_1)).

tff(c_26,plain,
    ( k2_mcart_1('#skF_3') != '#skF_6'
    | k1_mcart_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_39,plain,(
    k1_mcart_1('#skF_3') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_24,plain,(
    r2_hidden('#skF_3',k2_zfmisc_1(k1_tarski('#skF_4'),k2_tarski('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_50,plain,(
    ! [A_21,B_22,C_23] :
      ( r2_hidden(k1_mcart_1(A_21),B_22)
      | ~ r2_hidden(A_21,k2_zfmisc_1(B_22,C_23)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_53,plain,(
    r2_hidden(k1_mcart_1('#skF_3'),k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_24,c_50])).

tff(c_2,plain,(
    ! [C_5,A_1] :
      ( C_5 = A_1
      | ~ r2_hidden(C_5,k1_tarski(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_56,plain,(
    k1_mcart_1('#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_53,c_2])).

tff(c_60,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_39,c_56])).

tff(c_62,plain,(
    k1_mcart_1('#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_28,plain,
    ( k2_mcart_1('#skF_3') != '#skF_5'
    | k1_mcart_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_74,plain,(
    k2_mcart_1('#skF_3') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_28])).

tff(c_61,plain,(
    k2_mcart_1('#skF_3') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_114,plain,(
    ! [A_40,D_41,C_42,B_43] :
      ( k2_mcart_1(A_40) = D_41
      | k2_mcart_1(A_40) = C_42
      | ~ r2_hidden(A_40,k2_zfmisc_1(B_43,k2_tarski(C_42,D_41))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_125,plain,
    ( k2_mcart_1('#skF_3') = '#skF_6'
    | k2_mcart_1('#skF_3') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_24,c_114])).

tff(c_134,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_61,c_125])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:20:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.24/1.58  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.24/1.59  
% 2.24/1.59  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.24/1.59  %$ r2_hidden > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.24/1.59  
% 2.24/1.59  %Foreground sorts:
% 2.24/1.59  
% 2.24/1.59  
% 2.24/1.59  %Background operators:
% 2.24/1.59  
% 2.24/1.59  
% 2.24/1.59  %Foreground operators:
% 2.24/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.24/1.59  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.24/1.59  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.24/1.59  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.24/1.59  tff('#skF_5', type, '#skF_5': $i).
% 2.24/1.59  tff('#skF_6', type, '#skF_6': $i).
% 2.24/1.59  tff('#skF_3', type, '#skF_3': $i).
% 2.24/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.24/1.59  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.24/1.59  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.24/1.59  tff('#skF_4', type, '#skF_4': $i).
% 2.24/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.24/1.59  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.24/1.59  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.24/1.59  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.24/1.59  
% 2.24/1.60  tff(f_57, negated_conjecture, ~(![A, B, C, D]: (r2_hidden(A, k2_zfmisc_1(k1_tarski(B), k2_tarski(C, D))) => ((k1_mcart_1(A) = B) & ((k2_mcart_1(A) = C) | (k2_mcart_1(A) = D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_mcart_1)).
% 2.24/1.60  tff(f_40, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 2.24/1.60  tff(f_32, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 2.24/1.60  tff(f_48, axiom, (![A, B, C, D]: (r2_hidden(A, k2_zfmisc_1(B, k2_tarski(C, D))) => (r2_hidden(k1_mcart_1(A), B) & ((k2_mcart_1(A) = C) | (k2_mcart_1(A) = D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_mcart_1)).
% 2.24/1.60  tff(c_26, plain, (k2_mcart_1('#skF_3')!='#skF_6' | k1_mcart_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.24/1.60  tff(c_39, plain, (k1_mcart_1('#skF_3')!='#skF_4'), inference(splitLeft, [status(thm)], [c_26])).
% 2.24/1.60  tff(c_24, plain, (r2_hidden('#skF_3', k2_zfmisc_1(k1_tarski('#skF_4'), k2_tarski('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.24/1.60  tff(c_50, plain, (![A_21, B_22, C_23]: (r2_hidden(k1_mcart_1(A_21), B_22) | ~r2_hidden(A_21, k2_zfmisc_1(B_22, C_23)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.24/1.60  tff(c_53, plain, (r2_hidden(k1_mcart_1('#skF_3'), k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_24, c_50])).
% 2.24/1.60  tff(c_2, plain, (![C_5, A_1]: (C_5=A_1 | ~r2_hidden(C_5, k1_tarski(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.24/1.60  tff(c_56, plain, (k1_mcart_1('#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_53, c_2])).
% 2.24/1.60  tff(c_60, plain, $false, inference(negUnitSimplification, [status(thm)], [c_39, c_56])).
% 2.24/1.60  tff(c_62, plain, (k1_mcart_1('#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_26])).
% 2.24/1.60  tff(c_28, plain, (k2_mcart_1('#skF_3')!='#skF_5' | k1_mcart_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.24/1.60  tff(c_74, plain, (k2_mcart_1('#skF_3')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_28])).
% 2.24/1.60  tff(c_61, plain, (k2_mcart_1('#skF_3')!='#skF_6'), inference(splitRight, [status(thm)], [c_26])).
% 2.24/1.60  tff(c_114, plain, (![A_40, D_41, C_42, B_43]: (k2_mcart_1(A_40)=D_41 | k2_mcart_1(A_40)=C_42 | ~r2_hidden(A_40, k2_zfmisc_1(B_43, k2_tarski(C_42, D_41))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.24/1.60  tff(c_125, plain, (k2_mcart_1('#skF_3')='#skF_6' | k2_mcart_1('#skF_3')='#skF_5'), inference(resolution, [status(thm)], [c_24, c_114])).
% 2.24/1.60  tff(c_134, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_61, c_125])).
% 2.24/1.60  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.24/1.60  
% 2.24/1.60  Inference rules
% 2.24/1.60  ----------------------
% 2.24/1.60  #Ref     : 0
% 2.24/1.60  #Sup     : 21
% 2.24/1.60  #Fact    : 0
% 2.24/1.60  #Define  : 0
% 2.24/1.60  #Split   : 1
% 2.24/1.60  #Chain   : 0
% 2.24/1.60  #Close   : 0
% 2.24/1.60  
% 2.24/1.60  Ordering : KBO
% 2.24/1.60  
% 2.24/1.60  Simplification rules
% 2.24/1.60  ----------------------
% 2.24/1.60  #Subsume      : 2
% 2.24/1.60  #Demod        : 3
% 2.24/1.60  #Tautology    : 7
% 2.24/1.60  #SimpNegUnit  : 2
% 2.24/1.60  #BackRed      : 0
% 2.24/1.60  
% 2.24/1.60  #Partial instantiations: 0
% 2.24/1.60  #Strategies tried      : 1
% 2.24/1.60  
% 2.24/1.60  Timing (in seconds)
% 2.24/1.60  ----------------------
% 2.36/1.63  Preprocessing        : 0.47
% 2.36/1.63  Parsing              : 0.24
% 2.36/1.63  CNF conversion       : 0.03
% 2.36/1.63  Main loop            : 0.23
% 2.36/1.63  Inferencing          : 0.08
% 2.36/1.63  Reduction            : 0.06
% 2.36/1.63  Demodulation         : 0.04
% 2.36/1.63  BG Simplification    : 0.02
% 2.36/1.63  Subsumption          : 0.05
% 2.36/1.63  Abstraction          : 0.02
% 2.36/1.63  MUC search           : 0.00
% 2.36/1.63  Cooper               : 0.00
% 2.36/1.63  Total                : 0.73
% 2.36/1.63  Index Insertion      : 0.00
% 2.36/1.63  Index Deletion       : 0.00
% 2.36/1.63  Index Matching       : 0.00
% 2.36/1.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------
