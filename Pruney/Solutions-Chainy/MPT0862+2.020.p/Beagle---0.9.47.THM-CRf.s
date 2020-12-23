%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:07 EST 2020

% Result     : Theorem 1.56s
% Output     : CNFRefutation 1.64s
% Verified   : 
% Statistics : Number of formulae       :   29 (  37 expanded)
%              Number of leaves         :   16 (  21 expanded)
%              Depth                    :    4
%              Number of atoms          :   30 (  55 expanded)
%              Number of equality atoms :   20 (  39 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(f_48,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r2_hidden(A,k2_zfmisc_1(k1_tarski(B),k2_tarski(C,D)))
       => ( k1_mcart_1(A) = B
          & ( k2_mcart_1(A) = C
            | k2_mcart_1(A) = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_mcart_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(k1_tarski(B),C))
     => ( k1_mcart_1(A) = B
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_mcart_1)).

tff(f_39,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(A,k2_zfmisc_1(B,k2_tarski(C,D)))
     => ( r2_hidden(k1_mcart_1(A),B)
        & ( k2_mcart_1(A) = C
          | k2_mcart_1(A) = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_mcart_1)).

tff(c_14,plain,
    ( k2_mcart_1('#skF_1') != '#skF_3'
    | k1_mcart_1('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_15,plain,(
    k1_mcart_1('#skF_1') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_14])).

tff(c_10,plain,(
    r2_hidden('#skF_1',k2_zfmisc_1(k1_tarski('#skF_2'),k2_tarski('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_16,plain,(
    ! [A_8,B_9,C_10] :
      ( k1_mcart_1(A_8) = B_9
      | ~ r2_hidden(A_8,k2_zfmisc_1(k1_tarski(B_9),C_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_19,plain,(
    k1_mcart_1('#skF_1') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_10,c_16])).

tff(c_23,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_15,c_19])).

tff(c_24,plain,(
    k2_mcart_1('#skF_1') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_14])).

tff(c_25,plain,(
    k1_mcart_1('#skF_1') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_14])).

tff(c_12,plain,
    ( k2_mcart_1('#skF_1') != '#skF_4'
    | k1_mcart_1('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_31,plain,(
    k2_mcart_1('#skF_1') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_25,c_12])).

tff(c_49,plain,(
    ! [A_21,D_22,C_23,B_24] :
      ( k2_mcart_1(A_21) = D_22
      | k2_mcart_1(A_21) = C_23
      | ~ r2_hidden(A_21,k2_zfmisc_1(B_24,k2_tarski(C_23,D_22))) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_52,plain,
    ( k2_mcart_1('#skF_1') = '#skF_4'
    | k2_mcart_1('#skF_1') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_10,c_49])).

tff(c_56,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_31,c_52])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:24:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.56/1.08  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.64/1.08  
% 1.64/1.08  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.64/1.09  %$ r2_hidden > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.64/1.09  
% 1.64/1.09  %Foreground sorts:
% 1.64/1.09  
% 1.64/1.09  
% 1.64/1.09  %Background operators:
% 1.64/1.09  
% 1.64/1.09  
% 1.64/1.09  %Foreground operators:
% 1.64/1.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.64/1.09  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.64/1.09  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.64/1.09  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.64/1.09  tff('#skF_2', type, '#skF_2': $i).
% 1.64/1.09  tff('#skF_3', type, '#skF_3': $i).
% 1.64/1.09  tff('#skF_1', type, '#skF_1': $i).
% 1.64/1.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.64/1.09  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 1.64/1.09  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.64/1.09  tff('#skF_4', type, '#skF_4': $i).
% 1.64/1.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.64/1.09  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 1.64/1.09  
% 1.64/1.10  tff(f_48, negated_conjecture, ~(![A, B, C, D]: (r2_hidden(A, k2_zfmisc_1(k1_tarski(B), k2_tarski(C, D))) => ((k1_mcart_1(A) = B) & ((k2_mcart_1(A) = C) | (k2_mcart_1(A) = D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_mcart_1)).
% 1.64/1.10  tff(f_31, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(k1_tarski(B), C)) => ((k1_mcart_1(A) = B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_mcart_1)).
% 1.64/1.10  tff(f_39, axiom, (![A, B, C, D]: (r2_hidden(A, k2_zfmisc_1(B, k2_tarski(C, D))) => (r2_hidden(k1_mcart_1(A), B) & ((k2_mcart_1(A) = C) | (k2_mcart_1(A) = D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_mcart_1)).
% 1.64/1.10  tff(c_14, plain, (k2_mcart_1('#skF_1')!='#skF_3' | k1_mcart_1('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.64/1.10  tff(c_15, plain, (k1_mcart_1('#skF_1')!='#skF_2'), inference(splitLeft, [status(thm)], [c_14])).
% 1.64/1.10  tff(c_10, plain, (r2_hidden('#skF_1', k2_zfmisc_1(k1_tarski('#skF_2'), k2_tarski('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.64/1.10  tff(c_16, plain, (![A_8, B_9, C_10]: (k1_mcart_1(A_8)=B_9 | ~r2_hidden(A_8, k2_zfmisc_1(k1_tarski(B_9), C_10)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.64/1.10  tff(c_19, plain, (k1_mcart_1('#skF_1')='#skF_2'), inference(resolution, [status(thm)], [c_10, c_16])).
% 1.64/1.10  tff(c_23, plain, $false, inference(negUnitSimplification, [status(thm)], [c_15, c_19])).
% 1.64/1.10  tff(c_24, plain, (k2_mcart_1('#skF_1')!='#skF_3'), inference(splitRight, [status(thm)], [c_14])).
% 1.64/1.10  tff(c_25, plain, (k1_mcart_1('#skF_1')='#skF_2'), inference(splitRight, [status(thm)], [c_14])).
% 1.64/1.10  tff(c_12, plain, (k2_mcart_1('#skF_1')!='#skF_4' | k1_mcart_1('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.64/1.10  tff(c_31, plain, (k2_mcart_1('#skF_1')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_25, c_12])).
% 1.64/1.10  tff(c_49, plain, (![A_21, D_22, C_23, B_24]: (k2_mcart_1(A_21)=D_22 | k2_mcart_1(A_21)=C_23 | ~r2_hidden(A_21, k2_zfmisc_1(B_24, k2_tarski(C_23, D_22))))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.64/1.10  tff(c_52, plain, (k2_mcart_1('#skF_1')='#skF_4' | k2_mcart_1('#skF_1')='#skF_3'), inference(resolution, [status(thm)], [c_10, c_49])).
% 1.64/1.10  tff(c_56, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_31, c_52])).
% 1.64/1.10  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.64/1.10  
% 1.64/1.10  Inference rules
% 1.64/1.10  ----------------------
% 1.64/1.10  #Ref     : 0
% 1.64/1.10  #Sup     : 7
% 1.64/1.10  #Fact    : 0
% 1.64/1.10  #Define  : 0
% 1.64/1.10  #Split   : 1
% 1.64/1.10  #Chain   : 0
% 1.64/1.10  #Close   : 0
% 1.64/1.10  
% 1.64/1.10  Ordering : KBO
% 1.64/1.10  
% 1.64/1.10  Simplification rules
% 1.64/1.10  ----------------------
% 1.64/1.10  #Subsume      : 1
% 1.64/1.10  #Demod        : 3
% 1.64/1.10  #Tautology    : 3
% 1.64/1.10  #SimpNegUnit  : 2
% 1.64/1.10  #BackRed      : 0
% 1.64/1.10  
% 1.64/1.10  #Partial instantiations: 0
% 1.64/1.10  #Strategies tried      : 1
% 1.64/1.10  
% 1.64/1.10  Timing (in seconds)
% 1.64/1.10  ----------------------
% 1.64/1.10  Preprocessing        : 0.25
% 1.64/1.10  Parsing              : 0.14
% 1.64/1.10  CNF conversion       : 0.02
% 1.64/1.10  Main loop            : 0.09
% 1.64/1.10  Inferencing          : 0.03
% 1.64/1.10  Reduction            : 0.02
% 1.64/1.10  Demodulation         : 0.01
% 1.64/1.10  BG Simplification    : 0.01
% 1.64/1.10  Subsumption          : 0.01
% 1.64/1.10  Abstraction          : 0.00
% 1.64/1.10  MUC search           : 0.00
% 1.64/1.10  Cooper               : 0.00
% 1.64/1.10  Total                : 0.37
% 1.64/1.10  Index Insertion      : 0.00
% 1.64/1.10  Index Deletion       : 0.00
% 1.64/1.10  Index Matching       : 0.00
% 1.64/1.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------
