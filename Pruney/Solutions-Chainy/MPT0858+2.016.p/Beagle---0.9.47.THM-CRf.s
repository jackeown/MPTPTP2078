%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:58 EST 2020

% Result     : Theorem 1.49s
% Output     : CNFRefutation 1.49s
% Verified   : 
% Statistics : Number of formulae       :   25 (  30 expanded)
%              Number of leaves         :   15 (  18 expanded)
%              Depth                    :    3
%              Number of atoms          :   22 (  34 expanded)
%              Number of equality atoms :   12 (  20 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_2 > #skF_3 > #skF_1

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(f_46,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r2_hidden(A,k2_zfmisc_1(k1_tarski(B),k1_tarski(C)))
       => ( k1_mcart_1(A) = B
          & k2_mcart_1(A) = C ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_mcart_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(k1_tarski(B),C))
     => ( k1_mcart_1(A) = B
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_mcart_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,k1_tarski(C)))
     => ( r2_hidden(k1_mcart_1(A),B)
        & k2_mcart_1(A) = C ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_mcart_1)).

tff(c_12,plain,
    ( k2_mcart_1('#skF_1') != '#skF_3'
    | k1_mcart_1('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_24,plain,(
    k1_mcart_1('#skF_1') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_12])).

tff(c_14,plain,(
    r2_hidden('#skF_1',k2_zfmisc_1(k1_tarski('#skF_2'),k1_tarski('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_25,plain,(
    ! [A_9,B_10,C_11] :
      ( k1_mcart_1(A_9) = B_10
      | ~ r2_hidden(A_9,k2_zfmisc_1(k1_tarski(B_10),C_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_28,plain,(
    k1_mcart_1('#skF_1') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_14,c_25])).

tff(c_32,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_28])).

tff(c_33,plain,(
    k2_mcart_1('#skF_1') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_12])).

tff(c_45,plain,(
    ! [A_15,C_16,B_17] :
      ( k2_mcart_1(A_15) = C_16
      | ~ r2_hidden(A_15,k2_zfmisc_1(B_17,k1_tarski(C_16))) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_48,plain,(
    k2_mcart_1('#skF_1') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_14,c_45])).

tff(c_52,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_33,c_48])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.32  % Computer   : n010.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % DateTime   : Tue Dec  1 15:57:29 EST 2020
% 0.13/0.32  % CPUTime    : 
% 0.13/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.49/1.04  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.49/1.04  
% 1.49/1.04  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.49/1.05  %$ r2_hidden > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_2 > #skF_3 > #skF_1
% 1.49/1.05  
% 1.49/1.05  %Foreground sorts:
% 1.49/1.05  
% 1.49/1.05  
% 1.49/1.05  %Background operators:
% 1.49/1.05  
% 1.49/1.05  
% 1.49/1.05  %Foreground operators:
% 1.49/1.05  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.49/1.05  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.49/1.05  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.49/1.05  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.49/1.05  tff('#skF_2', type, '#skF_2': $i).
% 1.49/1.05  tff('#skF_3', type, '#skF_3': $i).
% 1.49/1.05  tff('#skF_1', type, '#skF_1': $i).
% 1.49/1.05  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.49/1.05  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 1.49/1.05  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.49/1.05  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.49/1.05  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 1.49/1.05  
% 1.49/1.05  tff(f_46, negated_conjecture, ~(![A, B, C]: (r2_hidden(A, k2_zfmisc_1(k1_tarski(B), k1_tarski(C))) => ((k1_mcart_1(A) = B) & (k2_mcart_1(A) = C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_mcart_1)).
% 1.49/1.05  tff(f_33, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(k1_tarski(B), C)) => ((k1_mcart_1(A) = B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_mcart_1)).
% 1.49/1.05  tff(f_39, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, k1_tarski(C))) => (r2_hidden(k1_mcart_1(A), B) & (k2_mcart_1(A) = C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_mcart_1)).
% 1.49/1.05  tff(c_12, plain, (k2_mcart_1('#skF_1')!='#skF_3' | k1_mcart_1('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.49/1.05  tff(c_24, plain, (k1_mcart_1('#skF_1')!='#skF_2'), inference(splitLeft, [status(thm)], [c_12])).
% 1.49/1.05  tff(c_14, plain, (r2_hidden('#skF_1', k2_zfmisc_1(k1_tarski('#skF_2'), k1_tarski('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.49/1.05  tff(c_25, plain, (![A_9, B_10, C_11]: (k1_mcart_1(A_9)=B_10 | ~r2_hidden(A_9, k2_zfmisc_1(k1_tarski(B_10), C_11)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.49/1.05  tff(c_28, plain, (k1_mcart_1('#skF_1')='#skF_2'), inference(resolution, [status(thm)], [c_14, c_25])).
% 1.49/1.05  tff(c_32, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_28])).
% 1.49/1.05  tff(c_33, plain, (k2_mcart_1('#skF_1')!='#skF_3'), inference(splitRight, [status(thm)], [c_12])).
% 1.49/1.05  tff(c_45, plain, (![A_15, C_16, B_17]: (k2_mcart_1(A_15)=C_16 | ~r2_hidden(A_15, k2_zfmisc_1(B_17, k1_tarski(C_16))))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.49/1.05  tff(c_48, plain, (k2_mcart_1('#skF_1')='#skF_3'), inference(resolution, [status(thm)], [c_14, c_45])).
% 1.49/1.05  tff(c_52, plain, $false, inference(negUnitSimplification, [status(thm)], [c_33, c_48])).
% 1.49/1.05  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.49/1.05  
% 1.49/1.05  Inference rules
% 1.49/1.05  ----------------------
% 1.49/1.05  #Ref     : 0
% 1.49/1.05  #Sup     : 7
% 1.49/1.05  #Fact    : 0
% 1.49/1.05  #Define  : 0
% 1.49/1.05  #Split   : 1
% 1.49/1.05  #Chain   : 0
% 1.49/1.05  #Close   : 0
% 1.49/1.05  
% 1.49/1.05  Ordering : KBO
% 1.49/1.05  
% 1.49/1.05  Simplification rules
% 1.49/1.05  ----------------------
% 1.49/1.05  #Subsume      : 0
% 1.49/1.05  #Demod        : 1
% 1.49/1.05  #Tautology    : 5
% 1.49/1.05  #SimpNegUnit  : 2
% 1.49/1.05  #BackRed      : 0
% 1.49/1.05  
% 1.49/1.05  #Partial instantiations: 0
% 1.49/1.05  #Strategies tried      : 1
% 1.49/1.05  
% 1.49/1.05  Timing (in seconds)
% 1.49/1.05  ----------------------
% 1.49/1.05  Preprocessing        : 0.26
% 1.49/1.05  Parsing              : 0.14
% 1.49/1.05  CNF conversion       : 0.01
% 1.49/1.06  Main loop            : 0.07
% 1.49/1.06  Inferencing          : 0.03
% 1.49/1.06  Reduction            : 0.02
% 1.49/1.06  Demodulation         : 0.01
% 1.49/1.06  BG Simplification    : 0.01
% 1.49/1.06  Subsumption          : 0.01
% 1.49/1.06  Abstraction          : 0.01
% 1.49/1.06  MUC search           : 0.00
% 1.49/1.06  Cooper               : 0.00
% 1.49/1.06  Total                : 0.35
% 1.49/1.06  Index Insertion      : 0.00
% 1.49/1.06  Index Deletion       : 0.00
% 1.49/1.06  Index Matching       : 0.00
% 1.49/1.06  BG Taut test         : 0.00
%------------------------------------------------------------------------------
