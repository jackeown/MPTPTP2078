%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:04 EST 2020

% Result     : Theorem 1.67s
% Output     : CNFRefutation 1.67s
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
        ( r2_hidden(A,k2_zfmisc_1(k2_tarski(B,C),k1_tarski(D)))
       => ( ( k1_mcart_1(A) = B
            | k1_mcart_1(A) = C )
          & k2_mcart_1(A) = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_mcart_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,k1_tarski(C)))
     => ( r2_hidden(k1_mcart_1(A),B)
        & k2_mcart_1(A) = C ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_mcart_1)).

tff(f_39,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(A,k2_zfmisc_1(k2_tarski(B,C),D))
     => ( ( k1_mcart_1(A) = B
          | k1_mcart_1(A) = C )
        & r2_hidden(k2_mcart_1(A),D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_mcart_1)).

tff(c_14,plain,
    ( k1_mcart_1('#skF_1') != '#skF_2'
    | k2_mcart_1('#skF_1') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_15,plain,(
    k2_mcart_1('#skF_1') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_14])).

tff(c_10,plain,(
    r2_hidden('#skF_1',k2_zfmisc_1(k2_tarski('#skF_2','#skF_3'),k1_tarski('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_16,plain,(
    ! [A_8,C_9,B_10] :
      ( k2_mcart_1(A_8) = C_9
      | ~ r2_hidden(A_8,k2_zfmisc_1(B_10,k1_tarski(C_9))) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_19,plain,(
    k2_mcart_1('#skF_1') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_10,c_16])).

tff(c_23,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_15,c_19])).

tff(c_24,plain,(
    k1_mcart_1('#skF_1') != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_14])).

tff(c_25,plain,(
    k2_mcart_1('#skF_1') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_14])).

tff(c_12,plain,
    ( k1_mcart_1('#skF_1') != '#skF_3'
    | k2_mcart_1('#skF_1') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_31,plain,(
    k1_mcart_1('#skF_1') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_25,c_12])).

tff(c_49,plain,(
    ! [A_21,C_22,B_23,D_24] :
      ( k1_mcart_1(A_21) = C_22
      | k1_mcart_1(A_21) = B_23
      | ~ r2_hidden(A_21,k2_zfmisc_1(k2_tarski(B_23,C_22),D_24)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_52,plain,
    ( k1_mcart_1('#skF_1') = '#skF_3'
    | k1_mcart_1('#skF_1') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_10,c_49])).

tff(c_56,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_31,c_52])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:08:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.67/1.25  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.67/1.25  
% 1.67/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.67/1.26  %$ r2_hidden > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.67/1.26  
% 1.67/1.26  %Foreground sorts:
% 1.67/1.26  
% 1.67/1.26  
% 1.67/1.26  %Background operators:
% 1.67/1.26  
% 1.67/1.26  
% 1.67/1.26  %Foreground operators:
% 1.67/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.67/1.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.67/1.26  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.67/1.26  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.67/1.26  tff('#skF_2', type, '#skF_2': $i).
% 1.67/1.26  tff('#skF_3', type, '#skF_3': $i).
% 1.67/1.26  tff('#skF_1', type, '#skF_1': $i).
% 1.67/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.67/1.26  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 1.67/1.26  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.67/1.26  tff('#skF_4', type, '#skF_4': $i).
% 1.67/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.67/1.26  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 1.67/1.26  
% 1.67/1.27  tff(f_48, negated_conjecture, ~(![A, B, C, D]: (r2_hidden(A, k2_zfmisc_1(k2_tarski(B, C), k1_tarski(D))) => (((k1_mcart_1(A) = B) | (k1_mcart_1(A) = C)) & (k2_mcart_1(A) = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_mcart_1)).
% 1.67/1.27  tff(f_31, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, k1_tarski(C))) => (r2_hidden(k1_mcart_1(A), B) & (k2_mcart_1(A) = C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_mcart_1)).
% 1.67/1.27  tff(f_39, axiom, (![A, B, C, D]: (r2_hidden(A, k2_zfmisc_1(k2_tarski(B, C), D)) => (((k1_mcart_1(A) = B) | (k1_mcart_1(A) = C)) & r2_hidden(k2_mcart_1(A), D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_mcart_1)).
% 1.67/1.27  tff(c_14, plain, (k1_mcart_1('#skF_1')!='#skF_2' | k2_mcart_1('#skF_1')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.67/1.27  tff(c_15, plain, (k2_mcart_1('#skF_1')!='#skF_4'), inference(splitLeft, [status(thm)], [c_14])).
% 1.67/1.27  tff(c_10, plain, (r2_hidden('#skF_1', k2_zfmisc_1(k2_tarski('#skF_2', '#skF_3'), k1_tarski('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.67/1.27  tff(c_16, plain, (![A_8, C_9, B_10]: (k2_mcart_1(A_8)=C_9 | ~r2_hidden(A_8, k2_zfmisc_1(B_10, k1_tarski(C_9))))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.67/1.27  tff(c_19, plain, (k2_mcart_1('#skF_1')='#skF_4'), inference(resolution, [status(thm)], [c_10, c_16])).
% 1.67/1.27  tff(c_23, plain, $false, inference(negUnitSimplification, [status(thm)], [c_15, c_19])).
% 1.67/1.27  tff(c_24, plain, (k1_mcart_1('#skF_1')!='#skF_2'), inference(splitRight, [status(thm)], [c_14])).
% 1.67/1.27  tff(c_25, plain, (k2_mcart_1('#skF_1')='#skF_4'), inference(splitRight, [status(thm)], [c_14])).
% 1.67/1.27  tff(c_12, plain, (k1_mcart_1('#skF_1')!='#skF_3' | k2_mcart_1('#skF_1')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.67/1.27  tff(c_31, plain, (k1_mcart_1('#skF_1')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_25, c_12])).
% 1.67/1.27  tff(c_49, plain, (![A_21, C_22, B_23, D_24]: (k1_mcart_1(A_21)=C_22 | k1_mcart_1(A_21)=B_23 | ~r2_hidden(A_21, k2_zfmisc_1(k2_tarski(B_23, C_22), D_24)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.67/1.27  tff(c_52, plain, (k1_mcart_1('#skF_1')='#skF_3' | k1_mcart_1('#skF_1')='#skF_2'), inference(resolution, [status(thm)], [c_10, c_49])).
% 1.67/1.27  tff(c_56, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_31, c_52])).
% 1.67/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.67/1.27  
% 1.67/1.27  Inference rules
% 1.67/1.27  ----------------------
% 1.67/1.27  #Ref     : 0
% 1.67/1.27  #Sup     : 7
% 1.67/1.27  #Fact    : 0
% 1.67/1.27  #Define  : 0
% 1.67/1.27  #Split   : 1
% 1.67/1.27  #Chain   : 0
% 1.67/1.27  #Close   : 0
% 1.67/1.27  
% 1.67/1.27  Ordering : KBO
% 1.67/1.27  
% 1.67/1.27  Simplification rules
% 1.67/1.27  ----------------------
% 1.67/1.27  #Subsume      : 1
% 1.67/1.27  #Demod        : 3
% 1.67/1.27  #Tautology    : 3
% 1.67/1.27  #SimpNegUnit  : 2
% 1.67/1.27  #BackRed      : 0
% 1.67/1.27  
% 1.67/1.27  #Partial instantiations: 0
% 1.67/1.27  #Strategies tried      : 1
% 1.67/1.27  
% 1.67/1.27  Timing (in seconds)
% 1.67/1.27  ----------------------
% 1.67/1.27  Preprocessing        : 0.26
% 1.67/1.27  Parsing              : 0.14
% 1.67/1.27  CNF conversion       : 0.02
% 1.67/1.27  Main loop            : 0.09
% 1.67/1.27  Inferencing          : 0.04
% 1.67/1.27  Reduction            : 0.02
% 1.67/1.27  Demodulation         : 0.01
% 1.67/1.27  BG Simplification    : 0.01
% 1.67/1.27  Subsumption          : 0.01
% 1.67/1.27  Abstraction          : 0.00
% 1.67/1.27  MUC search           : 0.00
% 1.67/1.27  Cooper               : 0.00
% 1.67/1.27  Total                : 0.38
% 1.67/1.27  Index Insertion      : 0.00
% 1.67/1.27  Index Deletion       : 0.00
% 1.67/1.27  Index Matching       : 0.00
% 1.67/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
