%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:07 EST 2020

% Result     : Theorem 1.66s
% Output     : CNFRefutation 1.66s
% Verified   : 
% Statistics : Number of formulae       :   32 (  43 expanded)
%              Number of leaves         :   17 (  23 expanded)
%              Depth                    :    4
%              Number of atoms          :   37 (  69 expanded)
%              Number of equality atoms :   26 (  51 expanded)
%              Maximal formula depth    :    9 (   4 average)
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

tff(f_52,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r2_hidden(A,k2_zfmisc_1(k1_tarski(B),k2_tarski(C,D)))
       => ( k1_mcart_1(A) = B
          & ( k2_mcart_1(A) = C
            | k2_mcart_1(A) = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_mcart_1)).

tff(f_27,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(A,k2_zfmisc_1(k2_tarski(B,C),D))
     => ( ( k1_mcart_1(A) = B
          | k1_mcart_1(A) = C )
        & r2_hidden(k2_mcart_1(A),D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_mcart_1)).

tff(f_43,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(A,k2_zfmisc_1(B,k2_tarski(C,D)))
     => ( r2_hidden(k1_mcart_1(A),B)
        & ( k2_mcart_1(A) = C
          | k2_mcart_1(A) = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_mcart_1)).

tff(c_16,plain,
    ( k2_mcart_1('#skF_1') != '#skF_3'
    | k1_mcart_1('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_26,plain,(
    k1_mcart_1('#skF_1') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_16])).

tff(c_12,plain,(
    r2_hidden('#skF_1',k2_zfmisc_1(k1_tarski('#skF_2'),k2_tarski('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_2,plain,(
    ! [A_1] : k2_tarski(A_1,A_1) = k1_tarski(A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_43,plain,(
    ! [A_25,C_26,B_27,D_28] :
      ( k1_mcart_1(A_25) = C_26
      | k1_mcart_1(A_25) = B_27
      | ~ r2_hidden(A_25,k2_zfmisc_1(k2_tarski(B_27,C_26),D_28)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_47,plain,(
    ! [A_29,A_30,D_31] :
      ( k1_mcart_1(A_29) = A_30
      | k1_mcart_1(A_29) = A_30
      | ~ r2_hidden(A_29,k2_zfmisc_1(k1_tarski(A_30),D_31)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_43])).

tff(c_50,plain,(
    k1_mcart_1('#skF_1') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_12,c_47])).

tff(c_54,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_26,c_50])).

tff(c_55,plain,(
    k2_mcart_1('#skF_1') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_16])).

tff(c_56,plain,(
    k1_mcart_1('#skF_1') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_16])).

tff(c_14,plain,
    ( k2_mcart_1('#skF_1') != '#skF_4'
    | k1_mcart_1('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_62,plain,(
    k2_mcart_1('#skF_1') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_14])).

tff(c_90,plain,(
    ! [A_53,D_54,C_55,B_56] :
      ( k2_mcart_1(A_53) = D_54
      | k2_mcart_1(A_53) = C_55
      | ~ r2_hidden(A_53,k2_zfmisc_1(B_56,k2_tarski(C_55,D_54))) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_93,plain,
    ( k2_mcart_1('#skF_1') = '#skF_4'
    | k2_mcart_1('#skF_1') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_12,c_90])).

tff(c_100,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_55,c_62,c_93])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.34  % Computer   : n019.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.21/0.34  % CPULimit   : 60
% 0.21/0.34  % DateTime   : Tue Dec  1 13:51:37 EST 2020
% 0.21/0.34  % CPUTime    : 
% 0.21/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.66/1.14  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.66/1.15  
% 1.66/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.66/1.15  %$ r2_hidden > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.66/1.15  
% 1.66/1.15  %Foreground sorts:
% 1.66/1.15  
% 1.66/1.15  
% 1.66/1.15  %Background operators:
% 1.66/1.15  
% 1.66/1.15  
% 1.66/1.15  %Foreground operators:
% 1.66/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.66/1.15  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.66/1.15  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.66/1.15  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.66/1.15  tff('#skF_2', type, '#skF_2': $i).
% 1.66/1.15  tff('#skF_3', type, '#skF_3': $i).
% 1.66/1.15  tff('#skF_1', type, '#skF_1': $i).
% 1.66/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.66/1.15  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 1.66/1.15  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.66/1.15  tff('#skF_4', type, '#skF_4': $i).
% 1.66/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.66/1.15  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 1.66/1.15  
% 1.66/1.16  tff(f_52, negated_conjecture, ~(![A, B, C, D]: (r2_hidden(A, k2_zfmisc_1(k1_tarski(B), k2_tarski(C, D))) => ((k1_mcart_1(A) = B) & ((k2_mcart_1(A) = C) | (k2_mcart_1(A) = D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_mcart_1)).
% 1.66/1.16  tff(f_27, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 1.66/1.16  tff(f_35, axiom, (![A, B, C, D]: (r2_hidden(A, k2_zfmisc_1(k2_tarski(B, C), D)) => (((k1_mcart_1(A) = B) | (k1_mcart_1(A) = C)) & r2_hidden(k2_mcart_1(A), D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_mcart_1)).
% 1.66/1.16  tff(f_43, axiom, (![A, B, C, D]: (r2_hidden(A, k2_zfmisc_1(B, k2_tarski(C, D))) => (r2_hidden(k1_mcart_1(A), B) & ((k2_mcart_1(A) = C) | (k2_mcart_1(A) = D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_mcart_1)).
% 1.66/1.16  tff(c_16, plain, (k2_mcart_1('#skF_1')!='#skF_3' | k1_mcart_1('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.66/1.16  tff(c_26, plain, (k1_mcart_1('#skF_1')!='#skF_2'), inference(splitLeft, [status(thm)], [c_16])).
% 1.66/1.16  tff(c_12, plain, (r2_hidden('#skF_1', k2_zfmisc_1(k1_tarski('#skF_2'), k2_tarski('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.66/1.16  tff(c_2, plain, (![A_1]: (k2_tarski(A_1, A_1)=k1_tarski(A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.66/1.16  tff(c_43, plain, (![A_25, C_26, B_27, D_28]: (k1_mcart_1(A_25)=C_26 | k1_mcart_1(A_25)=B_27 | ~r2_hidden(A_25, k2_zfmisc_1(k2_tarski(B_27, C_26), D_28)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.66/1.16  tff(c_47, plain, (![A_29, A_30, D_31]: (k1_mcart_1(A_29)=A_30 | k1_mcart_1(A_29)=A_30 | ~r2_hidden(A_29, k2_zfmisc_1(k1_tarski(A_30), D_31)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_43])).
% 1.66/1.16  tff(c_50, plain, (k1_mcart_1('#skF_1')='#skF_2'), inference(resolution, [status(thm)], [c_12, c_47])).
% 1.66/1.16  tff(c_54, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_26, c_50])).
% 1.66/1.16  tff(c_55, plain, (k2_mcart_1('#skF_1')!='#skF_3'), inference(splitRight, [status(thm)], [c_16])).
% 1.66/1.16  tff(c_56, plain, (k1_mcart_1('#skF_1')='#skF_2'), inference(splitRight, [status(thm)], [c_16])).
% 1.66/1.16  tff(c_14, plain, (k2_mcart_1('#skF_1')!='#skF_4' | k1_mcart_1('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.66/1.16  tff(c_62, plain, (k2_mcart_1('#skF_1')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_14])).
% 1.66/1.16  tff(c_90, plain, (![A_53, D_54, C_55, B_56]: (k2_mcart_1(A_53)=D_54 | k2_mcart_1(A_53)=C_55 | ~r2_hidden(A_53, k2_zfmisc_1(B_56, k2_tarski(C_55, D_54))))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.66/1.16  tff(c_93, plain, (k2_mcart_1('#skF_1')='#skF_4' | k2_mcart_1('#skF_1')='#skF_3'), inference(resolution, [status(thm)], [c_12, c_90])).
% 1.66/1.16  tff(c_100, plain, $false, inference(negUnitSimplification, [status(thm)], [c_55, c_62, c_93])).
% 1.66/1.16  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.66/1.16  
% 1.66/1.16  Inference rules
% 1.66/1.16  ----------------------
% 1.66/1.16  #Ref     : 0
% 1.66/1.16  #Sup     : 18
% 1.66/1.16  #Fact    : 0
% 1.66/1.16  #Define  : 0
% 1.66/1.16  #Split   : 1
% 1.66/1.16  #Chain   : 0
% 1.66/1.16  #Close   : 0
% 1.66/1.16  
% 1.66/1.16  Ordering : KBO
% 1.66/1.16  
% 1.66/1.16  Simplification rules
% 1.66/1.16  ----------------------
% 1.66/1.16  #Subsume      : 1
% 1.66/1.16  #Demod        : 3
% 1.66/1.16  #Tautology    : 5
% 1.66/1.16  #SimpNegUnit  : 2
% 1.66/1.16  #BackRed      : 0
% 1.66/1.16  
% 1.66/1.16  #Partial instantiations: 0
% 1.66/1.16  #Strategies tried      : 1
% 1.66/1.16  
% 1.66/1.16  Timing (in seconds)
% 1.66/1.16  ----------------------
% 1.66/1.16  Preprocessing        : 0.28
% 1.66/1.16  Parsing              : 0.15
% 1.66/1.16  CNF conversion       : 0.02
% 1.66/1.16  Main loop            : 0.12
% 1.66/1.16  Inferencing          : 0.05
% 1.66/1.16  Reduction            : 0.03
% 1.66/1.16  Demodulation         : 0.02
% 1.66/1.16  BG Simplification    : 0.01
% 1.66/1.16  Subsumption          : 0.02
% 1.66/1.16  Abstraction          : 0.01
% 1.66/1.16  MUC search           : 0.00
% 1.66/1.16  Cooper               : 0.00
% 1.66/1.16  Total                : 0.43
% 1.66/1.16  Index Insertion      : 0.00
% 1.66/1.16  Index Deletion       : 0.00
% 1.66/1.16  Index Matching       : 0.00
% 1.66/1.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
