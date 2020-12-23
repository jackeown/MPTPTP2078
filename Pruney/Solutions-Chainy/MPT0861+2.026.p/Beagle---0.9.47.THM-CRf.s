%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:04 EST 2020

% Result     : Theorem 1.78s
% Output     : CNFRefutation 1.78s
% Verified   : 
% Statistics : Number of formulae       :   35 (  48 expanded)
%              Number of leaves         :   18 (  25 expanded)
%              Depth                    :    4
%              Number of atoms          :   39 (  77 expanded)
%              Number of equality atoms :   27 (  57 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k1_enumset1 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(f_54,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r2_hidden(A,k2_zfmisc_1(k2_tarski(B,C),k1_tarski(D)))
       => ( ( k1_mcart_1(A) = B
            | k1_mcart_1(A) = C )
          & k2_mcart_1(A) = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_mcart_1)).

tff(f_27,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(A,k2_zfmisc_1(B,k2_tarski(C,D)))
     => ( r2_hidden(k1_mcart_1(A),B)
        & ( k2_mcart_1(A) = C
          | k2_mcart_1(A) = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_mcart_1)).

tff(f_37,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(A,k2_zfmisc_1(k2_tarski(B,C),D))
     => ( ( k1_mcart_1(A) = B
          | k1_mcart_1(A) = C )
        & r2_hidden(k2_mcart_1(A),D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_mcart_1)).

tff(c_18,plain,
    ( k1_mcart_1('#skF_1') != '#skF_2'
    | k2_mcart_1('#skF_1') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_28,plain,(
    k2_mcart_1('#skF_1') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_18])).

tff(c_14,plain,(
    r2_hidden('#skF_1',k2_zfmisc_1(k2_tarski('#skF_2','#skF_3'),k1_tarski('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2,plain,(
    ! [A_1] : k2_tarski(A_1,A_1) = k1_tarski(A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_68,plain,(
    ! [A_33,D_34,C_35,B_36] :
      ( k2_mcart_1(A_33) = D_34
      | k2_mcart_1(A_33) = C_35
      | ~ r2_hidden(A_33,k2_zfmisc_1(B_36,k2_tarski(C_35,D_34))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_72,plain,(
    ! [A_37,A_38,B_39] :
      ( k2_mcart_1(A_37) = A_38
      | k2_mcart_1(A_37) = A_38
      | ~ r2_hidden(A_37,k2_zfmisc_1(B_39,k1_tarski(A_38))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_68])).

tff(c_75,plain,(
    k2_mcart_1('#skF_1') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_14,c_72])).

tff(c_79,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_28,c_75])).

tff(c_80,plain,(
    k1_mcart_1('#skF_1') != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_81,plain,(
    k2_mcart_1('#skF_1') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_16,plain,
    ( k1_mcart_1('#skF_1') != '#skF_3'
    | k2_mcart_1('#skF_1') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_82,plain,(
    k2_mcart_1('#skF_1') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_16])).

tff(c_88,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_82])).

tff(c_89,plain,(
    k1_mcart_1('#skF_1') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_16])).

tff(c_132,plain,(
    ! [A_63,C_64,B_65,D_66] :
      ( k1_mcart_1(A_63) = C_64
      | k1_mcart_1(A_63) = B_65
      | ~ r2_hidden(A_63,k2_zfmisc_1(k2_tarski(B_65,C_64),D_66)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_135,plain,
    ( k1_mcart_1('#skF_1') = '#skF_3'
    | k1_mcart_1('#skF_1') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_14,c_132])).

tff(c_142,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_89,c_135])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:59:11 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.78/1.22  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.78/1.22  
% 1.78/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.78/1.22  %$ r2_hidden > k1_enumset1 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.78/1.22  
% 1.78/1.22  %Foreground sorts:
% 1.78/1.22  
% 1.78/1.22  
% 1.78/1.22  %Background operators:
% 1.78/1.22  
% 1.78/1.22  
% 1.78/1.22  %Foreground operators:
% 1.78/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.78/1.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.78/1.22  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.78/1.22  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.78/1.22  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.78/1.22  tff('#skF_2', type, '#skF_2': $i).
% 1.78/1.22  tff('#skF_3', type, '#skF_3': $i).
% 1.78/1.22  tff('#skF_1', type, '#skF_1': $i).
% 1.78/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.78/1.22  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 1.78/1.22  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.78/1.22  tff('#skF_4', type, '#skF_4': $i).
% 1.78/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.78/1.22  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 1.78/1.22  
% 1.78/1.23  tff(f_54, negated_conjecture, ~(![A, B, C, D]: (r2_hidden(A, k2_zfmisc_1(k2_tarski(B, C), k1_tarski(D))) => (((k1_mcart_1(A) = B) | (k1_mcart_1(A) = C)) & (k2_mcart_1(A) = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_mcart_1)).
% 1.78/1.23  tff(f_27, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 1.78/1.23  tff(f_45, axiom, (![A, B, C, D]: (r2_hidden(A, k2_zfmisc_1(B, k2_tarski(C, D))) => (r2_hidden(k1_mcart_1(A), B) & ((k2_mcart_1(A) = C) | (k2_mcart_1(A) = D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_mcart_1)).
% 1.78/1.23  tff(f_37, axiom, (![A, B, C, D]: (r2_hidden(A, k2_zfmisc_1(k2_tarski(B, C), D)) => (((k1_mcart_1(A) = B) | (k1_mcart_1(A) = C)) & r2_hidden(k2_mcart_1(A), D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_mcart_1)).
% 1.78/1.23  tff(c_18, plain, (k1_mcart_1('#skF_1')!='#skF_2' | k2_mcart_1('#skF_1')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.78/1.23  tff(c_28, plain, (k2_mcart_1('#skF_1')!='#skF_4'), inference(splitLeft, [status(thm)], [c_18])).
% 1.78/1.23  tff(c_14, plain, (r2_hidden('#skF_1', k2_zfmisc_1(k2_tarski('#skF_2', '#skF_3'), k1_tarski('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.78/1.23  tff(c_2, plain, (![A_1]: (k2_tarski(A_1, A_1)=k1_tarski(A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.78/1.23  tff(c_68, plain, (![A_33, D_34, C_35, B_36]: (k2_mcart_1(A_33)=D_34 | k2_mcart_1(A_33)=C_35 | ~r2_hidden(A_33, k2_zfmisc_1(B_36, k2_tarski(C_35, D_34))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.78/1.23  tff(c_72, plain, (![A_37, A_38, B_39]: (k2_mcart_1(A_37)=A_38 | k2_mcart_1(A_37)=A_38 | ~r2_hidden(A_37, k2_zfmisc_1(B_39, k1_tarski(A_38))))), inference(superposition, [status(thm), theory('equality')], [c_2, c_68])).
% 1.78/1.23  tff(c_75, plain, (k2_mcart_1('#skF_1')='#skF_4'), inference(resolution, [status(thm)], [c_14, c_72])).
% 1.78/1.23  tff(c_79, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_28, c_75])).
% 1.78/1.23  tff(c_80, plain, (k1_mcart_1('#skF_1')!='#skF_2'), inference(splitRight, [status(thm)], [c_18])).
% 1.78/1.23  tff(c_81, plain, (k2_mcart_1('#skF_1')='#skF_4'), inference(splitRight, [status(thm)], [c_18])).
% 1.78/1.23  tff(c_16, plain, (k1_mcart_1('#skF_1')!='#skF_3' | k2_mcart_1('#skF_1')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.78/1.23  tff(c_82, plain, (k2_mcart_1('#skF_1')!='#skF_4'), inference(splitLeft, [status(thm)], [c_16])).
% 1.78/1.23  tff(c_88, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_81, c_82])).
% 1.78/1.23  tff(c_89, plain, (k1_mcart_1('#skF_1')!='#skF_3'), inference(splitRight, [status(thm)], [c_16])).
% 1.78/1.23  tff(c_132, plain, (![A_63, C_64, B_65, D_66]: (k1_mcart_1(A_63)=C_64 | k1_mcart_1(A_63)=B_65 | ~r2_hidden(A_63, k2_zfmisc_1(k2_tarski(B_65, C_64), D_66)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.78/1.23  tff(c_135, plain, (k1_mcart_1('#skF_1')='#skF_3' | k1_mcart_1('#skF_1')='#skF_2'), inference(resolution, [status(thm)], [c_14, c_132])).
% 1.78/1.23  tff(c_142, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_89, c_135])).
% 1.78/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.78/1.23  
% 1.78/1.23  Inference rules
% 1.78/1.23  ----------------------
% 1.78/1.23  #Ref     : 0
% 1.78/1.23  #Sup     : 28
% 1.78/1.23  #Fact    : 0
% 1.78/1.23  #Define  : 0
% 1.78/1.23  #Split   : 3
% 1.78/1.23  #Chain   : 0
% 1.78/1.23  #Close   : 0
% 1.78/1.23  
% 1.78/1.23  Ordering : KBO
% 1.78/1.23  
% 1.78/1.23  Simplification rules
% 1.78/1.23  ----------------------
% 1.78/1.23  #Subsume      : 1
% 1.78/1.23  #Demod        : 5
% 1.78/1.23  #Tautology    : 14
% 1.78/1.23  #SimpNegUnit  : 2
% 1.78/1.23  #BackRed      : 1
% 1.78/1.23  
% 1.78/1.23  #Partial instantiations: 0
% 1.78/1.23  #Strategies tried      : 1
% 1.78/1.23  
% 1.78/1.23  Timing (in seconds)
% 1.78/1.23  ----------------------
% 1.78/1.23  Preprocessing        : 0.27
% 1.78/1.23  Parsing              : 0.14
% 1.78/1.23  CNF conversion       : 0.02
% 1.78/1.23  Main loop            : 0.14
% 1.78/1.23  Inferencing          : 0.06
% 1.78/1.23  Reduction            : 0.04
% 1.78/1.23  Demodulation         : 0.03
% 1.78/1.23  BG Simplification    : 0.01
% 1.78/1.23  Subsumption          : 0.02
% 1.78/1.23  Abstraction          : 0.01
% 1.78/1.23  MUC search           : 0.00
% 1.78/1.23  Cooper               : 0.00
% 1.78/1.23  Total                : 0.43
% 1.78/1.23  Index Insertion      : 0.00
% 1.78/1.23  Index Deletion       : 0.00
% 1.78/1.23  Index Matching       : 0.00
% 1.78/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
