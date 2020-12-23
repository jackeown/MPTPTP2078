%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:01 EST 2020

% Result     : Theorem 1.87s
% Output     : CNFRefutation 1.87s
% Verified   : 
% Statistics : Number of formulae       :   41 (  67 expanded)
%              Number of leaves         :   19 (  32 expanded)
%              Depth                    :    6
%              Number of atoms          :   55 ( 124 expanded)
%              Number of equality atoms :   21 (  52 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_mcart_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

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

tff(f_60,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r2_hidden(A,k2_zfmisc_1(B,k2_tarski(C,D)))
       => ( r2_hidden(k1_mcart_1(A),B)
          & ( k2_mcart_1(A) = C
            | k2_mcart_1(A) = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_mcart_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_33,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_47,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(A,k2_zfmisc_1(k2_tarski(B,C),D))
     => ( ( k1_mcart_1(A) = B
          | k1_mcart_1(A) = C )
        & r2_hidden(k2_mcart_1(A),D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_mcart_1)).

tff(c_24,plain,
    ( k2_mcart_1('#skF_1') != '#skF_4'
    | ~ r2_hidden(k1_mcart_1('#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_45,plain,(
    ~ r2_hidden(k1_mcart_1('#skF_1'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_22,plain,(
    r2_hidden('#skF_1',k2_zfmisc_1('#skF_2',k2_tarski('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_59,plain,(
    ! [A_25,B_26,C_27] :
      ( r2_hidden(k1_mcart_1(A_25),B_26)
      | ~ r2_hidden(A_25,k2_zfmisc_1(B_26,C_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_61,plain,(
    r2_hidden(k1_mcart_1('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_59])).

tff(c_65,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_45,c_61])).

tff(c_67,plain,(
    r2_hidden(k1_mcart_1('#skF_1'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_26,plain,
    ( k2_mcart_1('#skF_1') != '#skF_3'
    | ~ r2_hidden(k1_mcart_1('#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_69,plain,(
    k2_mcart_1('#skF_1') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_26])).

tff(c_66,plain,(
    k2_mcart_1('#skF_1') != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_79,plain,(
    ! [A_30,C_31,B_32] :
      ( r2_hidden(k2_mcart_1(A_30),C_31)
      | ~ r2_hidden(A_30,k2_zfmisc_1(B_32,C_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_82,plain,(
    r2_hidden(k2_mcart_1('#skF_1'),k2_tarski('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_22,c_79])).

tff(c_18,plain,(
    ! [A_14,B_15] : k1_mcart_1(k4_tarski(A_14,B_15)) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_4,plain,(
    ! [A_3,B_4,C_5,D_6] :
      ( r2_hidden(k4_tarski(A_3,B_4),k2_zfmisc_1(C_5,D_6))
      | ~ r2_hidden(B_4,D_6)
      | ~ r2_hidden(A_3,C_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_107,plain,(
    ! [A_48,C_49,B_50,D_51] :
      ( k1_mcart_1(A_48) = C_49
      | k1_mcart_1(A_48) = B_50
      | ~ r2_hidden(A_48,k2_zfmisc_1(k2_tarski(B_50,C_49),D_51)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_111,plain,(
    ! [A_3,D_6,B_50,C_49,B_4] :
      ( k1_mcart_1(k4_tarski(A_3,B_4)) = C_49
      | k1_mcart_1(k4_tarski(A_3,B_4)) = B_50
      | ~ r2_hidden(B_4,D_6)
      | ~ r2_hidden(A_3,k2_tarski(B_50,C_49)) ) ),
    inference(resolution,[status(thm)],[c_4,c_107])).

tff(c_113,plain,(
    ! [A_3,D_6,B_50,C_49,B_4] :
      ( C_49 = A_3
      | B_50 = A_3
      | ~ r2_hidden(B_4,D_6)
      | ~ r2_hidden(A_3,k2_tarski(B_50,C_49)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_18,c_111])).

tff(c_114,plain,(
    ! [B_4,D_6] : ~ r2_hidden(B_4,D_6) ),
    inference(splitLeft,[status(thm)],[c_113])).

tff(c_123,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_114,c_82])).

tff(c_125,plain,(
    ! [C_52,A_53,B_54] :
      ( C_52 = A_53
      | B_54 = A_53
      | ~ r2_hidden(A_53,k2_tarski(B_54,C_52)) ) ),
    inference(splitRight,[status(thm)],[c_113])).

tff(c_128,plain,
    ( k2_mcart_1('#skF_1') = '#skF_4'
    | k2_mcart_1('#skF_1') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_82,c_125])).

tff(c_132,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_69,c_66,c_128])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:04:38 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.87/1.19  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.87/1.20  
% 1.87/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.87/1.20  %$ r2_hidden > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_mcart_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.87/1.20  
% 1.87/1.20  %Foreground sorts:
% 1.87/1.20  
% 1.87/1.20  
% 1.87/1.20  %Background operators:
% 1.87/1.20  
% 1.87/1.20  
% 1.87/1.20  %Foreground operators:
% 1.87/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.87/1.20  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.87/1.20  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.87/1.20  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.87/1.20  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.87/1.20  tff('#skF_2', type, '#skF_2': $i).
% 1.87/1.20  tff('#skF_3', type, '#skF_3': $i).
% 1.87/1.20  tff('#skF_1', type, '#skF_1': $i).
% 1.87/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.87/1.20  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 1.87/1.20  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.87/1.20  tff('#skF_4', type, '#skF_4': $i).
% 1.87/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.87/1.20  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 1.87/1.20  
% 1.87/1.21  tff(f_60, negated_conjecture, ~(![A, B, C, D]: (r2_hidden(A, k2_zfmisc_1(B, k2_tarski(C, D))) => (r2_hidden(k1_mcart_1(A), B) & ((k2_mcart_1(A) = C) | (k2_mcart_1(A) = D))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_mcart_1)).
% 1.87/1.21  tff(f_39, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_mcart_1)).
% 1.87/1.21  tff(f_51, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_mcart_1)).
% 1.87/1.21  tff(f_33, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 1.87/1.21  tff(f_47, axiom, (![A, B, C, D]: (r2_hidden(A, k2_zfmisc_1(k2_tarski(B, C), D)) => (((k1_mcart_1(A) = B) | (k1_mcart_1(A) = C)) & r2_hidden(k2_mcart_1(A), D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_mcart_1)).
% 1.87/1.21  tff(c_24, plain, (k2_mcart_1('#skF_1')!='#skF_4' | ~r2_hidden(k1_mcart_1('#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.87/1.21  tff(c_45, plain, (~r2_hidden(k1_mcart_1('#skF_1'), '#skF_2')), inference(splitLeft, [status(thm)], [c_24])).
% 1.87/1.21  tff(c_22, plain, (r2_hidden('#skF_1', k2_zfmisc_1('#skF_2', k2_tarski('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.87/1.21  tff(c_59, plain, (![A_25, B_26, C_27]: (r2_hidden(k1_mcart_1(A_25), B_26) | ~r2_hidden(A_25, k2_zfmisc_1(B_26, C_27)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.87/1.21  tff(c_61, plain, (r2_hidden(k1_mcart_1('#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_22, c_59])).
% 1.87/1.21  tff(c_65, plain, $false, inference(negUnitSimplification, [status(thm)], [c_45, c_61])).
% 1.87/1.21  tff(c_67, plain, (r2_hidden(k1_mcart_1('#skF_1'), '#skF_2')), inference(splitRight, [status(thm)], [c_24])).
% 1.87/1.21  tff(c_26, plain, (k2_mcart_1('#skF_1')!='#skF_3' | ~r2_hidden(k1_mcart_1('#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.87/1.21  tff(c_69, plain, (k2_mcart_1('#skF_1')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_67, c_26])).
% 1.87/1.21  tff(c_66, plain, (k2_mcart_1('#skF_1')!='#skF_4'), inference(splitRight, [status(thm)], [c_24])).
% 1.87/1.21  tff(c_79, plain, (![A_30, C_31, B_32]: (r2_hidden(k2_mcart_1(A_30), C_31) | ~r2_hidden(A_30, k2_zfmisc_1(B_32, C_31)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.87/1.21  tff(c_82, plain, (r2_hidden(k2_mcart_1('#skF_1'), k2_tarski('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_22, c_79])).
% 1.87/1.21  tff(c_18, plain, (![A_14, B_15]: (k1_mcart_1(k4_tarski(A_14, B_15))=A_14)), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.87/1.21  tff(c_4, plain, (![A_3, B_4, C_5, D_6]: (r2_hidden(k4_tarski(A_3, B_4), k2_zfmisc_1(C_5, D_6)) | ~r2_hidden(B_4, D_6) | ~r2_hidden(A_3, C_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.87/1.21  tff(c_107, plain, (![A_48, C_49, B_50, D_51]: (k1_mcart_1(A_48)=C_49 | k1_mcart_1(A_48)=B_50 | ~r2_hidden(A_48, k2_zfmisc_1(k2_tarski(B_50, C_49), D_51)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.87/1.21  tff(c_111, plain, (![A_3, D_6, B_50, C_49, B_4]: (k1_mcart_1(k4_tarski(A_3, B_4))=C_49 | k1_mcart_1(k4_tarski(A_3, B_4))=B_50 | ~r2_hidden(B_4, D_6) | ~r2_hidden(A_3, k2_tarski(B_50, C_49)))), inference(resolution, [status(thm)], [c_4, c_107])).
% 1.87/1.21  tff(c_113, plain, (![A_3, D_6, B_50, C_49, B_4]: (C_49=A_3 | B_50=A_3 | ~r2_hidden(B_4, D_6) | ~r2_hidden(A_3, k2_tarski(B_50, C_49)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_18, c_111])).
% 1.87/1.21  tff(c_114, plain, (![B_4, D_6]: (~r2_hidden(B_4, D_6))), inference(splitLeft, [status(thm)], [c_113])).
% 1.87/1.21  tff(c_123, plain, $false, inference(negUnitSimplification, [status(thm)], [c_114, c_82])).
% 1.87/1.21  tff(c_125, plain, (![C_52, A_53, B_54]: (C_52=A_53 | B_54=A_53 | ~r2_hidden(A_53, k2_tarski(B_54, C_52)))), inference(splitRight, [status(thm)], [c_113])).
% 1.87/1.21  tff(c_128, plain, (k2_mcart_1('#skF_1')='#skF_4' | k2_mcart_1('#skF_1')='#skF_3'), inference(resolution, [status(thm)], [c_82, c_125])).
% 1.87/1.21  tff(c_132, plain, $false, inference(negUnitSimplification, [status(thm)], [c_69, c_66, c_128])).
% 1.87/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.87/1.21  
% 1.87/1.21  Inference rules
% 1.87/1.21  ----------------------
% 1.87/1.21  #Ref     : 0
% 1.87/1.21  #Sup     : 18
% 1.87/1.21  #Fact    : 0
% 1.87/1.21  #Define  : 0
% 1.87/1.21  #Split   : 2
% 1.87/1.21  #Chain   : 0
% 1.87/1.21  #Close   : 0
% 1.87/1.21  
% 1.87/1.21  Ordering : KBO
% 1.87/1.21  
% 1.87/1.21  Simplification rules
% 1.87/1.21  ----------------------
% 1.87/1.21  #Subsume      : 8
% 1.87/1.21  #Demod        : 6
% 1.87/1.21  #Tautology    : 13
% 1.87/1.21  #SimpNegUnit  : 10
% 1.87/1.21  #BackRed      : 3
% 1.87/1.21  
% 1.87/1.21  #Partial instantiations: 0
% 1.87/1.21  #Strategies tried      : 1
% 1.87/1.21  
% 1.87/1.21  Timing (in seconds)
% 1.87/1.21  ----------------------
% 1.96/1.21  Preprocessing        : 0.30
% 1.96/1.21  Parsing              : 0.17
% 1.96/1.21  CNF conversion       : 0.02
% 1.96/1.21  Main loop            : 0.12
% 1.96/1.21  Inferencing          : 0.04
% 1.96/1.21  Reduction            : 0.04
% 1.96/1.21  Demodulation         : 0.02
% 1.96/1.21  BG Simplification    : 0.01
% 1.96/1.21  Subsumption          : 0.02
% 1.96/1.21  Abstraction          : 0.01
% 1.96/1.21  MUC search           : 0.00
% 1.96/1.21  Cooper               : 0.00
% 1.96/1.21  Total                : 0.45
% 1.96/1.21  Index Insertion      : 0.00
% 1.96/1.21  Index Deletion       : 0.00
% 1.96/1.21  Index Matching       : 0.00
% 1.96/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
