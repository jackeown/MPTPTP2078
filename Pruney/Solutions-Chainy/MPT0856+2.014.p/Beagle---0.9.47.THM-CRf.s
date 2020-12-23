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
% DateTime   : Thu Dec  3 10:08:53 EST 2020

% Result     : Theorem 1.99s
% Output     : CNFRefutation 2.06s
% Verified   : 
% Statistics : Number of formulae       :   43 (  68 expanded)
%              Number of leaves         :   22 (  34 expanded)
%              Depth                    :   10
%              Number of atoms          :   42 (  91 expanded)
%              Number of equality atoms :   20 (  42 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4

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

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

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

tff(f_61,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r2_hidden(A,k2_zfmisc_1(k1_tarski(B),C))
       => ( k1_mcart_1(A) = B
          & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_mcart_1)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,k2_zfmisc_1(B,C))
        & ! [D,E] : k4_tarski(D,E) != A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l139_zfmisc_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_44,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(k1_tarski(C),D))
    <=> ( A = C
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t128_zfmisc_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

tff(c_24,plain,
    ( ~ r2_hidden(k2_mcart_1('#skF_3'),'#skF_5')
    | k1_mcart_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_63,plain,(
    k1_mcart_1('#skF_3') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_26,plain,(
    r2_hidden('#skF_3',k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_101,plain,(
    ! [A_48,B_49,C_50] :
      ( k4_tarski('#skF_1'(A_48,B_49,C_50),'#skF_2'(A_48,B_49,C_50)) = A_48
      | ~ r2_hidden(A_48,k2_zfmisc_1(B_49,C_50)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_22,plain,(
    ! [A_19,B_20] : k2_mcart_1(k4_tarski(A_19,B_20)) = B_20 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_136,plain,(
    ! [A_52,B_53,C_54] :
      ( k2_mcart_1(A_52) = '#skF_2'(A_52,B_53,C_54)
      | ~ r2_hidden(A_52,k2_zfmisc_1(B_53,C_54)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_22])).

tff(c_145,plain,(
    '#skF_2'('#skF_3',k1_tarski('#skF_4'),'#skF_5') = k2_mcart_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_136])).

tff(c_8,plain,(
    ! [A_7,B_8,C_9] :
      ( k4_tarski('#skF_1'(A_7,B_8,C_9),'#skF_2'(A_7,B_8,C_9)) = A_7
      | ~ r2_hidden(A_7,k2_zfmisc_1(B_8,C_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_149,plain,
    ( k4_tarski('#skF_1'('#skF_3',k1_tarski('#skF_4'),'#skF_5'),k2_mcart_1('#skF_3')) = '#skF_3'
    | ~ r2_hidden('#skF_3',k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_8])).

tff(c_153,plain,(
    k4_tarski('#skF_1'('#skF_3',k1_tarski('#skF_4'),'#skF_5'),k2_mcart_1('#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_149])).

tff(c_20,plain,(
    ! [A_19,B_20] : k1_mcart_1(k4_tarski(A_19,B_20)) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_167,plain,(
    '#skF_1'('#skF_3',k1_tarski('#skF_4'),'#skF_5') = k1_mcart_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_153,c_20])).

tff(c_175,plain,(
    k4_tarski(k1_mcart_1('#skF_3'),k2_mcart_1('#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_167,c_153])).

tff(c_14,plain,(
    ! [C_14,A_12,B_13,D_15] :
      ( C_14 = A_12
      | ~ r2_hidden(k4_tarski(A_12,B_13),k2_zfmisc_1(k1_tarski(C_14),D_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_218,plain,(
    ! [C_58,D_59] :
      ( k1_mcart_1('#skF_3') = C_58
      | ~ r2_hidden('#skF_3',k2_zfmisc_1(k1_tarski(C_58),D_59)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_175,c_14])).

tff(c_221,plain,(
    k1_mcart_1('#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_26,c_218])).

tff(c_225,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_63,c_221])).

tff(c_226,plain,(
    ~ r2_hidden(k2_mcart_1('#skF_3'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_232,plain,(
    ! [A_60,C_61,B_62] :
      ( r2_hidden(k2_mcart_1(A_60),C_61)
      | ~ r2_hidden(A_60,k2_zfmisc_1(B_62,C_61)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_234,plain,(
    r2_hidden(k2_mcart_1('#skF_3'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_26,c_232])).

tff(c_238,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_226,c_234])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:38:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.99/1.26  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.99/1.26  
% 1.99/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.99/1.26  %$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4
% 1.99/1.26  
% 1.99/1.26  %Foreground sorts:
% 1.99/1.26  
% 1.99/1.26  
% 1.99/1.26  %Background operators:
% 1.99/1.26  
% 1.99/1.26  
% 1.99/1.26  %Foreground operators:
% 1.99/1.26  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.99/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.99/1.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.99/1.26  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.99/1.26  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.99/1.26  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.99/1.26  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.99/1.26  tff('#skF_5', type, '#skF_5': $i).
% 1.99/1.26  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.99/1.26  tff('#skF_3', type, '#skF_3': $i).
% 1.99/1.26  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.99/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.99/1.26  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 1.99/1.26  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.99/1.26  tff('#skF_4', type, '#skF_4': $i).
% 1.99/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.99/1.26  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 1.99/1.26  
% 2.06/1.27  tff(f_61, negated_conjecture, ~(![A, B, C]: (r2_hidden(A, k2_zfmisc_1(k1_tarski(B), C)) => ((k1_mcart_1(A) = B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_mcart_1)).
% 2.06/1.27  tff(f_38, axiom, (![A, B, C]: ~(r2_hidden(A, k2_zfmisc_1(B, C)) & (![D, E]: ~(k4_tarski(D, E) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l139_zfmisc_1)).
% 2.06/1.27  tff(f_54, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 2.06/1.27  tff(f_44, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(k1_tarski(C), D)) <=> ((A = C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t128_zfmisc_1)).
% 2.06/1.27  tff(f_50, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 2.06/1.27  tff(c_24, plain, (~r2_hidden(k2_mcart_1('#skF_3'), '#skF_5') | k1_mcart_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.06/1.27  tff(c_63, plain, (k1_mcart_1('#skF_3')!='#skF_4'), inference(splitLeft, [status(thm)], [c_24])).
% 2.06/1.27  tff(c_26, plain, (r2_hidden('#skF_3', k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.06/1.27  tff(c_101, plain, (![A_48, B_49, C_50]: (k4_tarski('#skF_1'(A_48, B_49, C_50), '#skF_2'(A_48, B_49, C_50))=A_48 | ~r2_hidden(A_48, k2_zfmisc_1(B_49, C_50)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.06/1.27  tff(c_22, plain, (![A_19, B_20]: (k2_mcart_1(k4_tarski(A_19, B_20))=B_20)), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.06/1.27  tff(c_136, plain, (![A_52, B_53, C_54]: (k2_mcart_1(A_52)='#skF_2'(A_52, B_53, C_54) | ~r2_hidden(A_52, k2_zfmisc_1(B_53, C_54)))), inference(superposition, [status(thm), theory('equality')], [c_101, c_22])).
% 2.06/1.27  tff(c_145, plain, ('#skF_2'('#skF_3', k1_tarski('#skF_4'), '#skF_5')=k2_mcart_1('#skF_3')), inference(resolution, [status(thm)], [c_26, c_136])).
% 2.06/1.27  tff(c_8, plain, (![A_7, B_8, C_9]: (k4_tarski('#skF_1'(A_7, B_8, C_9), '#skF_2'(A_7, B_8, C_9))=A_7 | ~r2_hidden(A_7, k2_zfmisc_1(B_8, C_9)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.06/1.27  tff(c_149, plain, (k4_tarski('#skF_1'('#skF_3', k1_tarski('#skF_4'), '#skF_5'), k2_mcart_1('#skF_3'))='#skF_3' | ~r2_hidden('#skF_3', k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_145, c_8])).
% 2.06/1.27  tff(c_153, plain, (k4_tarski('#skF_1'('#skF_3', k1_tarski('#skF_4'), '#skF_5'), k2_mcart_1('#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_26, c_149])).
% 2.06/1.27  tff(c_20, plain, (![A_19, B_20]: (k1_mcart_1(k4_tarski(A_19, B_20))=A_19)), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.06/1.27  tff(c_167, plain, ('#skF_1'('#skF_3', k1_tarski('#skF_4'), '#skF_5')=k1_mcart_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_153, c_20])).
% 2.06/1.27  tff(c_175, plain, (k4_tarski(k1_mcart_1('#skF_3'), k2_mcart_1('#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_167, c_153])).
% 2.06/1.27  tff(c_14, plain, (![C_14, A_12, B_13, D_15]: (C_14=A_12 | ~r2_hidden(k4_tarski(A_12, B_13), k2_zfmisc_1(k1_tarski(C_14), D_15)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.06/1.27  tff(c_218, plain, (![C_58, D_59]: (k1_mcart_1('#skF_3')=C_58 | ~r2_hidden('#skF_3', k2_zfmisc_1(k1_tarski(C_58), D_59)))), inference(superposition, [status(thm), theory('equality')], [c_175, c_14])).
% 2.06/1.27  tff(c_221, plain, (k1_mcart_1('#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_26, c_218])).
% 2.06/1.27  tff(c_225, plain, $false, inference(negUnitSimplification, [status(thm)], [c_63, c_221])).
% 2.06/1.27  tff(c_226, plain, (~r2_hidden(k2_mcart_1('#skF_3'), '#skF_5')), inference(splitRight, [status(thm)], [c_24])).
% 2.06/1.27  tff(c_232, plain, (![A_60, C_61, B_62]: (r2_hidden(k2_mcart_1(A_60), C_61) | ~r2_hidden(A_60, k2_zfmisc_1(B_62, C_61)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.06/1.27  tff(c_234, plain, (r2_hidden(k2_mcart_1('#skF_3'), '#skF_5')), inference(resolution, [status(thm)], [c_26, c_232])).
% 2.06/1.27  tff(c_238, plain, $false, inference(negUnitSimplification, [status(thm)], [c_226, c_234])).
% 2.06/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.06/1.27  
% 2.06/1.27  Inference rules
% 2.06/1.27  ----------------------
% 2.06/1.27  #Ref     : 0
% 2.06/1.27  #Sup     : 51
% 2.06/1.27  #Fact    : 0
% 2.06/1.27  #Define  : 0
% 2.06/1.27  #Split   : 2
% 2.06/1.27  #Chain   : 0
% 2.06/1.27  #Close   : 0
% 2.06/1.27  
% 2.06/1.27  Ordering : KBO
% 2.06/1.27  
% 2.06/1.27  Simplification rules
% 2.06/1.27  ----------------------
% 2.06/1.27  #Subsume      : 8
% 2.06/1.27  #Demod        : 10
% 2.06/1.27  #Tautology    : 30
% 2.06/1.27  #SimpNegUnit  : 9
% 2.06/1.27  #BackRed      : 4
% 2.06/1.27  
% 2.06/1.27  #Partial instantiations: 0
% 2.06/1.27  #Strategies tried      : 1
% 2.06/1.27  
% 2.06/1.27  Timing (in seconds)
% 2.06/1.27  ----------------------
% 2.06/1.27  Preprocessing        : 0.27
% 2.06/1.28  Parsing              : 0.14
% 2.06/1.28  CNF conversion       : 0.02
% 2.06/1.28  Main loop            : 0.17
% 2.06/1.28  Inferencing          : 0.06
% 2.06/1.28  Reduction            : 0.05
% 2.06/1.28  Demodulation         : 0.04
% 2.06/1.28  BG Simplification    : 0.01
% 2.06/1.28  Subsumption          : 0.02
% 2.06/1.28  Abstraction          : 0.01
% 2.06/1.28  MUC search           : 0.00
% 2.06/1.28  Cooper               : 0.00
% 2.06/1.28  Total                : 0.46
% 2.06/1.28  Index Insertion      : 0.00
% 2.06/1.28  Index Deletion       : 0.00
% 2.06/1.28  Index Matching       : 0.00
% 2.06/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
