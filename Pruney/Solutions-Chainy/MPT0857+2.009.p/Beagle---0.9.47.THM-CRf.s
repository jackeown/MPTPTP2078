%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:55 EST 2020

% Result     : Theorem 1.98s
% Output     : CNFRefutation 1.98s
% Verified   : 
% Statistics : Number of formulae       :   43 (  58 expanded)
%              Number of leaves         :   22 (  31 expanded)
%              Depth                    :    8
%              Number of atoms          :   43 (  75 expanded)
%              Number of equality atoms :   20 (  32 expanded)
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
        ( r2_hidden(A,k2_zfmisc_1(B,k1_tarski(C)))
       => ( r2_hidden(k1_mcart_1(A),B)
          & k2_mcart_1(A) = C ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_mcart_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

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
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,k1_tarski(D)))
    <=> ( r2_hidden(A,C)
        & B = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t129_zfmisc_1)).

tff(c_24,plain,
    ( k2_mcart_1('#skF_3') != '#skF_5'
    | ~ r2_hidden(k1_mcart_1('#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_63,plain,(
    ~ r2_hidden(k1_mcart_1('#skF_3'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_26,plain,(
    r2_hidden('#skF_3',k2_zfmisc_1('#skF_4',k1_tarski('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_77,plain,(
    ! [A_34,B_35,C_36] :
      ( r2_hidden(k1_mcart_1(A_34),B_35)
      | ~ r2_hidden(A_34,k2_zfmisc_1(B_35,C_36)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_79,plain,(
    r2_hidden(k1_mcart_1('#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_77])).

tff(c_83,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_63,c_79])).

tff(c_84,plain,(
    k2_mcart_1('#skF_3') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_135,plain,(
    ! [A_58,B_59,C_60] :
      ( k4_tarski('#skF_1'(A_58,B_59,C_60),'#skF_2'(A_58,B_59,C_60)) = A_58
      | ~ r2_hidden(A_58,k2_zfmisc_1(B_59,C_60)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_20,plain,(
    ! [A_19,B_20] : k1_mcart_1(k4_tarski(A_19,B_20)) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_159,plain,(
    ! [A_61,B_62,C_63] :
      ( k1_mcart_1(A_61) = '#skF_1'(A_61,B_62,C_63)
      | ~ r2_hidden(A_61,k2_zfmisc_1(B_62,C_63)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_20])).

tff(c_168,plain,(
    '#skF_1'('#skF_3','#skF_4',k1_tarski('#skF_5')) = k1_mcart_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_159])).

tff(c_22,plain,(
    ! [A_19,B_20] : k2_mcart_1(k4_tarski(A_19,B_20)) = B_20 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_169,plain,(
    ! [A_64,B_65,C_66] :
      ( k2_mcart_1(A_64) = '#skF_2'(A_64,B_65,C_66)
      | ~ r2_hidden(A_64,k2_zfmisc_1(B_65,C_66)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_22])).

tff(c_178,plain,(
    '#skF_2'('#skF_3','#skF_4',k1_tarski('#skF_5')) = k2_mcart_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_169])).

tff(c_8,plain,(
    ! [A_7,B_8,C_9] :
      ( k4_tarski('#skF_1'(A_7,B_8,C_9),'#skF_2'(A_7,B_8,C_9)) = A_7
      | ~ r2_hidden(A_7,k2_zfmisc_1(B_8,C_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_191,plain,
    ( k4_tarski('#skF_1'('#skF_3','#skF_4',k1_tarski('#skF_5')),k2_mcart_1('#skF_3')) = '#skF_3'
    | ~ r2_hidden('#skF_3',k2_zfmisc_1('#skF_4',k1_tarski('#skF_5'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_178,c_8])).

tff(c_195,plain,(
    k4_tarski(k1_mcart_1('#skF_3'),k2_mcart_1('#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_168,c_191])).

tff(c_12,plain,(
    ! [D_15,B_13,A_12,C_14] :
      ( D_15 = B_13
      | ~ r2_hidden(k4_tarski(A_12,B_13),k2_zfmisc_1(C_14,k1_tarski(D_15))) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_219,plain,(
    ! [D_67,C_68] :
      ( k2_mcart_1('#skF_3') = D_67
      | ~ r2_hidden('#skF_3',k2_zfmisc_1(C_68,k1_tarski(D_67))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_195,c_12])).

tff(c_222,plain,(
    k2_mcart_1('#skF_3') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_26,c_219])).

tff(c_226,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_222])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n011.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 14:20:42 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.98/1.26  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.98/1.27  
% 1.98/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.98/1.27  %$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4
% 1.98/1.27  
% 1.98/1.27  %Foreground sorts:
% 1.98/1.27  
% 1.98/1.27  
% 1.98/1.27  %Background operators:
% 1.98/1.27  
% 1.98/1.27  
% 1.98/1.27  %Foreground operators:
% 1.98/1.27  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.98/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.98/1.27  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.98/1.27  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.98/1.27  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.98/1.27  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.98/1.27  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.98/1.27  tff('#skF_5', type, '#skF_5': $i).
% 1.98/1.27  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.98/1.27  tff('#skF_3', type, '#skF_3': $i).
% 1.98/1.27  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.98/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.98/1.27  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 1.98/1.27  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.98/1.27  tff('#skF_4', type, '#skF_4': $i).
% 1.98/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.98/1.27  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 1.98/1.27  
% 1.98/1.28  tff(f_61, negated_conjecture, ~(![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, k1_tarski(C))) => (r2_hidden(k1_mcart_1(A), B) & (k2_mcart_1(A) = C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_mcart_1)).
% 1.98/1.28  tff(f_50, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 1.98/1.28  tff(f_38, axiom, (![A, B, C]: ~(r2_hidden(A, k2_zfmisc_1(B, C)) & (![D, E]: ~(k4_tarski(D, E) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l139_zfmisc_1)).
% 1.98/1.28  tff(f_54, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 1.98/1.28  tff(f_44, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, k1_tarski(D))) <=> (r2_hidden(A, C) & (B = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t129_zfmisc_1)).
% 1.98/1.28  tff(c_24, plain, (k2_mcart_1('#skF_3')!='#skF_5' | ~r2_hidden(k1_mcart_1('#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.98/1.28  tff(c_63, plain, (~r2_hidden(k1_mcart_1('#skF_3'), '#skF_4')), inference(splitLeft, [status(thm)], [c_24])).
% 1.98/1.28  tff(c_26, plain, (r2_hidden('#skF_3', k2_zfmisc_1('#skF_4', k1_tarski('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.98/1.28  tff(c_77, plain, (![A_34, B_35, C_36]: (r2_hidden(k1_mcart_1(A_34), B_35) | ~r2_hidden(A_34, k2_zfmisc_1(B_35, C_36)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.98/1.28  tff(c_79, plain, (r2_hidden(k1_mcart_1('#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_26, c_77])).
% 1.98/1.28  tff(c_83, plain, $false, inference(negUnitSimplification, [status(thm)], [c_63, c_79])).
% 1.98/1.28  tff(c_84, plain, (k2_mcart_1('#skF_3')!='#skF_5'), inference(splitRight, [status(thm)], [c_24])).
% 1.98/1.28  tff(c_135, plain, (![A_58, B_59, C_60]: (k4_tarski('#skF_1'(A_58, B_59, C_60), '#skF_2'(A_58, B_59, C_60))=A_58 | ~r2_hidden(A_58, k2_zfmisc_1(B_59, C_60)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.98/1.28  tff(c_20, plain, (![A_19, B_20]: (k1_mcart_1(k4_tarski(A_19, B_20))=A_19)), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.98/1.28  tff(c_159, plain, (![A_61, B_62, C_63]: (k1_mcart_1(A_61)='#skF_1'(A_61, B_62, C_63) | ~r2_hidden(A_61, k2_zfmisc_1(B_62, C_63)))), inference(superposition, [status(thm), theory('equality')], [c_135, c_20])).
% 1.98/1.28  tff(c_168, plain, ('#skF_1'('#skF_3', '#skF_4', k1_tarski('#skF_5'))=k1_mcart_1('#skF_3')), inference(resolution, [status(thm)], [c_26, c_159])).
% 1.98/1.28  tff(c_22, plain, (![A_19, B_20]: (k2_mcart_1(k4_tarski(A_19, B_20))=B_20)), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.98/1.28  tff(c_169, plain, (![A_64, B_65, C_66]: (k2_mcart_1(A_64)='#skF_2'(A_64, B_65, C_66) | ~r2_hidden(A_64, k2_zfmisc_1(B_65, C_66)))), inference(superposition, [status(thm), theory('equality')], [c_135, c_22])).
% 1.98/1.28  tff(c_178, plain, ('#skF_2'('#skF_3', '#skF_4', k1_tarski('#skF_5'))=k2_mcart_1('#skF_3')), inference(resolution, [status(thm)], [c_26, c_169])).
% 1.98/1.28  tff(c_8, plain, (![A_7, B_8, C_9]: (k4_tarski('#skF_1'(A_7, B_8, C_9), '#skF_2'(A_7, B_8, C_9))=A_7 | ~r2_hidden(A_7, k2_zfmisc_1(B_8, C_9)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.98/1.28  tff(c_191, plain, (k4_tarski('#skF_1'('#skF_3', '#skF_4', k1_tarski('#skF_5')), k2_mcart_1('#skF_3'))='#skF_3' | ~r2_hidden('#skF_3', k2_zfmisc_1('#skF_4', k1_tarski('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_178, c_8])).
% 1.98/1.28  tff(c_195, plain, (k4_tarski(k1_mcart_1('#skF_3'), k2_mcart_1('#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_26, c_168, c_191])).
% 1.98/1.28  tff(c_12, plain, (![D_15, B_13, A_12, C_14]: (D_15=B_13 | ~r2_hidden(k4_tarski(A_12, B_13), k2_zfmisc_1(C_14, k1_tarski(D_15))))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.98/1.28  tff(c_219, plain, (![D_67, C_68]: (k2_mcart_1('#skF_3')=D_67 | ~r2_hidden('#skF_3', k2_zfmisc_1(C_68, k1_tarski(D_67))))), inference(superposition, [status(thm), theory('equality')], [c_195, c_12])).
% 1.98/1.28  tff(c_222, plain, (k2_mcart_1('#skF_3')='#skF_5'), inference(resolution, [status(thm)], [c_26, c_219])).
% 1.98/1.28  tff(c_226, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84, c_222])).
% 1.98/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.98/1.28  
% 1.98/1.28  Inference rules
% 1.98/1.28  ----------------------
% 1.98/1.28  #Ref     : 0
% 1.98/1.28  #Sup     : 45
% 1.98/1.28  #Fact    : 0
% 1.98/1.28  #Define  : 0
% 1.98/1.28  #Split   : 2
% 1.98/1.28  #Chain   : 0
% 1.98/1.28  #Close   : 0
% 1.98/1.28  
% 1.98/1.28  Ordering : KBO
% 1.98/1.28  
% 1.98/1.28  Simplification rules
% 1.98/1.28  ----------------------
% 1.98/1.28  #Subsume      : 6
% 1.98/1.28  #Demod        : 10
% 1.98/1.28  #Tautology    : 27
% 1.98/1.28  #SimpNegUnit  : 9
% 1.98/1.28  #BackRed      : 3
% 1.98/1.28  
% 1.98/1.28  #Partial instantiations: 0
% 1.98/1.28  #Strategies tried      : 1
% 1.98/1.28  
% 1.98/1.28  Timing (in seconds)
% 1.98/1.28  ----------------------
% 1.98/1.28  Preprocessing        : 0.32
% 1.98/1.28  Parsing              : 0.17
% 1.98/1.28  CNF conversion       : 0.02
% 1.98/1.28  Main loop            : 0.16
% 1.98/1.28  Inferencing          : 0.06
% 1.98/1.28  Reduction            : 0.05
% 1.98/1.28  Demodulation         : 0.03
% 1.98/1.28  BG Simplification    : 0.01
% 1.98/1.28  Subsumption          : 0.02
% 1.98/1.28  Abstraction          : 0.01
% 1.98/1.28  MUC search           : 0.00
% 1.98/1.28  Cooper               : 0.00
% 1.98/1.28  Total                : 0.51
% 1.98/1.28  Index Insertion      : 0.00
% 1.98/1.28  Index Deletion       : 0.00
% 1.98/1.28  Index Matching       : 0.00
% 1.98/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
