%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:00 EST 2020

% Result     : Theorem 3.15s
% Output     : CNFRefutation 3.31s
% Verified   : 
% Statistics : Number of formulae       :   44 (  59 expanded)
%              Number of leaves         :   25 (  33 expanded)
%              Depth                    :    5
%              Number of atoms          :   51 (  93 expanded)
%              Number of equality atoms :   29 (  49 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_2 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_84,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r2_hidden(A,k2_zfmisc_1(B,k2_tarski(C,D)))
       => ( r2_hidden(k1_mcart_1(A),B)
          & ( k2_mcart_1(A) = C
            | k2_mcart_1(A) = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_mcart_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_36,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_38,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_69,axiom,(
    ! [A,B,C,D,E] :
      ( E = k2_enumset1(A,B,C,D)
    <=> ! [F] :
          ( r2_hidden(F,E)
        <=> ~ ( F != A
              & F != B
              & F != C
              & F != D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_enumset1)).

tff(c_64,plain,
    ( k2_mcart_1('#skF_4') != '#skF_6'
    | ~ r2_hidden(k1_mcart_1('#skF_4'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_75,plain,(
    ~ r2_hidden(k1_mcart_1('#skF_4'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_60,plain,(
    r2_hidden('#skF_4',k2_zfmisc_1('#skF_5',k2_tarski('#skF_6','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_171,plain,(
    ! [A_74,B_75,C_76] :
      ( r2_hidden(k1_mcart_1(A_74),B_75)
      | ~ r2_hidden(A_74,k2_zfmisc_1(B_75,C_76)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_176,plain,(
    r2_hidden(k1_mcart_1('#skF_4'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_60,c_171])).

tff(c_181,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_176])).

tff(c_182,plain,(
    k2_mcart_1('#skF_4') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_183,plain,(
    r2_hidden(k1_mcart_1('#skF_4'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_62,plain,
    ( k2_mcart_1('#skF_4') != '#skF_7'
    | ~ r2_hidden(k1_mcart_1('#skF_4'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_194,plain,(
    k2_mcart_1('#skF_4') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_183,c_62])).

tff(c_314,plain,(
    ! [A_125,C_126,B_127] :
      ( r2_hidden(k2_mcart_1(A_125),C_126)
      | ~ r2_hidden(A_125,k2_zfmisc_1(B_127,C_126)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_325,plain,(
    r2_hidden(k2_mcart_1('#skF_4'),k2_tarski('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_60,c_314])).

tff(c_10,plain,(
    ! [A_7,B_8] : k1_enumset1(A_7,A_7,B_8) = k2_tarski(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_12,plain,(
    ! [A_9,B_10,C_11] : k2_enumset1(A_9,A_9,B_10,C_11) = k1_enumset1(A_9,B_10,C_11) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_559,plain,(
    ! [B_200,D_199,C_197,F_198,A_196] :
      ( F_198 = D_199
      | F_198 = C_197
      | F_198 = B_200
      | F_198 = A_196
      | ~ r2_hidden(F_198,k2_enumset1(A_196,B_200,C_197,D_199)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_854,plain,(
    ! [F_251,C_252,B_253,A_254] :
      ( F_251 = C_252
      | F_251 = B_253
      | F_251 = A_254
      | F_251 = A_254
      | ~ r2_hidden(F_251,k1_enumset1(A_254,B_253,C_252)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_559])).

tff(c_908,plain,(
    ! [F_255,B_256,A_257] :
      ( F_255 = B_256
      | F_255 = A_257
      | F_255 = A_257
      | F_255 = A_257
      | ~ r2_hidden(F_255,k2_tarski(A_257,B_256)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_854])).

tff(c_931,plain,
    ( k2_mcart_1('#skF_4') = '#skF_7'
    | k2_mcart_1('#skF_4') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_325,c_908])).

tff(c_957,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_182,c_182,c_182,c_194,c_931])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:03:41 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.15/1.52  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.15/1.52  
% 3.15/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.15/1.52  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_2 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_1
% 3.15/1.52  
% 3.15/1.52  %Foreground sorts:
% 3.15/1.52  
% 3.15/1.52  
% 3.15/1.52  %Background operators:
% 3.15/1.52  
% 3.15/1.52  
% 3.15/1.52  %Foreground operators:
% 3.15/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.15/1.52  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.15/1.52  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.15/1.52  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.15/1.52  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i) > $i).
% 3.15/1.52  tff('#skF_7', type, '#skF_7': $i).
% 3.15/1.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.15/1.52  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.15/1.52  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.15/1.52  tff('#skF_5', type, '#skF_5': $i).
% 3.15/1.52  tff('#skF_6', type, '#skF_6': $i).
% 3.15/1.52  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.15/1.52  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i * $i) > $i).
% 3.15/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.15/1.52  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 3.15/1.52  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.15/1.52  tff('#skF_4', type, '#skF_4': $i).
% 3.15/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.15/1.52  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 3.15/1.52  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.15/1.52  
% 3.31/1.54  tff(f_84, negated_conjecture, ~(![A, B, C, D]: (r2_hidden(A, k2_zfmisc_1(B, k2_tarski(C, D))) => (r2_hidden(k1_mcart_1(A), B) & ((k2_mcart_1(A) = C) | (k2_mcart_1(A) = D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_mcart_1)).
% 3.31/1.54  tff(f_75, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 3.31/1.54  tff(f_36, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 3.31/1.54  tff(f_38, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 3.31/1.54  tff(f_69, axiom, (![A, B, C, D, E]: ((E = k2_enumset1(A, B, C, D)) <=> (![F]: (r2_hidden(F, E) <=> ~(((~(F = A) & ~(F = B)) & ~(F = C)) & ~(F = D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_enumset1)).
% 3.31/1.54  tff(c_64, plain, (k2_mcart_1('#skF_4')!='#skF_6' | ~r2_hidden(k1_mcart_1('#skF_4'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.31/1.54  tff(c_75, plain, (~r2_hidden(k1_mcart_1('#skF_4'), '#skF_5')), inference(splitLeft, [status(thm)], [c_64])).
% 3.31/1.54  tff(c_60, plain, (r2_hidden('#skF_4', k2_zfmisc_1('#skF_5', k2_tarski('#skF_6', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.31/1.54  tff(c_171, plain, (![A_74, B_75, C_76]: (r2_hidden(k1_mcart_1(A_74), B_75) | ~r2_hidden(A_74, k2_zfmisc_1(B_75, C_76)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.31/1.54  tff(c_176, plain, (r2_hidden(k1_mcart_1('#skF_4'), '#skF_5')), inference(resolution, [status(thm)], [c_60, c_171])).
% 3.31/1.54  tff(c_181, plain, $false, inference(negUnitSimplification, [status(thm)], [c_75, c_176])).
% 3.31/1.54  tff(c_182, plain, (k2_mcart_1('#skF_4')!='#skF_6'), inference(splitRight, [status(thm)], [c_64])).
% 3.31/1.54  tff(c_183, plain, (r2_hidden(k1_mcart_1('#skF_4'), '#skF_5')), inference(splitRight, [status(thm)], [c_64])).
% 3.31/1.54  tff(c_62, plain, (k2_mcart_1('#skF_4')!='#skF_7' | ~r2_hidden(k1_mcart_1('#skF_4'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.31/1.54  tff(c_194, plain, (k2_mcart_1('#skF_4')!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_183, c_62])).
% 3.31/1.54  tff(c_314, plain, (![A_125, C_126, B_127]: (r2_hidden(k2_mcart_1(A_125), C_126) | ~r2_hidden(A_125, k2_zfmisc_1(B_127, C_126)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.31/1.54  tff(c_325, plain, (r2_hidden(k2_mcart_1('#skF_4'), k2_tarski('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_60, c_314])).
% 3.31/1.54  tff(c_10, plain, (![A_7, B_8]: (k1_enumset1(A_7, A_7, B_8)=k2_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.31/1.54  tff(c_12, plain, (![A_9, B_10, C_11]: (k2_enumset1(A_9, A_9, B_10, C_11)=k1_enumset1(A_9, B_10, C_11))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.31/1.54  tff(c_559, plain, (![B_200, D_199, C_197, F_198, A_196]: (F_198=D_199 | F_198=C_197 | F_198=B_200 | F_198=A_196 | ~r2_hidden(F_198, k2_enumset1(A_196, B_200, C_197, D_199)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.31/1.54  tff(c_854, plain, (![F_251, C_252, B_253, A_254]: (F_251=C_252 | F_251=B_253 | F_251=A_254 | F_251=A_254 | ~r2_hidden(F_251, k1_enumset1(A_254, B_253, C_252)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_559])).
% 3.31/1.54  tff(c_908, plain, (![F_255, B_256, A_257]: (F_255=B_256 | F_255=A_257 | F_255=A_257 | F_255=A_257 | ~r2_hidden(F_255, k2_tarski(A_257, B_256)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_854])).
% 3.31/1.54  tff(c_931, plain, (k2_mcart_1('#skF_4')='#skF_7' | k2_mcart_1('#skF_4')='#skF_6'), inference(resolution, [status(thm)], [c_325, c_908])).
% 3.31/1.54  tff(c_957, plain, $false, inference(negUnitSimplification, [status(thm)], [c_182, c_182, c_182, c_194, c_931])).
% 3.31/1.54  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.31/1.54  
% 3.31/1.54  Inference rules
% 3.31/1.54  ----------------------
% 3.31/1.54  #Ref     : 0
% 3.31/1.54  #Sup     : 203
% 3.31/1.54  #Fact    : 0
% 3.31/1.54  #Define  : 0
% 3.31/1.54  #Split   : 1
% 3.31/1.54  #Chain   : 0
% 3.31/1.54  #Close   : 0
% 3.31/1.54  
% 3.31/1.54  Ordering : KBO
% 3.31/1.54  
% 3.31/1.54  Simplification rules
% 3.31/1.54  ----------------------
% 3.31/1.54  #Subsume      : 36
% 3.31/1.54  #Demod        : 19
% 3.31/1.54  #Tautology    : 42
% 3.31/1.54  #SimpNegUnit  : 2
% 3.31/1.54  #BackRed      : 0
% 3.31/1.54  
% 3.31/1.54  #Partial instantiations: 0
% 3.31/1.54  #Strategies tried      : 1
% 3.31/1.54  
% 3.31/1.54  Timing (in seconds)
% 3.31/1.54  ----------------------
% 3.31/1.54  Preprocessing        : 0.34
% 3.31/1.54  Parsing              : 0.17
% 3.31/1.54  CNF conversion       : 0.03
% 3.31/1.54  Main loop            : 0.43
% 3.31/1.54  Inferencing          : 0.16
% 3.31/1.54  Reduction            : 0.13
% 3.31/1.54  Demodulation         : 0.09
% 3.31/1.54  BG Simplification    : 0.02
% 3.31/1.54  Subsumption          : 0.09
% 3.31/1.54  Abstraction          : 0.03
% 3.31/1.54  MUC search           : 0.00
% 3.31/1.54  Cooper               : 0.00
% 3.31/1.54  Total                : 0.80
% 3.31/1.54  Index Insertion      : 0.00
% 3.31/1.54  Index Deletion       : 0.00
% 3.31/1.54  Index Matching       : 0.00
% 3.31/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
