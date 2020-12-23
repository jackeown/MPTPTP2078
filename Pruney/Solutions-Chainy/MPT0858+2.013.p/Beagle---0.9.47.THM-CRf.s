%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:57 EST 2020

% Result     : Theorem 1.86s
% Output     : CNFRefutation 1.86s
% Verified   : 
% Statistics : Number of formulae       :   36 (  45 expanded)
%              Number of leaves         :   19 (  25 expanded)
%              Depth                    :    4
%              Number of atoms          :   35 (  56 expanded)
%              Number of equality atoms :   18 (  30 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_2 > #skF_3 > #skF_1

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(f_54,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r2_hidden(A,k2_zfmisc_1(k1_tarski(B),k1_tarski(C)))
       => ( k1_mcart_1(A) = B
          & k2_mcart_1(A) = C ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_mcart_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(c_20,plain,
    ( k2_mcart_1('#skF_1') != '#skF_3'
    | k1_mcart_1('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_32,plain,(
    k1_mcart_1('#skF_1') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_20])).

tff(c_22,plain,(
    r2_hidden('#skF_1',k2_zfmisc_1(k1_tarski('#skF_2'),k1_tarski('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_121,plain,(
    ! [A_33,B_34,C_35] :
      ( r2_hidden(k1_mcart_1(A_33),B_34)
      | ~ r2_hidden(A_33,k2_zfmisc_1(B_34,C_35)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_124,plain,(
    r2_hidden(k1_mcart_1('#skF_1'),k1_tarski('#skF_2')) ),
    inference(resolution,[status(thm)],[c_22,c_121])).

tff(c_64,plain,(
    ! [A_23,B_24] :
      ( k4_xboole_0(k1_tarski(A_23),k1_tarski(B_24)) = k1_tarski(A_23)
      | B_24 = A_23 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_12,plain,(
    ! [B_10,A_9] :
      ( ~ r2_hidden(B_10,A_9)
      | k4_xboole_0(A_9,k1_tarski(B_10)) != A_9 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_87,plain,(
    ! [B_24,A_23] :
      ( ~ r2_hidden(B_24,k1_tarski(A_23))
      | B_24 = A_23 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_12])).

tff(c_127,plain,(
    k1_mcart_1('#skF_1') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_124,c_87])).

tff(c_131,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_127])).

tff(c_132,plain,(
    k2_mcart_1('#skF_1') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_217,plain,(
    ! [A_54,C_55,B_56] :
      ( r2_hidden(k2_mcart_1(A_54),C_55)
      | ~ r2_hidden(A_54,k2_zfmisc_1(B_56,C_55)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_220,plain,(
    r2_hidden(k2_mcart_1('#skF_1'),k1_tarski('#skF_3')) ),
    inference(resolution,[status(thm)],[c_22,c_217])).

tff(c_183,plain,(
    ! [A_50,B_51] :
      ( k4_xboole_0(k1_tarski(A_50),k1_tarski(B_51)) = k1_tarski(A_50)
      | B_51 = A_50 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_205,plain,(
    ! [B_51,A_50] :
      ( ~ r2_hidden(B_51,k1_tarski(A_50))
      | B_51 = A_50 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_183,c_12])).

tff(c_223,plain,(
    k2_mcart_1('#skF_1') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_220,c_205])).

tff(c_227,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_132,c_223])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:51:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.86/1.18  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.86/1.18  
% 1.86/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.86/1.18  %$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_2 > #skF_3 > #skF_1
% 1.86/1.18  
% 1.86/1.18  %Foreground sorts:
% 1.86/1.18  
% 1.86/1.18  
% 1.86/1.18  %Background operators:
% 1.86/1.18  
% 1.86/1.18  
% 1.86/1.18  %Foreground operators:
% 1.86/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.86/1.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.86/1.18  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.86/1.18  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.86/1.18  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.86/1.18  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.86/1.18  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.86/1.18  tff('#skF_2', type, '#skF_2': $i).
% 1.86/1.18  tff('#skF_3', type, '#skF_3': $i).
% 1.86/1.18  tff('#skF_1', type, '#skF_1': $i).
% 1.86/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.86/1.18  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 1.86/1.18  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.86/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.86/1.18  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 1.86/1.18  
% 1.86/1.19  tff(f_54, negated_conjecture, ~(![A, B, C]: (r2_hidden(A, k2_zfmisc_1(k1_tarski(B), k1_tarski(C))) => ((k1_mcart_1(A) = B) & (k2_mcart_1(A) = C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_mcart_1)).
% 1.86/1.19  tff(f_47, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 1.86/1.19  tff(f_36, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 1.86/1.19  tff(f_41, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 1.86/1.19  tff(c_20, plain, (k2_mcart_1('#skF_1')!='#skF_3' | k1_mcart_1('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.86/1.19  tff(c_32, plain, (k1_mcart_1('#skF_1')!='#skF_2'), inference(splitLeft, [status(thm)], [c_20])).
% 1.86/1.19  tff(c_22, plain, (r2_hidden('#skF_1', k2_zfmisc_1(k1_tarski('#skF_2'), k1_tarski('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.86/1.19  tff(c_121, plain, (![A_33, B_34, C_35]: (r2_hidden(k1_mcart_1(A_33), B_34) | ~r2_hidden(A_33, k2_zfmisc_1(B_34, C_35)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.86/1.19  tff(c_124, plain, (r2_hidden(k1_mcart_1('#skF_1'), k1_tarski('#skF_2'))), inference(resolution, [status(thm)], [c_22, c_121])).
% 1.86/1.19  tff(c_64, plain, (![A_23, B_24]: (k4_xboole_0(k1_tarski(A_23), k1_tarski(B_24))=k1_tarski(A_23) | B_24=A_23)), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.86/1.19  tff(c_12, plain, (![B_10, A_9]: (~r2_hidden(B_10, A_9) | k4_xboole_0(A_9, k1_tarski(B_10))!=A_9)), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.86/1.19  tff(c_87, plain, (![B_24, A_23]: (~r2_hidden(B_24, k1_tarski(A_23)) | B_24=A_23)), inference(superposition, [status(thm), theory('equality')], [c_64, c_12])).
% 1.86/1.19  tff(c_127, plain, (k1_mcart_1('#skF_1')='#skF_2'), inference(resolution, [status(thm)], [c_124, c_87])).
% 1.86/1.19  tff(c_131, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_127])).
% 1.86/1.19  tff(c_132, plain, (k2_mcart_1('#skF_1')!='#skF_3'), inference(splitRight, [status(thm)], [c_20])).
% 1.86/1.19  tff(c_217, plain, (![A_54, C_55, B_56]: (r2_hidden(k2_mcart_1(A_54), C_55) | ~r2_hidden(A_54, k2_zfmisc_1(B_56, C_55)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.86/1.19  tff(c_220, plain, (r2_hidden(k2_mcart_1('#skF_1'), k1_tarski('#skF_3'))), inference(resolution, [status(thm)], [c_22, c_217])).
% 1.86/1.19  tff(c_183, plain, (![A_50, B_51]: (k4_xboole_0(k1_tarski(A_50), k1_tarski(B_51))=k1_tarski(A_50) | B_51=A_50)), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.86/1.19  tff(c_205, plain, (![B_51, A_50]: (~r2_hidden(B_51, k1_tarski(A_50)) | B_51=A_50)), inference(superposition, [status(thm), theory('equality')], [c_183, c_12])).
% 1.86/1.19  tff(c_223, plain, (k2_mcart_1('#skF_1')='#skF_3'), inference(resolution, [status(thm)], [c_220, c_205])).
% 1.86/1.19  tff(c_227, plain, $false, inference(negUnitSimplification, [status(thm)], [c_132, c_223])).
% 1.86/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.86/1.19  
% 1.86/1.19  Inference rules
% 1.86/1.19  ----------------------
% 1.86/1.19  #Ref     : 0
% 1.86/1.19  #Sup     : 43
% 1.86/1.19  #Fact    : 0
% 1.86/1.19  #Define  : 0
% 1.86/1.19  #Split   : 1
% 1.86/1.19  #Chain   : 0
% 1.86/1.19  #Close   : 0
% 1.86/1.19  
% 1.86/1.19  Ordering : KBO
% 1.86/1.19  
% 1.86/1.19  Simplification rules
% 1.86/1.19  ----------------------
% 1.86/1.19  #Subsume      : 0
% 1.86/1.19  #Demod        : 4
% 1.86/1.19  #Tautology    : 34
% 1.86/1.19  #SimpNegUnit  : 2
% 1.86/1.19  #BackRed      : 1
% 1.86/1.19  
% 1.86/1.19  #Partial instantiations: 0
% 1.86/1.19  #Strategies tried      : 1
% 1.86/1.19  
% 1.86/1.19  Timing (in seconds)
% 1.86/1.19  ----------------------
% 1.86/1.19  Preprocessing        : 0.28
% 1.86/1.19  Parsing              : 0.15
% 1.86/1.19  CNF conversion       : 0.02
% 1.86/1.19  Main loop            : 0.15
% 1.86/1.19  Inferencing          : 0.06
% 1.86/1.19  Reduction            : 0.04
% 1.86/1.19  Demodulation         : 0.03
% 1.86/1.19  BG Simplification    : 0.01
% 1.86/1.19  Subsumption          : 0.02
% 1.86/1.19  Abstraction          : 0.01
% 1.86/1.19  MUC search           : 0.00
% 1.86/1.19  Cooper               : 0.00
% 1.86/1.19  Total                : 0.45
% 1.86/1.19  Index Insertion      : 0.00
% 1.86/1.19  Index Deletion       : 0.00
% 1.86/1.19  Index Matching       : 0.00
% 1.86/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
