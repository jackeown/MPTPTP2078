%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:07 EST 2020

% Result     : Theorem 1.77s
% Output     : CNFRefutation 1.77s
% Verified   : 
% Statistics : Number of formulae       :   38 (  46 expanded)
%              Number of leaves         :   21 (  26 expanded)
%              Depth                    :    4
%              Number of atoms          :   41 (  66 expanded)
%              Number of equality atoms :   25 (  44 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(f_64,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r2_hidden(A,k2_zfmisc_1(k1_tarski(B),k2_tarski(C,D)))
       => ( k1_mcart_1(A) = B
          & ( k2_mcart_1(A) = C
            | k2_mcart_1(A) = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_mcart_1)).

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

tff(f_55,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(A,k2_zfmisc_1(B,k2_tarski(C,D)))
     => ( r2_hidden(k1_mcart_1(A),B)
        & ( k2_mcart_1(A) = C
          | k2_mcart_1(A) = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_mcart_1)).

tff(c_26,plain,
    ( k2_mcart_1('#skF_1') != '#skF_4'
    | k1_mcart_1('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_38,plain,(
    k1_mcart_1('#skF_1') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_24,plain,(
    r2_hidden('#skF_1',k2_zfmisc_1(k1_tarski('#skF_2'),k2_tarski('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_69,plain,(
    ! [A_27,B_28,C_29] :
      ( r2_hidden(k1_mcart_1(A_27),B_28)
      | ~ r2_hidden(A_27,k2_zfmisc_1(B_28,C_29)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_72,plain,(
    r2_hidden(k1_mcart_1('#skF_1'),k1_tarski('#skF_2')) ),
    inference(resolution,[status(thm)],[c_24,c_69])).

tff(c_87,plain,(
    ! [A_36,B_37] :
      ( k4_xboole_0(k1_tarski(A_36),k1_tarski(B_37)) = k1_tarski(A_36)
      | B_37 = A_36 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_12,plain,(
    ! [B_10,A_9] :
      ( ~ r2_hidden(B_10,A_9)
      | k4_xboole_0(A_9,k1_tarski(B_10)) != A_9 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_115,plain,(
    ! [B_38,A_39] :
      ( ~ r2_hidden(B_38,k1_tarski(A_39))
      | B_38 = A_39 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_12])).

tff(c_118,plain,(
    k1_mcart_1('#skF_1') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_72,c_115])).

tff(c_125,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_118])).

tff(c_127,plain,(
    k1_mcart_1('#skF_1') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_28,plain,
    ( k2_mcart_1('#skF_1') != '#skF_3'
    | k1_mcart_1('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_133,plain,(
    k2_mcart_1('#skF_1') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_28])).

tff(c_126,plain,(
    k2_mcart_1('#skF_1') != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_217,plain,(
    ! [A_61,D_62,C_63,B_64] :
      ( k2_mcart_1(A_61) = D_62
      | k2_mcart_1(A_61) = C_63
      | ~ r2_hidden(A_61,k2_zfmisc_1(B_64,k2_tarski(C_63,D_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_220,plain,
    ( k2_mcart_1('#skF_1') = '#skF_4'
    | k2_mcart_1('#skF_1') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_24,c_217])).

tff(c_227,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_133,c_126,c_220])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:07:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.77/1.25  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.77/1.25  
% 1.77/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.77/1.25  %$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.77/1.25  
% 1.77/1.25  %Foreground sorts:
% 1.77/1.25  
% 1.77/1.25  
% 1.77/1.25  %Background operators:
% 1.77/1.25  
% 1.77/1.25  
% 1.77/1.25  %Foreground operators:
% 1.77/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.77/1.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.77/1.25  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.77/1.25  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.77/1.25  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.77/1.25  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.77/1.25  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.77/1.25  tff('#skF_2', type, '#skF_2': $i).
% 1.77/1.25  tff('#skF_3', type, '#skF_3': $i).
% 1.77/1.25  tff('#skF_1', type, '#skF_1': $i).
% 1.77/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.77/1.25  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 1.77/1.25  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.77/1.25  tff('#skF_4', type, '#skF_4': $i).
% 1.77/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.77/1.25  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 1.77/1.25  
% 1.77/1.26  tff(f_64, negated_conjecture, ~(![A, B, C, D]: (r2_hidden(A, k2_zfmisc_1(k1_tarski(B), k2_tarski(C, D))) => ((k1_mcart_1(A) = B) & ((k2_mcart_1(A) = C) | (k2_mcart_1(A) = D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_mcart_1)).
% 1.77/1.26  tff(f_47, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 1.77/1.26  tff(f_36, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 1.77/1.26  tff(f_41, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 1.77/1.26  tff(f_55, axiom, (![A, B, C, D]: (r2_hidden(A, k2_zfmisc_1(B, k2_tarski(C, D))) => (r2_hidden(k1_mcart_1(A), B) & ((k2_mcart_1(A) = C) | (k2_mcart_1(A) = D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_mcart_1)).
% 1.77/1.26  tff(c_26, plain, (k2_mcart_1('#skF_1')!='#skF_4' | k1_mcart_1('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.77/1.26  tff(c_38, plain, (k1_mcart_1('#skF_1')!='#skF_2'), inference(splitLeft, [status(thm)], [c_26])).
% 1.77/1.26  tff(c_24, plain, (r2_hidden('#skF_1', k2_zfmisc_1(k1_tarski('#skF_2'), k2_tarski('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.77/1.26  tff(c_69, plain, (![A_27, B_28, C_29]: (r2_hidden(k1_mcart_1(A_27), B_28) | ~r2_hidden(A_27, k2_zfmisc_1(B_28, C_29)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.77/1.26  tff(c_72, plain, (r2_hidden(k1_mcart_1('#skF_1'), k1_tarski('#skF_2'))), inference(resolution, [status(thm)], [c_24, c_69])).
% 1.77/1.26  tff(c_87, plain, (![A_36, B_37]: (k4_xboole_0(k1_tarski(A_36), k1_tarski(B_37))=k1_tarski(A_36) | B_37=A_36)), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.77/1.26  tff(c_12, plain, (![B_10, A_9]: (~r2_hidden(B_10, A_9) | k4_xboole_0(A_9, k1_tarski(B_10))!=A_9)), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.77/1.26  tff(c_115, plain, (![B_38, A_39]: (~r2_hidden(B_38, k1_tarski(A_39)) | B_38=A_39)), inference(superposition, [status(thm), theory('equality')], [c_87, c_12])).
% 1.77/1.26  tff(c_118, plain, (k1_mcart_1('#skF_1')='#skF_2'), inference(resolution, [status(thm)], [c_72, c_115])).
% 1.77/1.26  tff(c_125, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_118])).
% 1.77/1.26  tff(c_127, plain, (k1_mcart_1('#skF_1')='#skF_2'), inference(splitRight, [status(thm)], [c_26])).
% 1.77/1.26  tff(c_28, plain, (k2_mcart_1('#skF_1')!='#skF_3' | k1_mcart_1('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.77/1.26  tff(c_133, plain, (k2_mcart_1('#skF_1')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_127, c_28])).
% 1.77/1.26  tff(c_126, plain, (k2_mcart_1('#skF_1')!='#skF_4'), inference(splitRight, [status(thm)], [c_26])).
% 1.77/1.26  tff(c_217, plain, (![A_61, D_62, C_63, B_64]: (k2_mcart_1(A_61)=D_62 | k2_mcart_1(A_61)=C_63 | ~r2_hidden(A_61, k2_zfmisc_1(B_64, k2_tarski(C_63, D_62))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.77/1.26  tff(c_220, plain, (k2_mcart_1('#skF_1')='#skF_4' | k2_mcart_1('#skF_1')='#skF_3'), inference(resolution, [status(thm)], [c_24, c_217])).
% 1.77/1.26  tff(c_227, plain, $false, inference(negUnitSimplification, [status(thm)], [c_133, c_126, c_220])).
% 1.77/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.77/1.26  
% 1.77/1.26  Inference rules
% 1.77/1.26  ----------------------
% 1.77/1.26  #Ref     : 0
% 1.77/1.26  #Sup     : 41
% 1.77/1.26  #Fact    : 0
% 1.77/1.26  #Define  : 0
% 1.77/1.26  #Split   : 1
% 1.77/1.26  #Chain   : 0
% 1.77/1.26  #Close   : 0
% 1.77/1.26  
% 1.77/1.26  Ordering : KBO
% 1.77/1.26  
% 1.77/1.26  Simplification rules
% 1.77/1.26  ----------------------
% 1.77/1.26  #Subsume      : 2
% 1.77/1.26  #Demod        : 3
% 1.77/1.26  #Tautology    : 30
% 1.77/1.26  #SimpNegUnit  : 2
% 1.77/1.26  #BackRed      : 0
% 1.77/1.26  
% 1.77/1.26  #Partial instantiations: 0
% 1.77/1.26  #Strategies tried      : 1
% 1.77/1.26  
% 1.77/1.26  Timing (in seconds)
% 1.77/1.26  ----------------------
% 1.77/1.27  Preprocessing        : 0.30
% 1.77/1.27  Parsing              : 0.17
% 1.77/1.27  CNF conversion       : 0.02
% 1.77/1.27  Main loop            : 0.14
% 1.77/1.27  Inferencing          : 0.06
% 1.77/1.27  Reduction            : 0.04
% 1.77/1.27  Demodulation         : 0.02
% 1.77/1.27  BG Simplification    : 0.01
% 1.77/1.27  Subsumption          : 0.02
% 1.77/1.27  Abstraction          : 0.01
% 1.77/1.27  MUC search           : 0.00
% 1.77/1.27  Cooper               : 0.00
% 1.77/1.27  Total                : 0.47
% 1.77/1.27  Index Insertion      : 0.00
% 1.77/1.27  Index Deletion       : 0.00
% 1.77/1.27  Index Matching       : 0.00
% 1.77/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
