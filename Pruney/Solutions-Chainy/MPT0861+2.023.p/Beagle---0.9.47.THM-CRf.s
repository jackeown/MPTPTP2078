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
% DateTime   : Thu Dec  3 10:09:04 EST 2020

% Result     : Theorem 1.90s
% Output     : CNFRefutation 1.90s
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
        ( r2_hidden(A,k2_zfmisc_1(k2_tarski(B,C),k1_tarski(D)))
       => ( ( k1_mcart_1(A) = B
            | k1_mcart_1(A) = C )
          & k2_mcart_1(A) = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_mcart_1)).

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
      ( r2_hidden(A,k2_zfmisc_1(k2_tarski(B,C),D))
     => ( ( k1_mcart_1(A) = B
          | k1_mcart_1(A) = C )
        & r2_hidden(k2_mcart_1(A),D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_mcart_1)).

tff(c_26,plain,
    ( k1_mcart_1('#skF_1') != '#skF_3'
    | k2_mcart_1('#skF_1') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_38,plain,(
    k2_mcart_1('#skF_1') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_24,plain,(
    r2_hidden('#skF_1',k2_zfmisc_1(k2_tarski('#skF_2','#skF_3'),k1_tarski('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_73,plain,(
    ! [A_30,C_31,B_32] :
      ( r2_hidden(k2_mcart_1(A_30),C_31)
      | ~ r2_hidden(A_30,k2_zfmisc_1(B_32,C_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_76,plain,(
    r2_hidden(k2_mcart_1('#skF_1'),k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_24,c_73])).

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
    k2_mcart_1('#skF_1') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_76,c_115])).

tff(c_125,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_118])).

tff(c_127,plain,(
    k2_mcart_1('#skF_1') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_28,plain,
    ( k1_mcart_1('#skF_1') != '#skF_2'
    | k2_mcart_1('#skF_1') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_133,plain,(
    k1_mcart_1('#skF_1') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_28])).

tff(c_126,plain,(
    k1_mcart_1('#skF_1') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_217,plain,(
    ! [A_61,C_62,B_63,D_64] :
      ( k1_mcart_1(A_61) = C_62
      | k1_mcart_1(A_61) = B_63
      | ~ r2_hidden(A_61,k2_zfmisc_1(k2_tarski(B_63,C_62),D_64)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_220,plain,
    ( k1_mcart_1('#skF_1') = '#skF_3'
    | k1_mcart_1('#skF_1') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_24,c_217])).

tff(c_227,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_133,c_126,c_220])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:36:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.90/1.17  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.90/1.17  
% 1.90/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.90/1.17  %$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.90/1.17  
% 1.90/1.17  %Foreground sorts:
% 1.90/1.17  
% 1.90/1.17  
% 1.90/1.17  %Background operators:
% 1.90/1.17  
% 1.90/1.17  
% 1.90/1.17  %Foreground operators:
% 1.90/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.90/1.17  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.90/1.17  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.90/1.17  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.90/1.17  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.90/1.17  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.90/1.17  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.90/1.17  tff('#skF_2', type, '#skF_2': $i).
% 1.90/1.17  tff('#skF_3', type, '#skF_3': $i).
% 1.90/1.17  tff('#skF_1', type, '#skF_1': $i).
% 1.90/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.90/1.17  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 1.90/1.17  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.90/1.17  tff('#skF_4', type, '#skF_4': $i).
% 1.90/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.90/1.17  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 1.90/1.17  
% 1.90/1.18  tff(f_64, negated_conjecture, ~(![A, B, C, D]: (r2_hidden(A, k2_zfmisc_1(k2_tarski(B, C), k1_tarski(D))) => (((k1_mcart_1(A) = B) | (k1_mcart_1(A) = C)) & (k2_mcart_1(A) = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_mcart_1)).
% 1.90/1.18  tff(f_47, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 1.90/1.18  tff(f_36, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 1.90/1.18  tff(f_41, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 1.90/1.18  tff(f_55, axiom, (![A, B, C, D]: (r2_hidden(A, k2_zfmisc_1(k2_tarski(B, C), D)) => (((k1_mcart_1(A) = B) | (k1_mcart_1(A) = C)) & r2_hidden(k2_mcart_1(A), D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_mcart_1)).
% 1.90/1.18  tff(c_26, plain, (k1_mcart_1('#skF_1')!='#skF_3' | k2_mcart_1('#skF_1')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.90/1.18  tff(c_38, plain, (k2_mcart_1('#skF_1')!='#skF_4'), inference(splitLeft, [status(thm)], [c_26])).
% 1.90/1.18  tff(c_24, plain, (r2_hidden('#skF_1', k2_zfmisc_1(k2_tarski('#skF_2', '#skF_3'), k1_tarski('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.90/1.18  tff(c_73, plain, (![A_30, C_31, B_32]: (r2_hidden(k2_mcart_1(A_30), C_31) | ~r2_hidden(A_30, k2_zfmisc_1(B_32, C_31)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.90/1.18  tff(c_76, plain, (r2_hidden(k2_mcart_1('#skF_1'), k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_24, c_73])).
% 1.90/1.18  tff(c_87, plain, (![A_36, B_37]: (k4_xboole_0(k1_tarski(A_36), k1_tarski(B_37))=k1_tarski(A_36) | B_37=A_36)), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.90/1.18  tff(c_12, plain, (![B_10, A_9]: (~r2_hidden(B_10, A_9) | k4_xboole_0(A_9, k1_tarski(B_10))!=A_9)), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.90/1.18  tff(c_115, plain, (![B_38, A_39]: (~r2_hidden(B_38, k1_tarski(A_39)) | B_38=A_39)), inference(superposition, [status(thm), theory('equality')], [c_87, c_12])).
% 1.90/1.18  tff(c_118, plain, (k2_mcart_1('#skF_1')='#skF_4'), inference(resolution, [status(thm)], [c_76, c_115])).
% 1.90/1.18  tff(c_125, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_118])).
% 1.90/1.18  tff(c_127, plain, (k2_mcart_1('#skF_1')='#skF_4'), inference(splitRight, [status(thm)], [c_26])).
% 1.90/1.18  tff(c_28, plain, (k1_mcart_1('#skF_1')!='#skF_2' | k2_mcart_1('#skF_1')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.90/1.18  tff(c_133, plain, (k1_mcart_1('#skF_1')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_127, c_28])).
% 1.90/1.18  tff(c_126, plain, (k1_mcart_1('#skF_1')!='#skF_3'), inference(splitRight, [status(thm)], [c_26])).
% 1.90/1.18  tff(c_217, plain, (![A_61, C_62, B_63, D_64]: (k1_mcart_1(A_61)=C_62 | k1_mcart_1(A_61)=B_63 | ~r2_hidden(A_61, k2_zfmisc_1(k2_tarski(B_63, C_62), D_64)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.90/1.18  tff(c_220, plain, (k1_mcart_1('#skF_1')='#skF_3' | k1_mcart_1('#skF_1')='#skF_2'), inference(resolution, [status(thm)], [c_24, c_217])).
% 1.90/1.18  tff(c_227, plain, $false, inference(negUnitSimplification, [status(thm)], [c_133, c_126, c_220])).
% 1.90/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.90/1.18  
% 1.90/1.18  Inference rules
% 1.90/1.18  ----------------------
% 1.90/1.18  #Ref     : 0
% 1.90/1.18  #Sup     : 41
% 1.90/1.18  #Fact    : 0
% 1.90/1.18  #Define  : 0
% 1.90/1.18  #Split   : 1
% 1.90/1.18  #Chain   : 0
% 1.90/1.18  #Close   : 0
% 1.90/1.18  
% 1.90/1.18  Ordering : KBO
% 1.90/1.18  
% 1.90/1.18  Simplification rules
% 1.90/1.18  ----------------------
% 1.90/1.18  #Subsume      : 2
% 1.90/1.18  #Demod        : 3
% 1.90/1.18  #Tautology    : 30
% 1.90/1.18  #SimpNegUnit  : 2
% 1.90/1.18  #BackRed      : 0
% 1.90/1.18  
% 1.90/1.18  #Partial instantiations: 0
% 1.90/1.18  #Strategies tried      : 1
% 1.90/1.18  
% 1.90/1.18  Timing (in seconds)
% 1.90/1.18  ----------------------
% 1.90/1.19  Preprocessing        : 0.28
% 1.90/1.19  Parsing              : 0.15
% 1.90/1.19  CNF conversion       : 0.02
% 1.90/1.19  Main loop            : 0.15
% 1.90/1.19  Inferencing          : 0.06
% 1.90/1.19  Reduction            : 0.04
% 1.90/1.19  Demodulation         : 0.03
% 1.90/1.19  BG Simplification    : 0.01
% 1.90/1.19  Subsumption          : 0.02
% 1.90/1.19  Abstraction          : 0.01
% 1.90/1.19  MUC search           : 0.00
% 1.90/1.19  Cooper               : 0.00
% 1.90/1.19  Total                : 0.45
% 1.90/1.19  Index Insertion      : 0.00
% 1.90/1.19  Index Deletion       : 0.00
% 1.90/1.19  Index Matching       : 0.00
% 1.90/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
