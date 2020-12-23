%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:38 EST 2020

% Result     : Theorem 1.62s
% Output     : CNFRefutation 1.62s
% Verified   : 
% Statistics : Number of formulae       :   39 (  60 expanded)
%              Number of leaves         :   15 (  27 expanded)
%              Depth                    :    4
%              Number of atoms          :   41 (  80 expanded)
%              Number of equality atoms :   30 (  65 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k2_enumset1 > k4_xboole_0 > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),k1_tarski(B))
        & A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_zfmisc_1)).

tff(f_47,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
      <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( A != B
     => r1_xboole_0(k1_tarski(A),k1_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_zfmisc_1)).

tff(c_129,plain,(
    ! [A_22,B_23] :
      ( r1_xboole_0(A_22,B_23)
      | k4_xboole_0(A_22,B_23) != A_22 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_8,plain,(
    ! [B_5] : ~ r1_xboole_0(k1_tarski(B_5),k1_tarski(B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_133,plain,(
    ! [B_5] : k4_xboole_0(k1_tarski(B_5),k1_tarski(B_5)) != k1_tarski(B_5) ),
    inference(resolution,[status(thm)],[c_129,c_8])).

tff(c_21,plain,(
    ! [A_9,B_10] :
      ( r1_xboole_0(A_9,B_10)
      | k4_xboole_0(A_9,B_10) != A_9 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_25,plain,(
    ! [B_5] : k4_xboole_0(k1_tarski(B_5),k1_tarski(B_5)) != k1_tarski(B_5) ),
    inference(resolution,[status(thm)],[c_21,c_8])).

tff(c_14,plain,
    ( '#skF_2' != '#skF_1'
    | '#skF_3' = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_19,plain,(
    '#skF_2' != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_14])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( r1_xboole_0(k1_tarski(A_6),k1_tarski(B_7))
      | B_7 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_42,plain,(
    ! [A_14,B_15] :
      ( k4_xboole_0(A_14,B_15) = A_14
      | ~ r1_xboole_0(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_54,plain,(
    ! [A_17,B_18] :
      ( k4_xboole_0(k1_tarski(A_17),k1_tarski(B_18)) = k1_tarski(A_17)
      | B_18 = A_17 ) ),
    inference(resolution,[status(thm)],[c_10,c_42])).

tff(c_12,plain,
    ( k4_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2')) != k1_tarski('#skF_1')
    | '#skF_3' = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_52,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2')) != k1_tarski('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_12])).

tff(c_60,plain,(
    '#skF_2' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_52])).

tff(c_72,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_19,c_60])).

tff(c_73,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_12])).

tff(c_74,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2')) = k1_tarski('#skF_1') ),
    inference(splitRight,[status(thm)],[c_12])).

tff(c_16,plain,
    ( k4_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2')) != k1_tarski('#skF_1')
    | k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) = k1_tarski('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_110,plain,(
    k4_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_4')) = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_73,c_74,c_16])).

tff(c_111,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_25,c_110])).

tff(c_112,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_14])).

tff(c_113,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_14])).

tff(c_18,plain,
    ( '#skF_2' != '#skF_1'
    | k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) = k1_tarski('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_124,plain,(
    k4_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_4')) = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_112,c_113,c_18])).

tff(c_160,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_133,c_124])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:59:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.62/1.05  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.62/1.05  
% 1.62/1.05  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.62/1.05  %$ r1_xboole_0 > k2_enumset1 > k4_xboole_0 > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.62/1.05  
% 1.62/1.05  %Foreground sorts:
% 1.62/1.05  
% 1.62/1.05  
% 1.62/1.05  %Background operators:
% 1.62/1.05  
% 1.62/1.05  
% 1.62/1.05  %Foreground operators:
% 1.62/1.05  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.62/1.05  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.62/1.05  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.62/1.05  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.62/1.05  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.62/1.05  tff('#skF_2', type, '#skF_2': $i).
% 1.62/1.05  tff('#skF_3', type, '#skF_3': $i).
% 1.62/1.05  tff('#skF_1', type, '#skF_1': $i).
% 1.62/1.05  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.62/1.05  tff('#skF_4', type, '#skF_4': $i).
% 1.62/1.05  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.62/1.05  
% 1.62/1.06  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 1.62/1.06  tff(f_36, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), k1_tarski(B)) & (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_zfmisc_1)).
% 1.62/1.06  tff(f_47, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 1.62/1.06  tff(f_41, axiom, (![A, B]: (~(A = B) => r1_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_zfmisc_1)).
% 1.62/1.06  tff(c_129, plain, (![A_22, B_23]: (r1_xboole_0(A_22, B_23) | k4_xboole_0(A_22, B_23)!=A_22)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.62/1.06  tff(c_8, plain, (![B_5]: (~r1_xboole_0(k1_tarski(B_5), k1_tarski(B_5)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.62/1.06  tff(c_133, plain, (![B_5]: (k4_xboole_0(k1_tarski(B_5), k1_tarski(B_5))!=k1_tarski(B_5))), inference(resolution, [status(thm)], [c_129, c_8])).
% 1.62/1.06  tff(c_21, plain, (![A_9, B_10]: (r1_xboole_0(A_9, B_10) | k4_xboole_0(A_9, B_10)!=A_9)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.62/1.06  tff(c_25, plain, (![B_5]: (k4_xboole_0(k1_tarski(B_5), k1_tarski(B_5))!=k1_tarski(B_5))), inference(resolution, [status(thm)], [c_21, c_8])).
% 1.62/1.06  tff(c_14, plain, ('#skF_2'!='#skF_1' | '#skF_3'='#skF_4'), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.62/1.06  tff(c_19, plain, ('#skF_2'!='#skF_1'), inference(splitLeft, [status(thm)], [c_14])).
% 1.62/1.06  tff(c_10, plain, (![A_6, B_7]: (r1_xboole_0(k1_tarski(A_6), k1_tarski(B_7)) | B_7=A_6)), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.62/1.06  tff(c_42, plain, (![A_14, B_15]: (k4_xboole_0(A_14, B_15)=A_14 | ~r1_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.62/1.06  tff(c_54, plain, (![A_17, B_18]: (k4_xboole_0(k1_tarski(A_17), k1_tarski(B_18))=k1_tarski(A_17) | B_18=A_17)), inference(resolution, [status(thm)], [c_10, c_42])).
% 1.62/1.06  tff(c_12, plain, (k4_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2'))!=k1_tarski('#skF_1') | '#skF_3'='#skF_4'), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.62/1.06  tff(c_52, plain, (k4_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2'))!=k1_tarski('#skF_1')), inference(splitLeft, [status(thm)], [c_12])).
% 1.62/1.06  tff(c_60, plain, ('#skF_2'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_54, c_52])).
% 1.62/1.06  tff(c_72, plain, $false, inference(negUnitSimplification, [status(thm)], [c_19, c_60])).
% 1.62/1.06  tff(c_73, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_12])).
% 1.62/1.06  tff(c_74, plain, (k4_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2'))=k1_tarski('#skF_1')), inference(splitRight, [status(thm)], [c_12])).
% 1.62/1.06  tff(c_16, plain, (k4_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2'))!=k1_tarski('#skF_1') | k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))=k1_tarski('#skF_3')), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.62/1.06  tff(c_110, plain, (k4_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_4'))=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_73, c_73, c_74, c_16])).
% 1.62/1.06  tff(c_111, plain, $false, inference(negUnitSimplification, [status(thm)], [c_25, c_110])).
% 1.62/1.06  tff(c_112, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_14])).
% 1.62/1.06  tff(c_113, plain, ('#skF_2'='#skF_1'), inference(splitRight, [status(thm)], [c_14])).
% 1.62/1.06  tff(c_18, plain, ('#skF_2'!='#skF_1' | k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))=k1_tarski('#skF_3')), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.62/1.06  tff(c_124, plain, (k4_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_4'))=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_112, c_112, c_113, c_18])).
% 1.62/1.06  tff(c_160, plain, $false, inference(negUnitSimplification, [status(thm)], [c_133, c_124])).
% 1.62/1.06  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.62/1.06  
% 1.62/1.06  Inference rules
% 1.62/1.06  ----------------------
% 1.62/1.06  #Ref     : 0
% 1.62/1.06  #Sup     : 31
% 1.62/1.06  #Fact    : 0
% 1.62/1.06  #Define  : 0
% 1.62/1.06  #Split   : 2
% 1.62/1.06  #Chain   : 0
% 1.62/1.06  #Close   : 0
% 1.62/1.06  
% 1.62/1.06  Ordering : KBO
% 1.62/1.06  
% 1.62/1.06  Simplification rules
% 1.62/1.06  ----------------------
% 1.62/1.06  #Subsume      : 1
% 1.62/1.06  #Demod        : 6
% 1.62/1.06  #Tautology    : 24
% 1.62/1.06  #SimpNegUnit  : 5
% 1.62/1.06  #BackRed      : 1
% 1.62/1.06  
% 1.62/1.06  #Partial instantiations: 0
% 1.62/1.06  #Strategies tried      : 1
% 1.62/1.06  
% 1.62/1.06  Timing (in seconds)
% 1.62/1.06  ----------------------
% 1.62/1.07  Preprocessing        : 0.25
% 1.62/1.07  Parsing              : 0.13
% 1.62/1.07  CNF conversion       : 0.02
% 1.62/1.07  Main loop            : 0.11
% 1.62/1.07  Inferencing          : 0.05
% 1.62/1.07  Reduction            : 0.03
% 1.62/1.07  Demodulation         : 0.02
% 1.62/1.07  BG Simplification    : 0.01
% 1.62/1.07  Subsumption          : 0.02
% 1.62/1.07  Abstraction          : 0.01
% 1.62/1.07  MUC search           : 0.00
% 1.62/1.07  Cooper               : 0.00
% 1.62/1.07  Total                : 0.39
% 1.62/1.07  Index Insertion      : 0.00
% 1.62/1.07  Index Deletion       : 0.00
% 1.62/1.07  Index Matching       : 0.00
% 1.62/1.07  BG Taut test         : 0.00
%------------------------------------------------------------------------------
