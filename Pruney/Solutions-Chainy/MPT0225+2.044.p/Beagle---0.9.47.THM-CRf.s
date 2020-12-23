%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:36 EST 2020

% Result     : Theorem 1.74s
% Output     : CNFRefutation 1.74s
% Verified   : 
% Statistics : Number of formulae       :   42 (  64 expanded)
%              Number of leaves         :   18 (  31 expanded)
%              Depth                    :    5
%              Number of atoms          :   39 (  82 expanded)
%              Number of equality atoms :   26 (  64 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_49,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
      <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_tarski(A)
    <=> ~ r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l33_zfmisc_1)).

tff(c_4,plain,(
    ! [C_5] : r2_hidden(C_5,k1_tarski(C_5)) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_26,plain,
    ( '#skF_3' != '#skF_4'
    | '#skF_5' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_31,plain,(
    '#skF_3' != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_22,plain,(
    ! [A_12,B_13] :
      ( k4_xboole_0(k1_tarski(A_12),B_13) = k1_tarski(A_12)
      | r2_hidden(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_24,plain,
    ( k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) != k1_tarski('#skF_3')
    | '#skF_5' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_66,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) != k1_tarski('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_71,plain,(
    r2_hidden('#skF_3',k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_66])).

tff(c_2,plain,(
    ! [C_5,A_1] :
      ( C_5 = A_1
      | ~ r2_hidden(C_5,k1_tarski(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_74,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_71,c_2])).

tff(c_78,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_31,c_74])).

tff(c_79,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_80,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) = k1_tarski('#skF_3') ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_28,plain,
    ( k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) != k1_tarski('#skF_3')
    | k4_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) = k1_tarski('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_118,plain,(
    k4_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_6')) = k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_79,c_80,c_28])).

tff(c_20,plain,(
    ! [A_12,B_13] :
      ( ~ r2_hidden(A_12,B_13)
      | k4_xboole_0(k1_tarski(A_12),B_13) != k1_tarski(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_122,plain,(
    ~ r2_hidden('#skF_6',k1_tarski('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_118,c_20])).

tff(c_134,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_122])).

tff(c_135,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_136,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_30,plain,
    ( '#skF_3' != '#skF_4'
    | k4_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) = k1_tarski('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_171,plain,(
    k4_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_6')) = k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_135,c_136,c_30])).

tff(c_206,plain,(
    ! [A_42,B_43] :
      ( ~ r2_hidden(A_42,B_43)
      | k4_xboole_0(k1_tarski(A_42),B_43) != k1_tarski(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_212,plain,(
    ~ r2_hidden('#skF_6',k1_tarski('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_171,c_206])).

tff(c_217,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_212])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:27:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.74/1.15  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.74/1.16  
% 1.74/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.74/1.16  %$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 1.74/1.16  
% 1.74/1.16  %Foreground sorts:
% 1.74/1.16  
% 1.74/1.16  
% 1.74/1.16  %Background operators:
% 1.74/1.16  
% 1.74/1.16  
% 1.74/1.16  %Foreground operators:
% 1.74/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.74/1.16  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.74/1.16  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.74/1.16  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.74/1.16  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.74/1.16  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.74/1.16  tff('#skF_5', type, '#skF_5': $i).
% 1.74/1.16  tff('#skF_6', type, '#skF_6': $i).
% 1.74/1.16  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.74/1.16  tff('#skF_3', type, '#skF_3': $i).
% 1.74/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.74/1.16  tff('#skF_4', type, '#skF_4': $i).
% 1.74/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.74/1.16  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.74/1.16  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.74/1.16  
% 1.74/1.17  tff(f_32, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 1.74/1.17  tff(f_49, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 1.74/1.17  tff(f_43, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)) <=> ~r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l33_zfmisc_1)).
% 1.74/1.17  tff(c_4, plain, (![C_5]: (r2_hidden(C_5, k1_tarski(C_5)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.74/1.17  tff(c_26, plain, ('#skF_3'!='#skF_4' | '#skF_5'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.74/1.17  tff(c_31, plain, ('#skF_3'!='#skF_4'), inference(splitLeft, [status(thm)], [c_26])).
% 1.74/1.17  tff(c_22, plain, (![A_12, B_13]: (k4_xboole_0(k1_tarski(A_12), B_13)=k1_tarski(A_12) | r2_hidden(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.74/1.17  tff(c_24, plain, (k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))!=k1_tarski('#skF_3') | '#skF_5'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.74/1.17  tff(c_66, plain, (k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))!=k1_tarski('#skF_3')), inference(splitLeft, [status(thm)], [c_24])).
% 1.74/1.17  tff(c_71, plain, (r2_hidden('#skF_3', k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_22, c_66])).
% 1.74/1.17  tff(c_2, plain, (![C_5, A_1]: (C_5=A_1 | ~r2_hidden(C_5, k1_tarski(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.74/1.17  tff(c_74, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_71, c_2])).
% 1.74/1.17  tff(c_78, plain, $false, inference(negUnitSimplification, [status(thm)], [c_31, c_74])).
% 1.74/1.17  tff(c_79, plain, ('#skF_5'='#skF_6'), inference(splitRight, [status(thm)], [c_24])).
% 1.74/1.17  tff(c_80, plain, (k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))=k1_tarski('#skF_3')), inference(splitRight, [status(thm)], [c_24])).
% 1.74/1.17  tff(c_28, plain, (k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))!=k1_tarski('#skF_3') | k4_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))=k1_tarski('#skF_5')), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.74/1.17  tff(c_118, plain, (k4_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_6'))=k1_tarski('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_79, c_79, c_80, c_28])).
% 1.74/1.17  tff(c_20, plain, (![A_12, B_13]: (~r2_hidden(A_12, B_13) | k4_xboole_0(k1_tarski(A_12), B_13)!=k1_tarski(A_12))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.74/1.17  tff(c_122, plain, (~r2_hidden('#skF_6', k1_tarski('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_118, c_20])).
% 1.74/1.17  tff(c_134, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4, c_122])).
% 1.74/1.17  tff(c_135, plain, ('#skF_5'='#skF_6'), inference(splitRight, [status(thm)], [c_26])).
% 1.74/1.17  tff(c_136, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_26])).
% 1.74/1.17  tff(c_30, plain, ('#skF_3'!='#skF_4' | k4_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))=k1_tarski('#skF_5')), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.74/1.17  tff(c_171, plain, (k4_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_6'))=k1_tarski('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_135, c_135, c_136, c_30])).
% 1.74/1.17  tff(c_206, plain, (![A_42, B_43]: (~r2_hidden(A_42, B_43) | k4_xboole_0(k1_tarski(A_42), B_43)!=k1_tarski(A_42))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.74/1.17  tff(c_212, plain, (~r2_hidden('#skF_6', k1_tarski('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_171, c_206])).
% 1.74/1.17  tff(c_217, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4, c_212])).
% 1.74/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.74/1.17  
% 1.74/1.17  Inference rules
% 1.74/1.17  ----------------------
% 1.74/1.17  #Ref     : 0
% 1.74/1.17  #Sup     : 43
% 1.74/1.17  #Fact    : 0
% 1.74/1.17  #Define  : 0
% 1.74/1.17  #Split   : 3
% 1.74/1.17  #Chain   : 0
% 1.74/1.17  #Close   : 0
% 1.74/1.17  
% 1.74/1.17  Ordering : KBO
% 1.74/1.17  
% 1.74/1.17  Simplification rules
% 1.74/1.17  ----------------------
% 1.74/1.17  #Subsume      : 1
% 1.74/1.17  #Demod        : 18
% 1.74/1.17  #Tautology    : 37
% 1.74/1.17  #SimpNegUnit  : 1
% 1.74/1.17  #BackRed      : 0
% 1.74/1.17  
% 1.74/1.17  #Partial instantiations: 0
% 1.74/1.17  #Strategies tried      : 1
% 1.74/1.17  
% 1.74/1.17  Timing (in seconds)
% 1.74/1.17  ----------------------
% 1.93/1.17  Preprocessing        : 0.28
% 1.93/1.17  Parsing              : 0.14
% 1.93/1.17  CNF conversion       : 0.02
% 1.93/1.17  Main loop            : 0.13
% 1.93/1.17  Inferencing          : 0.05
% 1.93/1.17  Reduction            : 0.04
% 1.93/1.17  Demodulation         : 0.02
% 1.93/1.17  BG Simplification    : 0.01
% 1.93/1.17  Subsumption          : 0.02
% 1.93/1.17  Abstraction          : 0.01
% 1.93/1.17  MUC search           : 0.00
% 1.93/1.18  Cooper               : 0.00
% 1.94/1.18  Total                : 0.44
% 1.94/1.18  Index Insertion      : 0.00
% 1.94/1.18  Index Deletion       : 0.00
% 1.94/1.18  Index Matching       : 0.00
% 1.94/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
