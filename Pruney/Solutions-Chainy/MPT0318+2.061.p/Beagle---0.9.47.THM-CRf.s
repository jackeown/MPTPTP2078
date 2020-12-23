%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:09 EST 2020

% Result     : Theorem 1.73s
% Output     : CNFRefutation 1.78s
% Verified   : 
% Statistics : Number of formulae       :   31 (  78 expanded)
%              Number of leaves         :   16 (  34 expanded)
%              Depth                    :    6
%              Number of atoms          :   29 ( 128 expanded)
%              Number of equality atoms :   27 ( 126 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_56,negated_conjecture,(
    ~ ! [A,B] :
        ( A != k1_xboole_0
       => ( k2_zfmisc_1(k1_tarski(B),A) != k1_xboole_0
          & k2_zfmisc_1(A,k1_tarski(B)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_29,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_46,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(c_24,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_22,plain,
    ( k2_zfmisc_1('#skF_1',k1_tarski('#skF_2')) = k1_xboole_0
    | k2_zfmisc_1(k1_tarski('#skF_2'),'#skF_1') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_93,plain,(
    k2_zfmisc_1(k1_tarski('#skF_2'),'#skF_1') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_22])).

tff(c_12,plain,(
    ! [B_9,A_8] :
      ( k1_xboole_0 = B_9
      | k1_xboole_0 = A_8
      | k2_zfmisc_1(A_8,B_9) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_97,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_tarski('#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_12])).

tff(c_102,plain,(
    k1_tarski('#skF_2') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_97])).

tff(c_4,plain,(
    ! [A_2] : k4_xboole_0(A_2,k1_xboole_0) = A_2 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_18,plain,(
    ! [B_11] : k4_xboole_0(k1_tarski(B_11),k1_tarski(B_11)) != k1_tarski(B_11) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_109,plain,(
    k4_xboole_0(k1_xboole_0,k1_tarski('#skF_2')) != k1_tarski('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_18])).

tff(c_117,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_4,c_102,c_109])).

tff(c_118,plain,(
    k2_zfmisc_1('#skF_1',k1_tarski('#skF_2')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_123,plain,
    ( k1_tarski('#skF_2') = k1_xboole_0
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_118,c_12])).

tff(c_128,plain,(
    k1_tarski('#skF_2') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_123])).

tff(c_135,plain,(
    k4_xboole_0(k1_xboole_0,k1_tarski('#skF_2')) != k1_tarski('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_128,c_18])).

tff(c_143,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_4,c_128,c_135])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n001.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 11:04:44 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.73/1.16  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.73/1.17  
% 1.73/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.73/1.17  %$ k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 1.73/1.17  
% 1.73/1.17  %Foreground sorts:
% 1.73/1.17  
% 1.73/1.17  
% 1.73/1.17  %Background operators:
% 1.73/1.17  
% 1.73/1.17  
% 1.73/1.17  %Foreground operators:
% 1.73/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.73/1.17  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.73/1.17  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.73/1.17  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.73/1.17  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.73/1.17  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.73/1.17  tff('#skF_2', type, '#skF_2': $i).
% 1.73/1.17  tff('#skF_1', type, '#skF_1': $i).
% 1.73/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.73/1.17  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.73/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.73/1.17  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.73/1.17  
% 1.78/1.19  tff(f_56, negated_conjecture, ~(![A, B]: (~(A = k1_xboole_0) => (~(k2_zfmisc_1(k1_tarski(B), A) = k1_xboole_0) & ~(k2_zfmisc_1(A, k1_tarski(B)) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t130_zfmisc_1)).
% 1.78/1.19  tff(f_41, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.78/1.19  tff(f_29, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 1.78/1.19  tff(f_46, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 1.78/1.19  tff(c_24, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.78/1.19  tff(c_22, plain, (k2_zfmisc_1('#skF_1', k1_tarski('#skF_2'))=k1_xboole_0 | k2_zfmisc_1(k1_tarski('#skF_2'), '#skF_1')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.78/1.19  tff(c_93, plain, (k2_zfmisc_1(k1_tarski('#skF_2'), '#skF_1')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_22])).
% 1.78/1.19  tff(c_12, plain, (![B_9, A_8]: (k1_xboole_0=B_9 | k1_xboole_0=A_8 | k2_zfmisc_1(A_8, B_9)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.78/1.19  tff(c_97, plain, (k1_xboole_0='#skF_1' | k1_tarski('#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_93, c_12])).
% 1.78/1.19  tff(c_102, plain, (k1_tarski('#skF_2')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_24, c_97])).
% 1.78/1.19  tff(c_4, plain, (![A_2]: (k4_xboole_0(A_2, k1_xboole_0)=A_2)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.78/1.19  tff(c_18, plain, (![B_11]: (k4_xboole_0(k1_tarski(B_11), k1_tarski(B_11))!=k1_tarski(B_11))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.78/1.19  tff(c_109, plain, (k4_xboole_0(k1_xboole_0, k1_tarski('#skF_2'))!=k1_tarski('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_102, c_18])).
% 1.78/1.19  tff(c_117, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_102, c_4, c_102, c_109])).
% 1.78/1.19  tff(c_118, plain, (k2_zfmisc_1('#skF_1', k1_tarski('#skF_2'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_22])).
% 1.78/1.19  tff(c_123, plain, (k1_tarski('#skF_2')=k1_xboole_0 | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_118, c_12])).
% 1.78/1.19  tff(c_128, plain, (k1_tarski('#skF_2')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_24, c_123])).
% 1.78/1.19  tff(c_135, plain, (k4_xboole_0(k1_xboole_0, k1_tarski('#skF_2'))!=k1_tarski('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_128, c_18])).
% 1.78/1.19  tff(c_143, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_128, c_4, c_128, c_135])).
% 1.78/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.78/1.19  
% 1.78/1.19  Inference rules
% 1.78/1.19  ----------------------
% 1.78/1.19  #Ref     : 0
% 1.78/1.19  #Sup     : 30
% 1.78/1.19  #Fact    : 0
% 1.78/1.19  #Define  : 0
% 1.78/1.19  #Split   : 1
% 1.78/1.19  #Chain   : 0
% 1.78/1.19  #Close   : 0
% 1.78/1.19  
% 1.78/1.19  Ordering : KBO
% 1.78/1.19  
% 1.78/1.19  Simplification rules
% 1.78/1.19  ----------------------
% 1.78/1.19  #Subsume      : 0
% 1.78/1.19  #Demod        : 10
% 1.78/1.19  #Tautology    : 24
% 1.78/1.19  #SimpNegUnit  : 2
% 1.78/1.19  #BackRed      : 2
% 1.78/1.19  
% 1.78/1.19  #Partial instantiations: 0
% 1.78/1.19  #Strategies tried      : 1
% 1.78/1.19  
% 1.78/1.19  Timing (in seconds)
% 1.78/1.19  ----------------------
% 1.78/1.19  Preprocessing        : 0.27
% 1.78/1.19  Parsing              : 0.14
% 1.78/1.19  CNF conversion       : 0.02
% 1.78/1.19  Main loop            : 0.14
% 1.78/1.19  Inferencing          : 0.05
% 1.78/1.19  Reduction            : 0.05
% 1.78/1.20  Demodulation         : 0.03
% 1.78/1.20  BG Simplification    : 0.01
% 1.78/1.20  Subsumption          : 0.03
% 1.78/1.20  Abstraction          : 0.01
% 1.78/1.20  MUC search           : 0.00
% 1.78/1.20  Cooper               : 0.00
% 1.78/1.20  Total                : 0.45
% 1.78/1.20  Index Insertion      : 0.00
% 1.78/1.20  Index Deletion       : 0.00
% 1.78/1.20  Index Matching       : 0.00
% 1.78/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
