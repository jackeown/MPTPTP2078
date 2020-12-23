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
% DateTime   : Thu Dec  3 09:54:09 EST 2020

% Result     : Theorem 1.66s
% Output     : CNFRefutation 1.66s
% Verified   : 
% Statistics : Number of formulae       :   32 (  46 expanded)
%              Number of leaves         :   17 (  24 expanded)
%              Depth                    :    4
%              Number of atoms          :   32 (  56 expanded)
%              Number of equality atoms :   30 (  54 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

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

tff(f_54,negated_conjecture,(
    ~ ! [A,B] :
        ( A != k1_xboole_0
       => ( k2_zfmisc_1(k1_tarski(B),A) != k1_xboole_0
          & k2_zfmisc_1(A,k1_tarski(B)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_zfmisc_1)).

tff(f_27,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_44,axiom,(
    ! [A,B] : k4_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_zfmisc_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(c_22,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2,plain,(
    ! [A_1] : k2_tarski(A_1,A_1) = k1_tarski(A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_64,plain,(
    ! [A_19,B_20] : k4_xboole_0(k1_tarski(A_19),k2_tarski(A_19,B_20)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_71,plain,(
    ! [A_1] : k4_xboole_0(k1_tarski(A_1),k1_tarski(A_1)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_64])).

tff(c_14,plain,(
    ! [B_10] : k4_xboole_0(k1_tarski(B_10),k1_tarski(B_10)) != k1_tarski(B_10) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_74,plain,(
    ! [B_10] : k1_tarski(B_10) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_14])).

tff(c_20,plain,
    ( k2_zfmisc_1('#skF_1',k1_tarski('#skF_2')) = k1_xboole_0
    | k2_zfmisc_1(k1_tarski('#skF_2'),'#skF_1') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_83,plain,(
    k2_zfmisc_1(k1_tarski('#skF_2'),'#skF_1') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_20])).

tff(c_88,plain,(
    ! [B_23,A_24] :
      ( k1_xboole_0 = B_23
      | k1_xboole_0 = A_24
      | k2_zfmisc_1(A_24,B_23) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_91,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_tarski('#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_83,c_88])).

tff(c_101,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_22,c_91])).

tff(c_102,plain,(
    k2_zfmisc_1('#skF_1',k1_tarski('#skF_2')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_108,plain,(
    ! [B_25,A_26] :
      ( k1_xboole_0 = B_25
      | k1_xboole_0 = A_26
      | k2_zfmisc_1(A_26,B_25) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_111,plain,
    ( k1_tarski('#skF_2') = k1_xboole_0
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_108])).

tff(c_121,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_74,c_111])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n013.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 15:48:09 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.66/1.09  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.66/1.09  
% 1.66/1.09  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.66/1.09  %$ k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 1.66/1.09  
% 1.66/1.09  %Foreground sorts:
% 1.66/1.09  
% 1.66/1.09  
% 1.66/1.09  %Background operators:
% 1.66/1.09  
% 1.66/1.09  
% 1.66/1.09  %Foreground operators:
% 1.66/1.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.66/1.09  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.66/1.09  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.66/1.09  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.66/1.09  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.66/1.09  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.66/1.09  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.66/1.09  tff('#skF_2', type, '#skF_2': $i).
% 1.66/1.09  tff('#skF_1', type, '#skF_1': $i).
% 1.66/1.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.66/1.09  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.66/1.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.66/1.09  
% 1.66/1.10  tff(f_54, negated_conjecture, ~(![A, B]: (~(A = k1_xboole_0) => (~(k2_zfmisc_1(k1_tarski(B), A) = k1_xboole_0) & ~(k2_zfmisc_1(A, k1_tarski(B)) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t130_zfmisc_1)).
% 1.66/1.10  tff(f_27, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 1.66/1.10  tff(f_44, axiom, (![A, B]: (k4_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_zfmisc_1)).
% 1.66/1.10  tff(f_42, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 1.66/1.10  tff(f_37, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.66/1.10  tff(c_22, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.66/1.10  tff(c_2, plain, (![A_1]: (k2_tarski(A_1, A_1)=k1_tarski(A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.66/1.10  tff(c_64, plain, (![A_19, B_20]: (k4_xboole_0(k1_tarski(A_19), k2_tarski(A_19, B_20))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.66/1.10  tff(c_71, plain, (![A_1]: (k4_xboole_0(k1_tarski(A_1), k1_tarski(A_1))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_64])).
% 1.66/1.10  tff(c_14, plain, (![B_10]: (k4_xboole_0(k1_tarski(B_10), k1_tarski(B_10))!=k1_tarski(B_10))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.66/1.10  tff(c_74, plain, (![B_10]: (k1_tarski(B_10)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_71, c_14])).
% 1.66/1.10  tff(c_20, plain, (k2_zfmisc_1('#skF_1', k1_tarski('#skF_2'))=k1_xboole_0 | k2_zfmisc_1(k1_tarski('#skF_2'), '#skF_1')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.66/1.10  tff(c_83, plain, (k2_zfmisc_1(k1_tarski('#skF_2'), '#skF_1')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_20])).
% 1.66/1.10  tff(c_88, plain, (![B_23, A_24]: (k1_xboole_0=B_23 | k1_xboole_0=A_24 | k2_zfmisc_1(A_24, B_23)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.66/1.10  tff(c_91, plain, (k1_xboole_0='#skF_1' | k1_tarski('#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_83, c_88])).
% 1.66/1.10  tff(c_101, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_22, c_91])).
% 1.66/1.10  tff(c_102, plain, (k2_zfmisc_1('#skF_1', k1_tarski('#skF_2'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_20])).
% 1.66/1.10  tff(c_108, plain, (![B_25, A_26]: (k1_xboole_0=B_25 | k1_xboole_0=A_26 | k2_zfmisc_1(A_26, B_25)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.66/1.10  tff(c_111, plain, (k1_tarski('#skF_2')=k1_xboole_0 | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_102, c_108])).
% 1.66/1.10  tff(c_121, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_74, c_111])).
% 1.66/1.10  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.66/1.10  
% 1.66/1.10  Inference rules
% 1.66/1.10  ----------------------
% 1.66/1.10  #Ref     : 0
% 1.66/1.10  #Sup     : 25
% 1.66/1.10  #Fact    : 0
% 1.66/1.10  #Define  : 0
% 1.66/1.10  #Split   : 1
% 1.66/1.10  #Chain   : 0
% 1.66/1.10  #Close   : 0
% 1.66/1.10  
% 1.66/1.10  Ordering : KBO
% 1.66/1.10  
% 1.66/1.10  Simplification rules
% 1.66/1.10  ----------------------
% 1.66/1.10  #Subsume      : 0
% 1.66/1.10  #Demod        : 1
% 1.66/1.10  #Tautology    : 18
% 1.66/1.10  #SimpNegUnit  : 2
% 1.66/1.10  #BackRed      : 1
% 1.66/1.10  
% 1.66/1.10  #Partial instantiations: 0
% 1.66/1.10  #Strategies tried      : 1
% 1.66/1.10  
% 1.66/1.10  Timing (in seconds)
% 1.66/1.10  ----------------------
% 1.66/1.10  Preprocessing        : 0.26
% 1.66/1.10  Parsing              : 0.14
% 1.66/1.10  CNF conversion       : 0.01
% 1.66/1.10  Main loop            : 0.10
% 1.66/1.10  Inferencing          : 0.03
% 1.66/1.10  Reduction            : 0.03
% 1.66/1.10  Demodulation         : 0.02
% 1.66/1.10  BG Simplification    : 0.01
% 1.66/1.10  Subsumption          : 0.02
% 1.66/1.10  Abstraction          : 0.00
% 1.66/1.10  MUC search           : 0.00
% 1.66/1.10  Cooper               : 0.00
% 1.66/1.10  Total                : 0.38
% 1.66/1.10  Index Insertion      : 0.00
% 1.66/1.10  Index Deletion       : 0.00
% 1.66/1.10  Index Matching       : 0.00
% 1.66/1.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------
