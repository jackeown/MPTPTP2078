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
% DateTime   : Thu Dec  3 09:54:07 EST 2020

% Result     : Theorem 1.75s
% Output     : CNFRefutation 2.00s
% Verified   : 
% Statistics : Number of formulae       :   42 (  69 expanded)
%              Number of leaves         :   24 (  36 expanded)
%              Depth                    :    6
%              Number of atoms          :   34 (  95 expanded)
%              Number of equality atoms :   32 (  93 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_61,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_76,negated_conjecture,(
    ~ ! [A,B] :
        ( A != k1_xboole_0
       => ( k2_zfmisc_1(k1_tarski(B),A) != k1_xboole_0
          & k2_zfmisc_1(A,k1_tarski(B)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_zfmisc_1)).

tff(f_31,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_66,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(c_36,plain,(
    ! [B_46] : k2_zfmisc_1(k1_xboole_0,B_46) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_44,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_42,plain,
    ( k2_zfmisc_1('#skF_1',k1_tarski('#skF_2')) = k1_xboole_0
    | k2_zfmisc_1(k1_tarski('#skF_2'),'#skF_1') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_113,plain,(
    k2_zfmisc_1(k1_tarski('#skF_2'),'#skF_1') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_147,plain,(
    ! [B_61,A_62] :
      ( k1_xboole_0 = B_61
      | k1_xboole_0 = A_62
      | k2_zfmisc_1(A_62,B_61) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_150,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_tarski('#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_147])).

tff(c_159,plain,(
    k1_tarski('#skF_2') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_150])).

tff(c_6,plain,(
    ! [A_4] : k4_xboole_0(A_4,k1_xboole_0) = A_4 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_38,plain,(
    ! [B_48] : k4_xboole_0(k1_tarski(B_48),k1_tarski(B_48)) != k1_tarski(B_48) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_172,plain,(
    k4_xboole_0(k1_xboole_0,k1_tarski('#skF_2')) != k1_tarski('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_159,c_38])).

tff(c_180,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_6,c_159,c_172])).

tff(c_181,plain,(
    k2_zfmisc_1('#skF_1',k1_tarski('#skF_2')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_216,plain,(
    ! [B_66,A_67] :
      ( k1_xboole_0 = B_66
      | k1_xboole_0 = A_67
      | k2_zfmisc_1(A_67,B_66) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_219,plain,
    ( k1_tarski('#skF_2') = k1_xboole_0
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_181,c_216])).

tff(c_228,plain,(
    k1_tarski('#skF_2') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_219])).

tff(c_182,plain,(
    k2_zfmisc_1(k1_tarski('#skF_2'),'#skF_1') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_233,plain,(
    k2_zfmisc_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_228,c_182])).

tff(c_237,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_233])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n009.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 16:16:56 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.75/1.17  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.00/1.17  
% 2.00/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.00/1.17  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 2.00/1.17  
% 2.00/1.17  %Foreground sorts:
% 2.00/1.17  
% 2.00/1.17  
% 2.00/1.17  %Background operators:
% 2.00/1.17  
% 2.00/1.17  
% 2.00/1.17  %Foreground operators:
% 2.00/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.00/1.17  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.00/1.17  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.00/1.17  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.00/1.17  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.00/1.17  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.00/1.17  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.00/1.17  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.00/1.17  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.00/1.17  tff('#skF_2', type, '#skF_2': $i).
% 2.00/1.17  tff('#skF_1', type, '#skF_1': $i).
% 2.00/1.17  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.00/1.17  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.00/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.00/1.17  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.00/1.17  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.00/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.00/1.17  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.00/1.17  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.00/1.17  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.00/1.17  
% 2.00/1.18  tff(f_61, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.00/1.18  tff(f_76, negated_conjecture, ~(![A, B]: (~(A = k1_xboole_0) => (~(k2_zfmisc_1(k1_tarski(B), A) = k1_xboole_0) & ~(k2_zfmisc_1(A, k1_tarski(B)) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t130_zfmisc_1)).
% 2.00/1.18  tff(f_31, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 2.00/1.18  tff(f_66, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.00/1.18  tff(c_36, plain, (![B_46]: (k2_zfmisc_1(k1_xboole_0, B_46)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.00/1.18  tff(c_44, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.00/1.18  tff(c_42, plain, (k2_zfmisc_1('#skF_1', k1_tarski('#skF_2'))=k1_xboole_0 | k2_zfmisc_1(k1_tarski('#skF_2'), '#skF_1')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.00/1.18  tff(c_113, plain, (k2_zfmisc_1(k1_tarski('#skF_2'), '#skF_1')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_42])).
% 2.00/1.18  tff(c_147, plain, (![B_61, A_62]: (k1_xboole_0=B_61 | k1_xboole_0=A_62 | k2_zfmisc_1(A_62, B_61)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.00/1.18  tff(c_150, plain, (k1_xboole_0='#skF_1' | k1_tarski('#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_113, c_147])).
% 2.00/1.18  tff(c_159, plain, (k1_tarski('#skF_2')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_44, c_150])).
% 2.00/1.18  tff(c_6, plain, (![A_4]: (k4_xboole_0(A_4, k1_xboole_0)=A_4)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.00/1.18  tff(c_38, plain, (![B_48]: (k4_xboole_0(k1_tarski(B_48), k1_tarski(B_48))!=k1_tarski(B_48))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.00/1.18  tff(c_172, plain, (k4_xboole_0(k1_xboole_0, k1_tarski('#skF_2'))!=k1_tarski('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_159, c_38])).
% 2.00/1.18  tff(c_180, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_159, c_6, c_159, c_172])).
% 2.00/1.18  tff(c_181, plain, (k2_zfmisc_1('#skF_1', k1_tarski('#skF_2'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_42])).
% 2.00/1.18  tff(c_216, plain, (![B_66, A_67]: (k1_xboole_0=B_66 | k1_xboole_0=A_67 | k2_zfmisc_1(A_67, B_66)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.00/1.18  tff(c_219, plain, (k1_tarski('#skF_2')=k1_xboole_0 | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_181, c_216])).
% 2.00/1.18  tff(c_228, plain, (k1_tarski('#skF_2')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_44, c_219])).
% 2.00/1.18  tff(c_182, plain, (k2_zfmisc_1(k1_tarski('#skF_2'), '#skF_1')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_42])).
% 2.00/1.18  tff(c_233, plain, (k2_zfmisc_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_228, c_182])).
% 2.00/1.18  tff(c_237, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_233])).
% 2.00/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.00/1.18  
% 2.00/1.18  Inference rules
% 2.00/1.18  ----------------------
% 2.00/1.18  #Ref     : 0
% 2.00/1.18  #Sup     : 45
% 2.00/1.18  #Fact    : 0
% 2.00/1.18  #Define  : 0
% 2.00/1.18  #Split   : 1
% 2.00/1.18  #Chain   : 0
% 2.00/1.18  #Close   : 0
% 2.00/1.18  
% 2.00/1.18  Ordering : KBO
% 2.00/1.18  
% 2.00/1.18  Simplification rules
% 2.00/1.18  ----------------------
% 2.00/1.18  #Subsume      : 0
% 2.00/1.18  #Demod        : 8
% 2.00/1.18  #Tautology    : 38
% 2.00/1.18  #SimpNegUnit  : 2
% 2.00/1.18  #BackRed      : 3
% 2.00/1.18  
% 2.00/1.18  #Partial instantiations: 0
% 2.00/1.18  #Strategies tried      : 1
% 2.00/1.18  
% 2.00/1.18  Timing (in seconds)
% 2.00/1.18  ----------------------
% 2.00/1.18  Preprocessing        : 0.31
% 2.00/1.19  Parsing              : 0.16
% 2.00/1.19  CNF conversion       : 0.02
% 2.00/1.19  Main loop            : 0.14
% 2.00/1.19  Inferencing          : 0.04
% 2.00/1.19  Reduction            : 0.05
% 2.00/1.19  Demodulation         : 0.03
% 2.00/1.19  BG Simplification    : 0.01
% 2.00/1.19  Subsumption          : 0.02
% 2.00/1.19  Abstraction          : 0.01
% 2.00/1.19  MUC search           : 0.00
% 2.00/1.19  Cooper               : 0.00
% 2.00/1.19  Total                : 0.47
% 2.00/1.19  Index Insertion      : 0.00
% 2.00/1.19  Index Deletion       : 0.00
% 2.00/1.19  Index Matching       : 0.00
% 2.00/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
