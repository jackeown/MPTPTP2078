%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:09 EST 2020

% Result     : Theorem 1.67s
% Output     : CNFRefutation 1.67s
% Verified   : 
% Statistics : Number of formulae       :   34 (  48 expanded)
%              Number of leaves         :   19 (  26 expanded)
%              Depth                    :    4
%              Number of atoms          :   32 (  56 expanded)
%              Number of equality atoms :   30 (  54 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_58,negated_conjecture,(
    ~ ! [A,B] :
        ( A != k1_xboole_0
       => ( k2_zfmisc_1(k1_tarski(B),A) != k1_xboole_0
          & k2_zfmisc_1(A,k1_tarski(B)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t130_zfmisc_1)).

tff(f_27,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(c_26,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,k1_xboole_0) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_67,plain,(
    ! [A_22,B_23] : k4_xboole_0(A_22,k2_xboole_0(A_22,B_23)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_74,plain,(
    ! [A_1] : k4_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_67])).

tff(c_20,plain,(
    ! [B_17] : k4_xboole_0(k1_tarski(B_17),k1_tarski(B_17)) != k1_tarski(B_17) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_84,plain,(
    ! [B_17] : k1_tarski(B_17) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_20])).

tff(c_24,plain,
    ( k2_zfmisc_1('#skF_1',k1_tarski('#skF_2')) = k1_xboole_0
    | k2_zfmisc_1(k1_tarski('#skF_2'),'#skF_1') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_95,plain,(
    k2_zfmisc_1(k1_tarski('#skF_2'),'#skF_1') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_100,plain,(
    ! [B_28,A_29] :
      ( k1_xboole_0 = B_28
      | k1_xboole_0 = A_29
      | k2_zfmisc_1(A_29,B_28) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_103,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_tarski('#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_100])).

tff(c_113,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_26,c_103])).

tff(c_114,plain,(
    k2_zfmisc_1('#skF_1',k1_tarski('#skF_2')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_120,plain,(
    ! [B_30,A_31] :
      ( k1_xboole_0 = B_30
      | k1_xboole_0 = A_31
      | k2_zfmisc_1(A_31,B_30) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_123,plain,
    ( k1_tarski('#skF_2') = k1_xboole_0
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_120])).

tff(c_133,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_84,c_123])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n016.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 14:01:49 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.67/1.12  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.67/1.12  
% 1.67/1.12  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.67/1.12  %$ k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 1.67/1.12  
% 1.67/1.12  %Foreground sorts:
% 1.67/1.12  
% 1.67/1.12  
% 1.67/1.12  %Background operators:
% 1.67/1.12  
% 1.67/1.12  
% 1.67/1.12  %Foreground operators:
% 1.67/1.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.67/1.12  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.67/1.12  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.67/1.12  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.67/1.12  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.67/1.12  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.67/1.12  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.67/1.12  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.67/1.12  tff('#skF_2', type, '#skF_2': $i).
% 1.67/1.12  tff('#skF_1', type, '#skF_1': $i).
% 1.67/1.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.67/1.12  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.67/1.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.67/1.12  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.67/1.12  
% 1.67/1.13  tff(f_58, negated_conjecture, ~(![A, B]: (~(A = k1_xboole_0) => (~(k2_zfmisc_1(k1_tarski(B), A) = k1_xboole_0) & ~(k2_zfmisc_1(A, k1_tarski(B)) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t130_zfmisc_1)).
% 1.67/1.13  tff(f_27, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 1.67/1.13  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 1.67/1.13  tff(f_48, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 1.67/1.13  tff(f_43, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.67/1.13  tff(c_26, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.67/1.13  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, k1_xboole_0)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.67/1.13  tff(c_67, plain, (![A_22, B_23]: (k4_xboole_0(A_22, k2_xboole_0(A_22, B_23))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.67/1.13  tff(c_74, plain, (![A_1]: (k4_xboole_0(A_1, A_1)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_67])).
% 1.67/1.13  tff(c_20, plain, (![B_17]: (k4_xboole_0(k1_tarski(B_17), k1_tarski(B_17))!=k1_tarski(B_17))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.67/1.13  tff(c_84, plain, (![B_17]: (k1_tarski(B_17)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_74, c_20])).
% 1.67/1.13  tff(c_24, plain, (k2_zfmisc_1('#skF_1', k1_tarski('#skF_2'))=k1_xboole_0 | k2_zfmisc_1(k1_tarski('#skF_2'), '#skF_1')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.67/1.13  tff(c_95, plain, (k2_zfmisc_1(k1_tarski('#skF_2'), '#skF_1')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_24])).
% 1.67/1.13  tff(c_100, plain, (![B_28, A_29]: (k1_xboole_0=B_28 | k1_xboole_0=A_29 | k2_zfmisc_1(A_29, B_28)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.67/1.13  tff(c_103, plain, (k1_xboole_0='#skF_1' | k1_tarski('#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_95, c_100])).
% 1.67/1.13  tff(c_113, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84, c_26, c_103])).
% 1.67/1.13  tff(c_114, plain, (k2_zfmisc_1('#skF_1', k1_tarski('#skF_2'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_24])).
% 1.67/1.13  tff(c_120, plain, (![B_30, A_31]: (k1_xboole_0=B_30 | k1_xboole_0=A_31 | k2_zfmisc_1(A_31, B_30)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.67/1.13  tff(c_123, plain, (k1_tarski('#skF_2')=k1_xboole_0 | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_114, c_120])).
% 1.67/1.13  tff(c_133, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_84, c_123])).
% 1.67/1.13  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.67/1.13  
% 1.67/1.13  Inference rules
% 1.67/1.13  ----------------------
% 1.67/1.13  #Ref     : 0
% 1.67/1.13  #Sup     : 27
% 1.67/1.13  #Fact    : 0
% 1.67/1.13  #Define  : 0
% 1.67/1.13  #Split   : 1
% 1.67/1.13  #Chain   : 0
% 1.67/1.13  #Close   : 0
% 1.67/1.13  
% 1.67/1.13  Ordering : KBO
% 1.67/1.13  
% 1.67/1.13  Simplification rules
% 1.67/1.13  ----------------------
% 1.67/1.13  #Subsume      : 0
% 1.67/1.13  #Demod        : 1
% 1.67/1.13  #Tautology    : 20
% 1.67/1.13  #SimpNegUnit  : 2
% 1.67/1.13  #BackRed      : 0
% 1.67/1.13  
% 1.67/1.13  #Partial instantiations: 0
% 1.67/1.13  #Strategies tried      : 1
% 1.67/1.13  
% 1.67/1.13  Timing (in seconds)
% 1.67/1.13  ----------------------
% 1.67/1.14  Preprocessing        : 0.29
% 1.67/1.14  Parsing              : 0.15
% 1.67/1.14  CNF conversion       : 0.02
% 1.67/1.14  Main loop            : 0.10
% 1.67/1.14  Inferencing          : 0.03
% 1.67/1.14  Reduction            : 0.03
% 1.67/1.14  Demodulation         : 0.02
% 1.67/1.14  BG Simplification    : 0.01
% 1.67/1.14  Subsumption          : 0.02
% 1.67/1.14  Abstraction          : 0.01
% 1.67/1.14  MUC search           : 0.00
% 1.67/1.14  Cooper               : 0.00
% 1.67/1.14  Total                : 0.41
% 1.67/1.14  Index Insertion      : 0.00
% 1.67/1.14  Index Deletion       : 0.00
% 1.67/1.14  Index Matching       : 0.00
% 1.67/1.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
