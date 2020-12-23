%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:48 EST 2020

% Result     : Theorem 1.68s
% Output     : CNFRefutation 1.68s
% Verified   : 
% Statistics : Number of formulae       :   31 (  33 expanded)
%              Number of leaves         :   18 (  20 expanded)
%              Depth                    :    5
%              Number of atoms          :   22 (  26 expanded)
%              Number of equality atoms :   21 (  25 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_31,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_47,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_xboole_0
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_zfmisc_1)).

tff(c_6,plain,(
    ! [A_5] : k5_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_60,plain,(
    ! [A_20,B_21] : k5_xboole_0(A_20,k3_xboole_0(A_20,B_21)) = k4_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_69,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_60])).

tff(c_72,plain,(
    ! [A_1] : k4_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_69])).

tff(c_14,plain,(
    ! [B_13] : k4_xboole_0(k1_tarski(B_13),k1_tarski(B_13)) != k1_tarski(B_13) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_73,plain,(
    ! [B_13] : k1_tarski(B_13) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_14])).

tff(c_18,plain,(
    '#skF_2' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_20,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_82,plain,(
    ! [A_23,B_24] :
      ( k4_xboole_0(k1_tarski(A_23),k1_tarski(B_24)) = k1_tarski(A_23)
      | B_24 = A_23 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_102,plain,
    ( k1_tarski('#skF_1') = k1_xboole_0
    | '#skF_2' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_82])).

tff(c_108,plain,(
    k1_tarski('#skF_1') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_102])).

tff(c_110,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_73,c_108])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:33:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.68/1.12  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.68/1.13  
% 1.68/1.13  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.68/1.13  %$ k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 1.68/1.13  
% 1.68/1.13  %Foreground sorts:
% 1.68/1.13  
% 1.68/1.13  
% 1.68/1.13  %Background operators:
% 1.68/1.13  
% 1.68/1.13  
% 1.68/1.13  %Foreground operators:
% 1.68/1.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.68/1.13  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.68/1.13  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.68/1.13  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.68/1.13  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.68/1.13  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.68/1.13  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.68/1.13  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.68/1.13  tff('#skF_2', type, '#skF_2': $i).
% 1.68/1.13  tff('#skF_1', type, '#skF_1': $i).
% 1.68/1.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.68/1.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.68/1.13  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.68/1.13  
% 1.68/1.14  tff(f_31, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 1.68/1.14  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 1.68/1.14  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 1.68/1.14  tff(f_42, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 1.68/1.14  tff(f_47, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_xboole_0) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_zfmisc_1)).
% 1.68/1.14  tff(c_6, plain, (![A_5]: (k5_xboole_0(A_5, A_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.68/1.14  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.68/1.14  tff(c_60, plain, (![A_20, B_21]: (k5_xboole_0(A_20, k3_xboole_0(A_20, B_21))=k4_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.68/1.14  tff(c_69, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_60])).
% 1.68/1.14  tff(c_72, plain, (![A_1]: (k4_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_69])).
% 1.68/1.14  tff(c_14, plain, (![B_13]: (k4_xboole_0(k1_tarski(B_13), k1_tarski(B_13))!=k1_tarski(B_13))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.68/1.14  tff(c_73, plain, (![B_13]: (k1_tarski(B_13)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_72, c_14])).
% 1.68/1.14  tff(c_18, plain, ('#skF_2'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.68/1.14  tff(c_20, plain, (k4_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.68/1.14  tff(c_82, plain, (![A_23, B_24]: (k4_xboole_0(k1_tarski(A_23), k1_tarski(B_24))=k1_tarski(A_23) | B_24=A_23)), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.68/1.14  tff(c_102, plain, (k1_tarski('#skF_1')=k1_xboole_0 | '#skF_2'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_20, c_82])).
% 1.68/1.14  tff(c_108, plain, (k1_tarski('#skF_1')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_18, c_102])).
% 1.68/1.14  tff(c_110, plain, $false, inference(negUnitSimplification, [status(thm)], [c_73, c_108])).
% 1.68/1.14  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.68/1.14  
% 1.68/1.14  Inference rules
% 1.68/1.14  ----------------------
% 1.68/1.14  #Ref     : 0
% 1.68/1.14  #Sup     : 21
% 1.68/1.14  #Fact    : 0
% 1.68/1.14  #Define  : 0
% 1.68/1.14  #Split   : 0
% 1.68/1.14  #Chain   : 0
% 1.68/1.14  #Close   : 0
% 1.68/1.14  
% 1.68/1.14  Ordering : KBO
% 1.68/1.14  
% 1.68/1.14  Simplification rules
% 1.68/1.14  ----------------------
% 1.68/1.14  #Subsume      : 0
% 1.68/1.14  #Demod        : 2
% 1.68/1.14  #Tautology    : 18
% 1.68/1.14  #SimpNegUnit  : 3
% 1.68/1.14  #BackRed      : 1
% 1.68/1.14  
% 1.68/1.14  #Partial instantiations: 0
% 1.68/1.14  #Strategies tried      : 1
% 1.68/1.14  
% 1.68/1.14  Timing (in seconds)
% 1.68/1.14  ----------------------
% 1.68/1.14  Preprocessing        : 0.29
% 1.68/1.14  Parsing              : 0.15
% 1.68/1.14  CNF conversion       : 0.02
% 1.68/1.14  Main loop            : 0.10
% 1.68/1.14  Inferencing          : 0.04
% 1.68/1.14  Reduction            : 0.03
% 1.68/1.14  Demodulation         : 0.02
% 1.68/1.14  BG Simplification    : 0.01
% 1.68/1.14  Subsumption          : 0.01
% 1.68/1.14  Abstraction          : 0.01
% 1.68/1.14  MUC search           : 0.00
% 1.68/1.14  Cooper               : 0.00
% 1.68/1.14  Total                : 0.41
% 1.68/1.14  Index Insertion      : 0.00
% 1.68/1.14  Index Deletion       : 0.00
% 1.68/1.14  Index Matching       : 0.00
% 1.68/1.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
