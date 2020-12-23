%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:44 EST 2020

% Result     : Theorem 1.64s
% Output     : CNFRefutation 1.81s
% Verified   : 
% Statistics : Number of formulae       :   24 (  25 expanded)
%              Number of leaves         :   15 (  16 expanded)
%              Depth                    :    5
%              Number of atoms          :   18 (  20 expanded)
%              Number of equality atoms :   17 (  19 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_42,negated_conjecture,(
    ~ ! [A,B] :
        ( A != B
       => k5_xboole_0(k1_tarski(A),k1_tarski(B)) = k2_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(c_14,plain,(
    '#skF_2' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_6,plain,(
    ! [A_5,B_6] : k2_xboole_0(k1_tarski(A_5),k1_tarski(B_6)) = k2_tarski(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_35,plain,(
    ! [A_14,B_15] :
      ( k4_xboole_0(k1_tarski(A_14),k1_tarski(B_15)) = k1_tarski(A_14)
      | B_15 = A_14 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_4,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k4_xboole_0(B_4,A_3)) = k2_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_41,plain,(
    ! [B_15,A_14] :
      ( k5_xboole_0(k1_tarski(B_15),k1_tarski(A_14)) = k2_xboole_0(k1_tarski(B_15),k1_tarski(A_14))
      | B_15 = A_14 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_35,c_4])).

tff(c_72,plain,(
    ! [B_18,A_19] :
      ( k5_xboole_0(k1_tarski(B_18),k1_tarski(A_19)) = k2_tarski(B_18,A_19)
      | B_18 = A_19 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_41])).

tff(c_12,plain,(
    k5_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2')) != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_81,plain,(
    '#skF_2' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_12])).

tff(c_90,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_81])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 21:02:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.64/1.18  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.64/1.18  
% 1.64/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.64/1.18  %$ k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1
% 1.64/1.18  
% 1.64/1.18  %Foreground sorts:
% 1.64/1.18  
% 1.64/1.18  
% 1.64/1.18  %Background operators:
% 1.64/1.18  
% 1.64/1.18  
% 1.64/1.18  %Foreground operators:
% 1.64/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.64/1.18  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.64/1.18  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.64/1.18  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.64/1.18  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.64/1.18  tff('#skF_2', type, '#skF_2': $i).
% 1.64/1.18  tff('#skF_1', type, '#skF_1': $i).
% 1.64/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.64/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.64/1.18  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.64/1.18  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.64/1.18  
% 1.81/1.19  tff(f_42, negated_conjecture, ~(![A, B]: (~(A = B) => (k5_xboole_0(k1_tarski(A), k1_tarski(B)) = k2_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_zfmisc_1)).
% 1.81/1.19  tff(f_31, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 1.81/1.19  tff(f_36, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 1.81/1.19  tff(f_29, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 1.81/1.19  tff(c_14, plain, ('#skF_2'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.81/1.19  tff(c_6, plain, (![A_5, B_6]: (k2_xboole_0(k1_tarski(A_5), k1_tarski(B_6))=k2_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.81/1.19  tff(c_35, plain, (![A_14, B_15]: (k4_xboole_0(k1_tarski(A_14), k1_tarski(B_15))=k1_tarski(A_14) | B_15=A_14)), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.81/1.19  tff(c_4, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k4_xboole_0(B_4, A_3))=k2_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.81/1.19  tff(c_41, plain, (![B_15, A_14]: (k5_xboole_0(k1_tarski(B_15), k1_tarski(A_14))=k2_xboole_0(k1_tarski(B_15), k1_tarski(A_14)) | B_15=A_14)), inference(superposition, [status(thm), theory('equality')], [c_35, c_4])).
% 1.81/1.19  tff(c_72, plain, (![B_18, A_19]: (k5_xboole_0(k1_tarski(B_18), k1_tarski(A_19))=k2_tarski(B_18, A_19) | B_18=A_19)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_41])).
% 1.81/1.19  tff(c_12, plain, (k5_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2'))!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.81/1.19  tff(c_81, plain, ('#skF_2'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_72, c_12])).
% 1.81/1.19  tff(c_90, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14, c_81])).
% 1.81/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.81/1.19  
% 1.81/1.19  Inference rules
% 1.81/1.19  ----------------------
% 1.81/1.19  #Ref     : 0
% 1.81/1.19  #Sup     : 17
% 1.81/1.19  #Fact    : 0
% 1.81/1.19  #Define  : 0
% 1.81/1.19  #Split   : 0
% 1.81/1.19  #Chain   : 0
% 1.81/1.19  #Close   : 0
% 1.81/1.19  
% 1.81/1.19  Ordering : KBO
% 1.81/1.19  
% 1.81/1.19  Simplification rules
% 1.81/1.19  ----------------------
% 1.81/1.19  #Subsume      : 0
% 1.81/1.19  #Demod        : 2
% 1.81/1.19  #Tautology    : 10
% 1.81/1.19  #SimpNegUnit  : 1
% 1.81/1.19  #BackRed      : 0
% 1.81/1.19  
% 1.81/1.19  #Partial instantiations: 0
% 1.81/1.19  #Strategies tried      : 1
% 1.81/1.19  
% 1.81/1.19  Timing (in seconds)
% 1.81/1.19  ----------------------
% 1.82/1.19  Preprocessing        : 0.29
% 1.82/1.19  Parsing              : 0.15
% 1.82/1.19  CNF conversion       : 0.02
% 1.82/1.19  Main loop            : 0.08
% 1.82/1.19  Inferencing          : 0.04
% 1.82/1.19  Reduction            : 0.02
% 1.82/1.19  Demodulation         : 0.02
% 1.82/1.19  BG Simplification    : 0.01
% 1.82/1.19  Subsumption          : 0.01
% 1.82/1.19  Abstraction          : 0.01
% 1.82/1.19  MUC search           : 0.00
% 1.82/1.19  Cooper               : 0.00
% 1.82/1.20  Total                : 0.39
% 1.82/1.20  Index Insertion      : 0.00
% 1.82/1.20  Index Deletion       : 0.00
% 1.82/1.20  Index Matching       : 0.00
% 1.82/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
