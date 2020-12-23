%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:49 EST 2020

% Result     : Theorem 1.81s
% Output     : CNFRefutation 1.81s
% Verified   : 
% Statistics : Number of formulae       :   38 (  72 expanded)
%              Number of leaves         :   20 (  34 expanded)
%              Depth                    :    7
%              Number of atoms          :   28 (  84 expanded)
%              Number of equality atoms :   27 (  83 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_49,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_xboole_0
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_zfmisc_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_31,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_29,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k3_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(c_20,plain,(
    '#skF_2' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_89,plain,(
    ! [A_29,B_30] :
      ( k4_xboole_0(k1_tarski(A_29),k1_tarski(B_30)) = k1_tarski(A_29)
      | B_30 = A_29 ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_22,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_99,plain,
    ( k1_tarski('#skF_1') = k1_xboole_0
    | '#skF_2' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_22])).

tff(c_109,plain,(
    k1_tarski('#skF_1') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_99])).

tff(c_16,plain,(
    ! [B_17] : k4_xboole_0(k1_tarski(B_17),k1_tarski(B_17)) != k1_tarski(B_17) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_128,plain,(
    k4_xboole_0(k1_xboole_0,k1_tarski('#skF_1')) != k1_tarski('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_16])).

tff(c_136,plain,(
    k4_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_109,c_128])).

tff(c_6,plain,(
    ! [A_4] : k2_tarski(A_4,A_4) = k1_tarski(A_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_62,plain,(
    ! [A_25,B_26] : k3_xboole_0(k1_tarski(A_25),k2_tarski(A_25,B_26)) = k1_tarski(A_25) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(A_1,B_2)) = k4_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_68,plain,(
    ! [A_25,B_26] : k5_xboole_0(k1_tarski(A_25),k1_tarski(A_25)) = k4_xboole_0(k1_tarski(A_25),k2_tarski(A_25,B_26)) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_2])).

tff(c_76,plain,(
    ! [A_25,B_26] : k4_xboole_0(k1_tarski(A_25),k2_tarski(A_25,B_26)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_68])).

tff(c_153,plain,(
    ! [B_34] : k4_xboole_0(k1_xboole_0,k2_tarski('#skF_1',B_34)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_76])).

tff(c_161,plain,(
    k4_xboole_0(k1_xboole_0,k1_tarski('#skF_1')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_153])).

tff(c_164,plain,(
    k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_161])).

tff(c_166,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_136,c_164])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 19:48:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.81/1.19  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.81/1.20  
% 1.81/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.81/1.20  %$ k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 1.81/1.20  
% 1.81/1.20  %Foreground sorts:
% 1.81/1.20  
% 1.81/1.20  
% 1.81/1.20  %Background operators:
% 1.81/1.20  
% 1.81/1.20  
% 1.81/1.20  %Foreground operators:
% 1.81/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.81/1.20  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.81/1.20  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.81/1.20  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.81/1.20  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.81/1.20  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.81/1.20  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.81/1.20  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.81/1.20  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.81/1.20  tff('#skF_2', type, '#skF_2': $i).
% 1.81/1.20  tff('#skF_1', type, '#skF_1': $i).
% 1.81/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.81/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.81/1.20  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.81/1.20  
% 1.81/1.21  tff(f_49, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_xboole_0) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_zfmisc_1)).
% 1.81/1.21  tff(f_44, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 1.81/1.21  tff(f_31, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 1.81/1.21  tff(f_29, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 1.81/1.21  tff(f_39, axiom, (![A, B]: (k3_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_zfmisc_1)).
% 1.81/1.21  tff(f_27, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 1.81/1.21  tff(c_20, plain, ('#skF_2'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.81/1.21  tff(c_89, plain, (![A_29, B_30]: (k4_xboole_0(k1_tarski(A_29), k1_tarski(B_30))=k1_tarski(A_29) | B_30=A_29)), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.81/1.21  tff(c_22, plain, (k4_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.81/1.21  tff(c_99, plain, (k1_tarski('#skF_1')=k1_xboole_0 | '#skF_2'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_89, c_22])).
% 1.81/1.21  tff(c_109, plain, (k1_tarski('#skF_1')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_20, c_99])).
% 1.81/1.21  tff(c_16, plain, (![B_17]: (k4_xboole_0(k1_tarski(B_17), k1_tarski(B_17))!=k1_tarski(B_17))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.81/1.21  tff(c_128, plain, (k4_xboole_0(k1_xboole_0, k1_tarski('#skF_1'))!=k1_tarski('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_109, c_16])).
% 1.81/1.21  tff(c_136, plain, (k4_xboole_0(k1_xboole_0, k1_xboole_0)!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_109, c_109, c_128])).
% 1.81/1.21  tff(c_6, plain, (![A_4]: (k2_tarski(A_4, A_4)=k1_tarski(A_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.81/1.21  tff(c_4, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.81/1.21  tff(c_62, plain, (![A_25, B_26]: (k3_xboole_0(k1_tarski(A_25), k2_tarski(A_25, B_26))=k1_tarski(A_25))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.81/1.21  tff(c_2, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(A_1, B_2))=k4_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.81/1.21  tff(c_68, plain, (![A_25, B_26]: (k5_xboole_0(k1_tarski(A_25), k1_tarski(A_25))=k4_xboole_0(k1_tarski(A_25), k2_tarski(A_25, B_26)))), inference(superposition, [status(thm), theory('equality')], [c_62, c_2])).
% 1.81/1.21  tff(c_76, plain, (![A_25, B_26]: (k4_xboole_0(k1_tarski(A_25), k2_tarski(A_25, B_26))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_68])).
% 1.81/1.21  tff(c_153, plain, (![B_34]: (k4_xboole_0(k1_xboole_0, k2_tarski('#skF_1', B_34))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_109, c_76])).
% 1.81/1.21  tff(c_161, plain, (k4_xboole_0(k1_xboole_0, k1_tarski('#skF_1'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_6, c_153])).
% 1.81/1.21  tff(c_164, plain, (k4_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_109, c_161])).
% 1.81/1.21  tff(c_166, plain, $false, inference(negUnitSimplification, [status(thm)], [c_136, c_164])).
% 1.81/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.81/1.21  
% 1.81/1.21  Inference rules
% 1.81/1.21  ----------------------
% 1.81/1.21  #Ref     : 0
% 1.81/1.21  #Sup     : 37
% 1.81/1.21  #Fact    : 0
% 1.81/1.21  #Define  : 0
% 1.81/1.21  #Split   : 0
% 1.81/1.21  #Chain   : 0
% 1.81/1.21  #Close   : 0
% 1.81/1.21  
% 1.81/1.21  Ordering : KBO
% 1.81/1.21  
% 1.81/1.21  Simplification rules
% 1.81/1.21  ----------------------
% 1.81/1.21  #Subsume      : 1
% 1.81/1.21  #Demod        : 10
% 1.81/1.21  #Tautology    : 26
% 1.81/1.21  #SimpNegUnit  : 3
% 1.81/1.21  #BackRed      : 1
% 1.81/1.21  
% 1.81/1.21  #Partial instantiations: 0
% 1.81/1.21  #Strategies tried      : 1
% 1.81/1.21  
% 1.81/1.21  Timing (in seconds)
% 1.81/1.21  ----------------------
% 1.81/1.21  Preprocessing        : 0.29
% 1.81/1.21  Parsing              : 0.16
% 1.81/1.21  CNF conversion       : 0.02
% 1.81/1.21  Main loop            : 0.12
% 1.81/1.21  Inferencing          : 0.05
% 1.81/1.21  Reduction            : 0.04
% 1.81/1.21  Demodulation         : 0.03
% 1.81/1.21  BG Simplification    : 0.01
% 1.81/1.21  Subsumption          : 0.01
% 1.81/1.21  Abstraction          : 0.01
% 1.81/1.21  MUC search           : 0.00
% 1.81/1.21  Cooper               : 0.00
% 1.81/1.21  Total                : 0.43
% 1.81/1.21  Index Insertion      : 0.00
% 1.81/1.21  Index Deletion       : 0.00
% 1.81/1.21  Index Matching       : 0.00
% 1.81/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
