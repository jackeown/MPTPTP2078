%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:26 EST 2020

% Result     : Theorem 2.55s
% Output     : CNFRefutation 2.55s
% Verified   : 
% Statistics : Number of formulae       :   41 (  48 expanded)
%              Number of leaves         :   24 (  27 expanded)
%              Depth                    :    7
%              Number of atoms          :   34 (  41 expanded)
%              Number of equality atoms :   33 (  40 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_48,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_60,axiom,(
    ! [A] : k1_setfam_1(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_setfam_1)).

tff(f_39,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_37,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k2_tarski(A,B),k1_tarski(C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_enumset1)).

tff(f_58,axiom,(
    ! [A,B] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & k1_setfam_1(k2_xboole_0(A,B)) != k3_xboole_0(k1_setfam_1(A),k1_setfam_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_setfam_1)).

tff(f_63,negated_conjecture,(
    ~ ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(c_48,plain,(
    ! [A_41,B_42] : k2_xboole_0(A_41,k3_xboole_0(A_41,B_42)) = A_41 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_22,plain,(
    ! [A_32,B_33] : k2_xboole_0(k1_tarski(A_32),B_33) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_55,plain,(
    ! [A_32] : k1_tarski(A_32) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_22])).

tff(c_26,plain,(
    ! [A_36] : k1_setfam_1(k1_tarski(A_36)) = A_36 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_14,plain,(
    ! [A_20,B_21] : k1_enumset1(A_20,A_20,B_21) = k2_tarski(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_12,plain,(
    ! [A_19] : k2_tarski(A_19,A_19) = k1_tarski(A_19) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_114,plain,(
    ! [A_53,B_54,C_55] : k2_xboole_0(k2_tarski(A_53,B_54),k1_tarski(C_55)) = k1_enumset1(A_53,B_54,C_55) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_123,plain,(
    ! [A_19,C_55] : k2_xboole_0(k1_tarski(A_19),k1_tarski(C_55)) = k1_enumset1(A_19,A_19,C_55) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_114])).

tff(c_126,plain,(
    ! [A_19,C_55] : k2_xboole_0(k1_tarski(A_19),k1_tarski(C_55)) = k2_tarski(A_19,C_55) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_123])).

tff(c_361,plain,(
    ! [A_94,B_95] :
      ( k3_xboole_0(k1_setfam_1(A_94),k1_setfam_1(B_95)) = k1_setfam_1(k2_xboole_0(A_94,B_95))
      | k1_xboole_0 = B_95
      | k1_xboole_0 = A_94 ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_376,plain,(
    ! [A_94,A_36] :
      ( k1_setfam_1(k2_xboole_0(A_94,k1_tarski(A_36))) = k3_xboole_0(k1_setfam_1(A_94),A_36)
      | k1_tarski(A_36) = k1_xboole_0
      | k1_xboole_0 = A_94 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_361])).

tff(c_593,plain,(
    ! [A_117,A_118] :
      ( k1_setfam_1(k2_xboole_0(A_117,k1_tarski(A_118))) = k3_xboole_0(k1_setfam_1(A_117),A_118)
      | k1_xboole_0 = A_117 ) ),
    inference(negUnitSimplification,[status(thm)],[c_55,c_376])).

tff(c_608,plain,(
    ! [A_19,C_55] :
      ( k3_xboole_0(k1_setfam_1(k1_tarski(A_19)),C_55) = k1_setfam_1(k2_tarski(A_19,C_55))
      | k1_tarski(A_19) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_126,c_593])).

tff(c_618,plain,(
    ! [A_19,C_55] :
      ( k1_setfam_1(k2_tarski(A_19,C_55)) = k3_xboole_0(A_19,C_55)
      | k1_tarski(A_19) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_608])).

tff(c_619,plain,(
    ! [A_19,C_55] : k1_setfam_1(k2_tarski(A_19,C_55)) = k3_xboole_0(A_19,C_55) ),
    inference(negUnitSimplification,[status(thm)],[c_55,c_618])).

tff(c_28,plain,(
    k1_setfam_1(k2_tarski('#skF_1','#skF_2')) != k3_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_725,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_619,c_28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:32:16 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.55/1.37  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.55/1.37  
% 2.55/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.55/1.38  %$ k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.55/1.38  
% 2.55/1.38  %Foreground sorts:
% 2.55/1.38  
% 2.55/1.38  
% 2.55/1.38  %Background operators:
% 2.55/1.38  
% 2.55/1.38  
% 2.55/1.38  %Foreground operators:
% 2.55/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.55/1.38  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.55/1.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.55/1.38  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.55/1.38  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.55/1.38  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.55/1.38  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.55/1.38  tff('#skF_2', type, '#skF_2': $i).
% 2.55/1.38  tff('#skF_1', type, '#skF_1': $i).
% 2.55/1.38  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.55/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.55/1.38  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.55/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.55/1.38  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.55/1.38  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.55/1.38  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.55/1.38  
% 2.55/1.38  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_xboole_1)).
% 2.55/1.38  tff(f_48, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.55/1.38  tff(f_60, axiom, (![A]: (k1_setfam_1(k1_tarski(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_setfam_1)).
% 2.55/1.38  tff(f_39, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.55/1.38  tff(f_37, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.55/1.38  tff(f_31, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k2_tarski(A, B), k1_tarski(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_enumset1)).
% 2.55/1.38  tff(f_58, axiom, (![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(k1_setfam_1(k2_xboole_0(A, B)) = k3_xboole_0(k1_setfam_1(A), k1_setfam_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_setfam_1)).
% 2.55/1.38  tff(f_63, negated_conjecture, ~(![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.55/1.38  tff(c_48, plain, (![A_41, B_42]: (k2_xboole_0(A_41, k3_xboole_0(A_41, B_42))=A_41)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.55/1.38  tff(c_22, plain, (![A_32, B_33]: (k2_xboole_0(k1_tarski(A_32), B_33)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.55/1.38  tff(c_55, plain, (![A_32]: (k1_tarski(A_32)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_48, c_22])).
% 2.55/1.38  tff(c_26, plain, (![A_36]: (k1_setfam_1(k1_tarski(A_36))=A_36)), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.55/1.38  tff(c_14, plain, (![A_20, B_21]: (k1_enumset1(A_20, A_20, B_21)=k2_tarski(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.55/1.38  tff(c_12, plain, (![A_19]: (k2_tarski(A_19, A_19)=k1_tarski(A_19))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.55/1.38  tff(c_114, plain, (![A_53, B_54, C_55]: (k2_xboole_0(k2_tarski(A_53, B_54), k1_tarski(C_55))=k1_enumset1(A_53, B_54, C_55))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.55/1.38  tff(c_123, plain, (![A_19, C_55]: (k2_xboole_0(k1_tarski(A_19), k1_tarski(C_55))=k1_enumset1(A_19, A_19, C_55))), inference(superposition, [status(thm), theory('equality')], [c_12, c_114])).
% 2.55/1.38  tff(c_126, plain, (![A_19, C_55]: (k2_xboole_0(k1_tarski(A_19), k1_tarski(C_55))=k2_tarski(A_19, C_55))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_123])).
% 2.55/1.38  tff(c_361, plain, (![A_94, B_95]: (k3_xboole_0(k1_setfam_1(A_94), k1_setfam_1(B_95))=k1_setfam_1(k2_xboole_0(A_94, B_95)) | k1_xboole_0=B_95 | k1_xboole_0=A_94)), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.55/1.38  tff(c_376, plain, (![A_94, A_36]: (k1_setfam_1(k2_xboole_0(A_94, k1_tarski(A_36)))=k3_xboole_0(k1_setfam_1(A_94), A_36) | k1_tarski(A_36)=k1_xboole_0 | k1_xboole_0=A_94)), inference(superposition, [status(thm), theory('equality')], [c_26, c_361])).
% 2.55/1.38  tff(c_593, plain, (![A_117, A_118]: (k1_setfam_1(k2_xboole_0(A_117, k1_tarski(A_118)))=k3_xboole_0(k1_setfam_1(A_117), A_118) | k1_xboole_0=A_117)), inference(negUnitSimplification, [status(thm)], [c_55, c_376])).
% 2.55/1.38  tff(c_608, plain, (![A_19, C_55]: (k3_xboole_0(k1_setfam_1(k1_tarski(A_19)), C_55)=k1_setfam_1(k2_tarski(A_19, C_55)) | k1_tarski(A_19)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_126, c_593])).
% 2.55/1.38  tff(c_618, plain, (![A_19, C_55]: (k1_setfam_1(k2_tarski(A_19, C_55))=k3_xboole_0(A_19, C_55) | k1_tarski(A_19)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_608])).
% 2.55/1.38  tff(c_619, plain, (![A_19, C_55]: (k1_setfam_1(k2_tarski(A_19, C_55))=k3_xboole_0(A_19, C_55))), inference(negUnitSimplification, [status(thm)], [c_55, c_618])).
% 2.55/1.38  tff(c_28, plain, (k1_setfam_1(k2_tarski('#skF_1', '#skF_2'))!=k3_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.55/1.38  tff(c_725, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_619, c_28])).
% 2.55/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.55/1.38  
% 2.55/1.38  Inference rules
% 2.55/1.38  ----------------------
% 2.55/1.38  #Ref     : 0
% 2.55/1.38  #Sup     : 163
% 2.55/1.38  #Fact    : 0
% 2.55/1.38  #Define  : 0
% 2.55/1.38  #Split   : 0
% 2.55/1.38  #Chain   : 0
% 2.55/1.38  #Close   : 0
% 2.55/1.38  
% 2.55/1.38  Ordering : KBO
% 2.55/1.38  
% 2.55/1.38  Simplification rules
% 2.55/1.38  ----------------------
% 2.55/1.38  #Subsume      : 18
% 2.55/1.38  #Demod        : 108
% 2.55/1.38  #Tautology    : 111
% 2.55/1.38  #SimpNegUnit  : 6
% 2.55/1.38  #BackRed      : 5
% 2.55/1.38  
% 2.55/1.38  #Partial instantiations: 0
% 2.55/1.38  #Strategies tried      : 1
% 2.55/1.38  
% 2.55/1.38  Timing (in seconds)
% 2.55/1.38  ----------------------
% 2.55/1.39  Preprocessing        : 0.31
% 2.55/1.39  Parsing              : 0.17
% 2.55/1.39  CNF conversion       : 0.02
% 2.55/1.39  Main loop            : 0.28
% 2.55/1.39  Inferencing          : 0.12
% 2.55/1.39  Reduction            : 0.10
% 2.55/1.39  Demodulation         : 0.08
% 2.55/1.39  BG Simplification    : 0.02
% 2.55/1.39  Subsumption          : 0.03
% 2.55/1.39  Abstraction          : 0.02
% 2.55/1.39  MUC search           : 0.00
% 2.55/1.39  Cooper               : 0.00
% 2.55/1.39  Total                : 0.61
% 2.55/1.39  Index Insertion      : 0.00
% 2.55/1.39  Index Deletion       : 0.00
% 2.55/1.39  Index Matching       : 0.00
% 2.55/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
