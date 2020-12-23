%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:15 EST 2020

% Result     : Theorem 3.25s
% Output     : CNFRefutation 3.25s
% Verified   : 
% Statistics : Number of formulae       :   43 (  50 expanded)
%              Number of leaves         :   25 (  29 expanded)
%              Depth                    :   11
%              Number of atoms          :   25 (  32 expanded)
%              Number of equality atoms :   24 (  31 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_33,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_tarski(A),k1_enumset1(B,C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).

tff(f_49,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_51,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_53,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_tarski(A),k2_enumset1(B,C,D,E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_enumset1)).

tff(f_56,negated_conjecture,(
    ~ ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(c_8,plain,(
    ! [A_12,B_13,C_14,D_15] : k2_xboole_0(k1_tarski(A_12),k1_enumset1(B_13,C_14,D_15)) = k2_enumset1(A_12,B_13,C_14,D_15) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_24,plain,(
    ! [A_61] : k2_tarski(A_61,A_61) = k1_tarski(A_61) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_26,plain,(
    ! [A_62,B_63] : k1_enumset1(A_62,A_62,B_63) = k2_tarski(A_62,B_63) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_84,plain,(
    ! [A_78,B_79,C_80,D_81] : k2_xboole_0(k1_tarski(A_78),k1_enumset1(B_79,C_80,D_81)) = k2_enumset1(A_78,B_79,C_80,D_81) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_99,plain,(
    ! [A_82,A_83,B_84] : k2_xboole_0(k1_tarski(A_82),k2_tarski(A_83,B_84)) = k2_enumset1(A_82,A_83,A_83,B_84) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_84])).

tff(c_28,plain,(
    ! [A_64,B_65,C_66] : k2_enumset1(A_64,A_64,B_65,C_66) = k1_enumset1(A_64,B_65,C_66) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_112,plain,(
    ! [A_83,B_84] : k2_xboole_0(k1_tarski(A_83),k2_tarski(A_83,B_84)) = k1_enumset1(A_83,A_83,B_84) ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_28])).

tff(c_132,plain,(
    ! [A_85,B_86] : k2_xboole_0(k1_tarski(A_85),k2_tarski(A_85,B_86)) = k2_tarski(A_85,B_86) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_112])).

tff(c_151,plain,(
    ! [A_61] : k2_xboole_0(k1_tarski(A_61),k1_tarski(A_61)) = k2_tarski(A_61,A_61) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_132])).

tff(c_171,plain,(
    ! [A_91] : k2_xboole_0(k1_tarski(A_91),k1_tarski(A_91)) = k1_tarski(A_91) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_151])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] : k2_xboole_0(k2_xboole_0(A_1,B_2),C_3) = k2_xboole_0(A_1,k2_xboole_0(B_2,C_3)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_375,plain,(
    ! [A_117,C_118] : k2_xboole_0(k1_tarski(A_117),k2_xboole_0(k1_tarski(A_117),C_118)) = k2_xboole_0(k1_tarski(A_117),C_118) ),
    inference(superposition,[status(thm),theory(equality)],[c_171,c_2])).

tff(c_408,plain,(
    ! [A_12,B_13,C_14,D_15] : k2_xboole_0(k1_tarski(A_12),k2_enumset1(A_12,B_13,C_14,D_15)) = k2_xboole_0(k1_tarski(A_12),k1_enumset1(B_13,C_14,D_15)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_375])).

tff(c_1392,plain,(
    ! [A_225,B_226,C_227,D_228] : k2_xboole_0(k1_tarski(A_225),k2_enumset1(A_225,B_226,C_227,D_228)) = k2_enumset1(A_225,B_226,C_227,D_228) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_408])).

tff(c_12,plain,(
    ! [C_22,D_23,A_20,B_21,E_24] : k2_xboole_0(k1_tarski(A_20),k2_enumset1(B_21,C_22,D_23,E_24)) = k3_enumset1(A_20,B_21,C_22,D_23,E_24) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1407,plain,(
    ! [A_225,B_226,C_227,D_228] : k3_enumset1(A_225,A_225,B_226,C_227,D_228) = k2_enumset1(A_225,B_226,C_227,D_228) ),
    inference(superposition,[status(thm),theory(equality)],[c_1392,c_12])).

tff(c_30,plain,(
    k3_enumset1('#skF_1','#skF_1','#skF_2','#skF_3','#skF_4') != k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1445,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1407,c_30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:11:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.25/1.48  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.25/1.49  
% 3.25/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.25/1.49  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.25/1.49  
% 3.25/1.49  %Foreground sorts:
% 3.25/1.49  
% 3.25/1.49  
% 3.25/1.49  %Background operators:
% 3.25/1.49  
% 3.25/1.49  
% 3.25/1.49  %Foreground operators:
% 3.25/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.25/1.49  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.25/1.49  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.25/1.49  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.25/1.49  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.25/1.49  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.25/1.49  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.25/1.49  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.25/1.49  tff('#skF_2', type, '#skF_2': $i).
% 3.25/1.49  tff('#skF_3', type, '#skF_3': $i).
% 3.25/1.49  tff('#skF_1', type, '#skF_1': $i).
% 3.25/1.49  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.25/1.49  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.25/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.25/1.49  tff('#skF_4', type, '#skF_4': $i).
% 3.25/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.25/1.49  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.25/1.49  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.25/1.49  
% 3.25/1.50  tff(f_33, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_tarski(A), k1_enumset1(B, C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_enumset1)).
% 3.25/1.50  tff(f_49, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.25/1.50  tff(f_51, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 3.25/1.50  tff(f_53, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 3.25/1.50  tff(f_27, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 3.25/1.50  tff(f_37, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_tarski(A), k2_enumset1(B, C, D, E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_enumset1)).
% 3.25/1.50  tff(f_56, negated_conjecture, ~(![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 3.25/1.50  tff(c_8, plain, (![A_12, B_13, C_14, D_15]: (k2_xboole_0(k1_tarski(A_12), k1_enumset1(B_13, C_14, D_15))=k2_enumset1(A_12, B_13, C_14, D_15))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.25/1.50  tff(c_24, plain, (![A_61]: (k2_tarski(A_61, A_61)=k1_tarski(A_61))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.25/1.50  tff(c_26, plain, (![A_62, B_63]: (k1_enumset1(A_62, A_62, B_63)=k2_tarski(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.25/1.50  tff(c_84, plain, (![A_78, B_79, C_80, D_81]: (k2_xboole_0(k1_tarski(A_78), k1_enumset1(B_79, C_80, D_81))=k2_enumset1(A_78, B_79, C_80, D_81))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.25/1.50  tff(c_99, plain, (![A_82, A_83, B_84]: (k2_xboole_0(k1_tarski(A_82), k2_tarski(A_83, B_84))=k2_enumset1(A_82, A_83, A_83, B_84))), inference(superposition, [status(thm), theory('equality')], [c_26, c_84])).
% 3.25/1.50  tff(c_28, plain, (![A_64, B_65, C_66]: (k2_enumset1(A_64, A_64, B_65, C_66)=k1_enumset1(A_64, B_65, C_66))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.25/1.50  tff(c_112, plain, (![A_83, B_84]: (k2_xboole_0(k1_tarski(A_83), k2_tarski(A_83, B_84))=k1_enumset1(A_83, A_83, B_84))), inference(superposition, [status(thm), theory('equality')], [c_99, c_28])).
% 3.25/1.50  tff(c_132, plain, (![A_85, B_86]: (k2_xboole_0(k1_tarski(A_85), k2_tarski(A_85, B_86))=k2_tarski(A_85, B_86))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_112])).
% 3.25/1.50  tff(c_151, plain, (![A_61]: (k2_xboole_0(k1_tarski(A_61), k1_tarski(A_61))=k2_tarski(A_61, A_61))), inference(superposition, [status(thm), theory('equality')], [c_24, c_132])).
% 3.25/1.50  tff(c_171, plain, (![A_91]: (k2_xboole_0(k1_tarski(A_91), k1_tarski(A_91))=k1_tarski(A_91))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_151])).
% 3.25/1.50  tff(c_2, plain, (![A_1, B_2, C_3]: (k2_xboole_0(k2_xboole_0(A_1, B_2), C_3)=k2_xboole_0(A_1, k2_xboole_0(B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.25/1.50  tff(c_375, plain, (![A_117, C_118]: (k2_xboole_0(k1_tarski(A_117), k2_xboole_0(k1_tarski(A_117), C_118))=k2_xboole_0(k1_tarski(A_117), C_118))), inference(superposition, [status(thm), theory('equality')], [c_171, c_2])).
% 3.25/1.50  tff(c_408, plain, (![A_12, B_13, C_14, D_15]: (k2_xboole_0(k1_tarski(A_12), k2_enumset1(A_12, B_13, C_14, D_15))=k2_xboole_0(k1_tarski(A_12), k1_enumset1(B_13, C_14, D_15)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_375])).
% 3.25/1.50  tff(c_1392, plain, (![A_225, B_226, C_227, D_228]: (k2_xboole_0(k1_tarski(A_225), k2_enumset1(A_225, B_226, C_227, D_228))=k2_enumset1(A_225, B_226, C_227, D_228))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_408])).
% 3.25/1.50  tff(c_12, plain, (![C_22, D_23, A_20, B_21, E_24]: (k2_xboole_0(k1_tarski(A_20), k2_enumset1(B_21, C_22, D_23, E_24))=k3_enumset1(A_20, B_21, C_22, D_23, E_24))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.25/1.50  tff(c_1407, plain, (![A_225, B_226, C_227, D_228]: (k3_enumset1(A_225, A_225, B_226, C_227, D_228)=k2_enumset1(A_225, B_226, C_227, D_228))), inference(superposition, [status(thm), theory('equality')], [c_1392, c_12])).
% 3.25/1.50  tff(c_30, plain, (k3_enumset1('#skF_1', '#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.25/1.50  tff(c_1445, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1407, c_30])).
% 3.25/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.25/1.50  
% 3.25/1.50  Inference rules
% 3.25/1.50  ----------------------
% 3.25/1.50  #Ref     : 0
% 3.25/1.50  #Sup     : 334
% 3.25/1.50  #Fact    : 0
% 3.25/1.50  #Define  : 0
% 3.25/1.50  #Split   : 0
% 3.25/1.50  #Chain   : 0
% 3.25/1.50  #Close   : 0
% 3.25/1.50  
% 3.25/1.50  Ordering : KBO
% 3.25/1.50  
% 3.25/1.50  Simplification rules
% 3.25/1.50  ----------------------
% 3.25/1.50  #Subsume      : 0
% 3.25/1.50  #Demod        : 300
% 3.25/1.50  #Tautology    : 230
% 3.25/1.50  #SimpNegUnit  : 0
% 3.25/1.50  #BackRed      : 2
% 3.25/1.50  
% 3.25/1.50  #Partial instantiations: 0
% 3.25/1.50  #Strategies tried      : 1
% 3.25/1.50  
% 3.25/1.50  Timing (in seconds)
% 3.25/1.50  ----------------------
% 3.25/1.50  Preprocessing        : 0.30
% 3.25/1.50  Parsing              : 0.16
% 3.25/1.50  CNF conversion       : 0.02
% 3.25/1.50  Main loop            : 0.44
% 3.25/1.50  Inferencing          : 0.18
% 3.25/1.50  Reduction            : 0.17
% 3.25/1.50  Demodulation         : 0.13
% 3.25/1.50  BG Simplification    : 0.03
% 3.25/1.50  Subsumption          : 0.04
% 3.25/1.50  Abstraction          : 0.03
% 3.25/1.50  MUC search           : 0.00
% 3.25/1.50  Cooper               : 0.00
% 3.25/1.50  Total                : 0.76
% 3.25/1.50  Index Insertion      : 0.00
% 3.25/1.50  Index Deletion       : 0.00
% 3.25/1.50  Index Matching       : 0.00
% 3.25/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
