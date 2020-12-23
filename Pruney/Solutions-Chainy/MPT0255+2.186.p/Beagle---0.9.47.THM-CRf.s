%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:01 EST 2020

% Result     : Theorem 1.93s
% Output     : CNFRefutation 2.10s
% Verified   : 
% Statistics : Number of formulae       :   40 (  40 expanded)
%              Number of leaves         :   25 (  25 expanded)
%              Depth                    :    7
%              Number of atoms          :   25 (  25 expanded)
%              Number of equality atoms :   24 (  24 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_37,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k1_tarski(A),k3_enumset1(B,C,D,E,F)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_enumset1)).

tff(f_52,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_56,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(A,B),C) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( k2_xboole_0(A,B) = k1_xboole_0
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_xboole_1)).

tff(c_10,plain,(
    ! [A_13,B_14] : k1_enumset1(A_13,A_13,B_14) = k2_tarski(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_12,plain,(
    ! [A_15,B_16,C_17] : k2_enumset1(A_15,A_15,B_16,C_17) = k1_enumset1(A_15,B_16,C_17) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_14,plain,(
    ! [A_18,B_19,C_20,D_21] : k3_enumset1(A_18,A_18,B_19,C_20,D_21) = k2_enumset1(A_18,B_19,C_20,D_21) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_16,plain,(
    ! [E_26,A_22,B_23,D_25,C_24] : k4_enumset1(A_22,A_22,B_23,C_24,D_25,E_26) = k3_enumset1(A_22,B_23,C_24,D_25,E_26) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_244,plain,(
    ! [E_83,F_84,A_82,C_80,B_81,D_79] : k2_xboole_0(k1_tarski(A_82),k3_enumset1(B_81,C_80,D_79,E_83,F_84)) = k4_enumset1(A_82,B_81,C_80,D_79,E_83,F_84) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_24,plain,(
    ! [A_42,B_43] : k2_xboole_0(k1_tarski(A_42),B_43) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_261,plain,(
    ! [E_88,C_86,A_89,F_87,B_85,D_90] : k4_enumset1(A_89,B_85,C_86,D_90,E_88,F_87) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_244,c_24])).

tff(c_273,plain,(
    ! [C_99,A_98,E_100,B_102,D_101] : k3_enumset1(A_98,B_102,C_99,D_101,E_100) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_261])).

tff(c_276,plain,(
    ! [A_103,B_104,C_105,D_106] : k2_enumset1(A_103,B_104,C_105,D_106) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_273])).

tff(c_279,plain,(
    ! [A_107,B_108,C_109] : k1_enumset1(A_107,B_108,C_109) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_276])).

tff(c_287,plain,(
    ! [A_13,B_14] : k2_tarski(A_13,B_14) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_279])).

tff(c_26,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_41,plain,(
    ! [A_47,B_48] :
      ( k1_xboole_0 = A_47
      | k2_xboole_0(A_47,B_48) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_45,plain,(
    k2_tarski('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_41])).

tff(c_289,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_287,c_45])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:41:20 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.93/1.23  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.07/1.23  
% 2.07/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.07/1.24  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.07/1.24  
% 2.07/1.24  %Foreground sorts:
% 2.07/1.24  
% 2.07/1.24  
% 2.07/1.24  %Background operators:
% 2.07/1.24  
% 2.07/1.24  
% 2.07/1.24  %Foreground operators:
% 2.07/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.07/1.24  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.07/1.24  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.07/1.24  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.07/1.24  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.07/1.24  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.07/1.24  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.07/1.24  tff('#skF_2', type, '#skF_2': $i).
% 2.07/1.24  tff('#skF_3', type, '#skF_3': $i).
% 2.07/1.24  tff('#skF_1', type, '#skF_1': $i).
% 2.07/1.24  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.07/1.24  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.07/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.07/1.24  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.07/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.07/1.24  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.07/1.24  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.07/1.24  
% 2.10/1.25  tff(f_37, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.10/1.25  tff(f_39, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 2.10/1.25  tff(f_41, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 2.10/1.25  tff(f_43, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 2.10/1.25  tff(f_33, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k1_tarski(A), k3_enumset1(B, C, D, E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_enumset1)).
% 2.10/1.25  tff(f_52, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.10/1.25  tff(f_56, negated_conjecture, ~(![A, B, C]: ~(k2_xboole_0(k2_tarski(A, B), C) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_zfmisc_1)).
% 2.10/1.25  tff(f_29, axiom, (![A, B]: ((k2_xboole_0(A, B) = k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_xboole_1)).
% 2.10/1.25  tff(c_10, plain, (![A_13, B_14]: (k1_enumset1(A_13, A_13, B_14)=k2_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.10/1.25  tff(c_12, plain, (![A_15, B_16, C_17]: (k2_enumset1(A_15, A_15, B_16, C_17)=k1_enumset1(A_15, B_16, C_17))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.10/1.25  tff(c_14, plain, (![A_18, B_19, C_20, D_21]: (k3_enumset1(A_18, A_18, B_19, C_20, D_21)=k2_enumset1(A_18, B_19, C_20, D_21))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.10/1.25  tff(c_16, plain, (![E_26, A_22, B_23, D_25, C_24]: (k4_enumset1(A_22, A_22, B_23, C_24, D_25, E_26)=k3_enumset1(A_22, B_23, C_24, D_25, E_26))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.10/1.25  tff(c_244, plain, (![E_83, F_84, A_82, C_80, B_81, D_79]: (k2_xboole_0(k1_tarski(A_82), k3_enumset1(B_81, C_80, D_79, E_83, F_84))=k4_enumset1(A_82, B_81, C_80, D_79, E_83, F_84))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.10/1.25  tff(c_24, plain, (![A_42, B_43]: (k2_xboole_0(k1_tarski(A_42), B_43)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.10/1.25  tff(c_261, plain, (![E_88, C_86, A_89, F_87, B_85, D_90]: (k4_enumset1(A_89, B_85, C_86, D_90, E_88, F_87)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_244, c_24])).
% 2.10/1.25  tff(c_273, plain, (![C_99, A_98, E_100, B_102, D_101]: (k3_enumset1(A_98, B_102, C_99, D_101, E_100)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_16, c_261])).
% 2.10/1.25  tff(c_276, plain, (![A_103, B_104, C_105, D_106]: (k2_enumset1(A_103, B_104, C_105, D_106)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_14, c_273])).
% 2.10/1.25  tff(c_279, plain, (![A_107, B_108, C_109]: (k1_enumset1(A_107, B_108, C_109)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_12, c_276])).
% 2.10/1.25  tff(c_287, plain, (![A_13, B_14]: (k2_tarski(A_13, B_14)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_10, c_279])).
% 2.10/1.25  tff(c_26, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.10/1.25  tff(c_41, plain, (![A_47, B_48]: (k1_xboole_0=A_47 | k2_xboole_0(A_47, B_48)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.10/1.25  tff(c_45, plain, (k2_tarski('#skF_1', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_26, c_41])).
% 2.10/1.25  tff(c_289, plain, $false, inference(negUnitSimplification, [status(thm)], [c_287, c_45])).
% 2.10/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.10/1.25  
% 2.10/1.25  Inference rules
% 2.10/1.25  ----------------------
% 2.10/1.25  #Ref     : 0
% 2.10/1.25  #Sup     : 68
% 2.10/1.25  #Fact    : 0
% 2.10/1.25  #Define  : 0
% 2.10/1.25  #Split   : 1
% 2.10/1.25  #Chain   : 0
% 2.10/1.25  #Close   : 0
% 2.10/1.25  
% 2.10/1.25  Ordering : KBO
% 2.10/1.25  
% 2.10/1.25  Simplification rules
% 2.10/1.25  ----------------------
% 2.10/1.25  #Subsume      : 3
% 2.10/1.25  #Demod        : 12
% 2.10/1.25  #Tautology    : 50
% 2.10/1.25  #SimpNegUnit  : 1
% 2.10/1.25  #BackRed      : 2
% 2.10/1.25  
% 2.10/1.25  #Partial instantiations: 0
% 2.10/1.25  #Strategies tried      : 1
% 2.10/1.25  
% 2.10/1.25  Timing (in seconds)
% 2.10/1.25  ----------------------
% 2.10/1.25  Preprocessing        : 0.30
% 2.10/1.25  Parsing              : 0.16
% 2.10/1.25  CNF conversion       : 0.02
% 2.10/1.25  Main loop            : 0.17
% 2.10/1.25  Inferencing          : 0.07
% 2.10/1.25  Reduction            : 0.06
% 2.10/1.25  Demodulation         : 0.04
% 2.10/1.25  BG Simplification    : 0.01
% 2.10/1.25  Subsumption          : 0.02
% 2.10/1.25  Abstraction          : 0.01
% 2.10/1.25  MUC search           : 0.00
% 2.10/1.25  Cooper               : 0.00
% 2.10/1.25  Total                : 0.49
% 2.10/1.25  Index Insertion      : 0.00
% 2.10/1.25  Index Deletion       : 0.00
% 2.10/1.25  Index Matching       : 0.00
% 2.10/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
