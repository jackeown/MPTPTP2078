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
% DateTime   : Thu Dec  3 09:46:26 EST 2020

% Result     : Theorem 1.99s
% Output     : CNFRefutation 1.99s
% Verified   : 
% Statistics : Number of formulae       :   33 (  33 expanded)
%              Number of leaves         :   24 (  24 expanded)
%              Depth                    :    5
%              Number of atoms          :   14 (  14 expanded)
%              Number of equality atoms :   13 (  13 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_41,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k2_enumset1(A,B,C,D),k1_enumset1(E,F,G)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k1_enumset1(F,G,H)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_enumset1)).

tff(f_44,negated_conjecture,(
    ~ ! [A,B,C,D,E,F] : k6_enumset1(A,A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_enumset1)).

tff(c_16,plain,(
    ! [B_33,C_34,E_36,F_37,A_32,D_35] : k5_enumset1(A_32,A_32,B_33,C_34,D_35,E_36,F_37) = k4_enumset1(A_32,B_33,C_34,D_35,E_36,F_37) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_6,plain,(
    ! [B_6,C_7,E_9,D_8,A_5,G_11,F_10] : k2_xboole_0(k2_enumset1(A_5,B_6,C_7,D_8),k1_enumset1(E_9,F_10,G_11)) = k5_enumset1(A_5,B_6,C_7,D_8,E_9,F_10,G_11) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12,plain,(
    ! [A_23,B_24,C_25,D_26] : k3_enumset1(A_23,A_23,B_24,C_25,D_26) = k2_enumset1(A_23,B_24,C_25,D_26) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_221,plain,(
    ! [G_75,D_80,F_81,A_78,H_77,E_79,C_82,B_76] : k2_xboole_0(k3_enumset1(A_78,B_76,C_82,D_80,E_79),k1_enumset1(F_81,G_75,H_77)) = k6_enumset1(A_78,B_76,C_82,D_80,E_79,F_81,G_75,H_77) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_230,plain,(
    ! [G_75,F_81,A_23,B_24,H_77,D_26,C_25] : k6_enumset1(A_23,A_23,B_24,C_25,D_26,F_81,G_75,H_77) = k2_xboole_0(k2_enumset1(A_23,B_24,C_25,D_26),k1_enumset1(F_81,G_75,H_77)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_221])).

tff(c_233,plain,(
    ! [G_75,F_81,A_23,B_24,H_77,D_26,C_25] : k6_enumset1(A_23,A_23,B_24,C_25,D_26,F_81,G_75,H_77) = k5_enumset1(A_23,B_24,C_25,D_26,F_81,G_75,H_77) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_230])).

tff(c_18,plain,(
    k6_enumset1('#skF_1','#skF_1','#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6') != k4_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_243,plain,(
    k5_enumset1('#skF_1','#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6') != k4_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_233,c_18])).

tff(c_246,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_243])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:54:35 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.99/1.27  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.99/1.27  
% 1.99/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.99/1.27  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.99/1.27  
% 1.99/1.27  %Foreground sorts:
% 1.99/1.27  
% 1.99/1.27  
% 1.99/1.27  %Background operators:
% 1.99/1.27  
% 1.99/1.27  
% 1.99/1.27  %Foreground operators:
% 1.99/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.99/1.27  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.99/1.27  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.99/1.27  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.99/1.27  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.99/1.27  tff('#skF_5', type, '#skF_5': $i).
% 1.99/1.27  tff('#skF_6', type, '#skF_6': $i).
% 1.99/1.27  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.99/1.27  tff('#skF_2', type, '#skF_2': $i).
% 1.99/1.27  tff('#skF_3', type, '#skF_3': $i).
% 1.99/1.27  tff('#skF_1', type, '#skF_1': $i).
% 1.99/1.27  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.99/1.27  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 1.99/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.99/1.27  tff('#skF_4', type, '#skF_4': $i).
% 1.99/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.99/1.27  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.99/1.27  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.99/1.27  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.99/1.27  
% 1.99/1.28  tff(f_41, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 1.99/1.28  tff(f_31, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k2_enumset1(A, B, C, D), k1_enumset1(E, F, G)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_enumset1)).
% 1.99/1.28  tff(f_37, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 1.99/1.28  tff(f_33, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k1_enumset1(F, G, H)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_enumset1)).
% 1.99/1.28  tff(f_44, negated_conjecture, ~(![A, B, C, D, E, F]: (k6_enumset1(A, A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_enumset1)).
% 1.99/1.28  tff(c_16, plain, (![B_33, C_34, E_36, F_37, A_32, D_35]: (k5_enumset1(A_32, A_32, B_33, C_34, D_35, E_36, F_37)=k4_enumset1(A_32, B_33, C_34, D_35, E_36, F_37))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.99/1.28  tff(c_6, plain, (![B_6, C_7, E_9, D_8, A_5, G_11, F_10]: (k2_xboole_0(k2_enumset1(A_5, B_6, C_7, D_8), k1_enumset1(E_9, F_10, G_11))=k5_enumset1(A_5, B_6, C_7, D_8, E_9, F_10, G_11))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.99/1.28  tff(c_12, plain, (![A_23, B_24, C_25, D_26]: (k3_enumset1(A_23, A_23, B_24, C_25, D_26)=k2_enumset1(A_23, B_24, C_25, D_26))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.99/1.28  tff(c_221, plain, (![G_75, D_80, F_81, A_78, H_77, E_79, C_82, B_76]: (k2_xboole_0(k3_enumset1(A_78, B_76, C_82, D_80, E_79), k1_enumset1(F_81, G_75, H_77))=k6_enumset1(A_78, B_76, C_82, D_80, E_79, F_81, G_75, H_77))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.99/1.28  tff(c_230, plain, (![G_75, F_81, A_23, B_24, H_77, D_26, C_25]: (k6_enumset1(A_23, A_23, B_24, C_25, D_26, F_81, G_75, H_77)=k2_xboole_0(k2_enumset1(A_23, B_24, C_25, D_26), k1_enumset1(F_81, G_75, H_77)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_221])).
% 1.99/1.28  tff(c_233, plain, (![G_75, F_81, A_23, B_24, H_77, D_26, C_25]: (k6_enumset1(A_23, A_23, B_24, C_25, D_26, F_81, G_75, H_77)=k5_enumset1(A_23, B_24, C_25, D_26, F_81, G_75, H_77))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_230])).
% 1.99/1.28  tff(c_18, plain, (k6_enumset1('#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')!=k4_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.99/1.28  tff(c_243, plain, (k5_enumset1('#skF_1', '#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')!=k4_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_233, c_18])).
% 1.99/1.28  tff(c_246, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_243])).
% 1.99/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.99/1.28  
% 1.99/1.28  Inference rules
% 1.99/1.28  ----------------------
% 1.99/1.28  #Ref     : 0
% 1.99/1.28  #Sup     : 56
% 1.99/1.28  #Fact    : 0
% 1.99/1.28  #Define  : 0
% 1.99/1.28  #Split   : 0
% 1.99/1.28  #Chain   : 0
% 1.99/1.28  #Close   : 0
% 1.99/1.28  
% 1.99/1.28  Ordering : KBO
% 1.99/1.28  
% 1.99/1.28  Simplification rules
% 1.99/1.28  ----------------------
% 1.99/1.28  #Subsume      : 0
% 1.99/1.28  #Demod        : 17
% 1.99/1.28  #Tautology    : 37
% 1.99/1.28  #SimpNegUnit  : 0
% 1.99/1.28  #BackRed      : 1
% 1.99/1.28  
% 1.99/1.28  #Partial instantiations: 0
% 1.99/1.28  #Strategies tried      : 1
% 1.99/1.28  
% 1.99/1.28  Timing (in seconds)
% 1.99/1.28  ----------------------
% 1.99/1.28  Preprocessing        : 0.31
% 1.99/1.28  Parsing              : 0.16
% 1.99/1.28  CNF conversion       : 0.02
% 1.99/1.28  Main loop            : 0.16
% 1.99/1.28  Inferencing          : 0.07
% 1.99/1.28  Reduction            : 0.05
% 1.99/1.28  Demodulation         : 0.04
% 1.99/1.28  BG Simplification    : 0.02
% 1.99/1.28  Subsumption          : 0.02
% 1.99/1.28  Abstraction          : 0.01
% 1.99/1.28  MUC search           : 0.00
% 1.99/1.28  Cooper               : 0.00
% 1.99/1.28  Total                : 0.49
% 1.99/1.29  Index Insertion      : 0.00
% 1.99/1.29  Index Deletion       : 0.00
% 1.99/1.29  Index Matching       : 0.00
% 1.99/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
