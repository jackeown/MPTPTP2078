%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:25 EST 2020

% Result     : Theorem 5.18s
% Output     : CNFRefutation 5.55s
% Verified   : 
% Statistics : Number of formulae       :   31 (  31 expanded)
%              Number of leaves         :   22 (  22 expanded)
%              Depth                    :    5
%              Number of atoms          :   14 (  14 expanded)
%              Number of equality atoms :   13 (  13 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_31,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k1_enumset1(A,B,C),k1_enumset1(D,E,F)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k1_enumset1(F,G,H)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_enumset1)).

tff(f_44,negated_conjecture,(
    ~ ! [A,B,C,D,E,F] : k6_enumset1(A,A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_enumset1)).

tff(c_6,plain,(
    ! [B_16,A_15,D_18,E_19,F_20,C_17] : k2_xboole_0(k1_enumset1(A_15,B_16,C_17),k1_enumset1(D_18,E_19,F_20)) = k4_enumset1(A_15,B_16,C_17,D_18,E_19,F_20) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12,plain,(
    ! [A_30,B_31,C_32] : k2_enumset1(A_30,A_30,B_31,C_32) = k1_enumset1(A_30,B_31,C_32) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_14,plain,(
    ! [A_33,B_34,C_35,D_36] : k3_enumset1(A_33,A_33,B_34,C_35,D_36) = k2_enumset1(A_33,B_34,C_35,D_36) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_890,plain,(
    ! [D_115,G_113,F_118,B_119,C_117,E_120,A_114,H_116] : k2_xboole_0(k3_enumset1(A_114,B_119,C_117,D_115,E_120),k1_enumset1(F_118,G_113,H_116)) = k6_enumset1(A_114,B_119,C_117,D_115,E_120,F_118,G_113,H_116) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2824,plain,(
    ! [F_214,C_211,H_215,D_212,B_216,A_210,G_213] : k6_enumset1(A_210,A_210,B_216,C_211,D_212,F_214,G_213,H_215) = k2_xboole_0(k2_enumset1(A_210,B_216,C_211,D_212),k1_enumset1(F_214,G_213,H_215)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_890])).

tff(c_2926,plain,(
    ! [F_214,H_215,A_30,C_32,G_213,B_31] : k6_enumset1(A_30,A_30,A_30,B_31,C_32,F_214,G_213,H_215) = k2_xboole_0(k1_enumset1(A_30,B_31,C_32),k1_enumset1(F_214,G_213,H_215)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_2824])).

tff(c_2952,plain,(
    ! [F_214,H_215,A_30,C_32,G_213,B_31] : k6_enumset1(A_30,A_30,A_30,B_31,C_32,F_214,G_213,H_215) = k4_enumset1(A_30,B_31,C_32,F_214,G_213,H_215) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_2926])).

tff(c_18,plain,(
    k6_enumset1('#skF_1','#skF_1','#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6') != k4_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_4282,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2952,c_18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:28:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.18/2.06  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.18/2.06  
% 5.18/2.06  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.18/2.06  %$ k6_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 5.18/2.06  
% 5.18/2.06  %Foreground sorts:
% 5.18/2.06  
% 5.18/2.06  
% 5.18/2.06  %Background operators:
% 5.18/2.06  
% 5.18/2.06  
% 5.18/2.06  %Foreground operators:
% 5.18/2.06  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.18/2.06  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.18/2.06  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 5.18/2.06  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.18/2.06  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.18/2.06  tff('#skF_5', type, '#skF_5': $i).
% 5.18/2.06  tff('#skF_6', type, '#skF_6': $i).
% 5.18/2.06  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.18/2.06  tff('#skF_2', type, '#skF_2': $i).
% 5.18/2.06  tff('#skF_3', type, '#skF_3': $i).
% 5.18/2.06  tff('#skF_1', type, '#skF_1': $i).
% 5.18/2.06  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.18/2.06  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 5.18/2.06  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.18/2.06  tff('#skF_4', type, '#skF_4': $i).
% 5.18/2.06  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.18/2.06  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.18/2.06  
% 5.55/2.07  tff(f_31, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k1_enumset1(A, B, C), k1_enumset1(D, E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t53_enumset1)).
% 5.55/2.07  tff(f_37, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 5.55/2.07  tff(f_39, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 5.55/2.07  tff(f_33, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k1_enumset1(F, G, H)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_enumset1)).
% 5.55/2.07  tff(f_44, negated_conjecture, ~(![A, B, C, D, E, F]: (k6_enumset1(A, A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_enumset1)).
% 5.55/2.07  tff(c_6, plain, (![B_16, A_15, D_18, E_19, F_20, C_17]: (k2_xboole_0(k1_enumset1(A_15, B_16, C_17), k1_enumset1(D_18, E_19, F_20))=k4_enumset1(A_15, B_16, C_17, D_18, E_19, F_20))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.55/2.07  tff(c_12, plain, (![A_30, B_31, C_32]: (k2_enumset1(A_30, A_30, B_31, C_32)=k1_enumset1(A_30, B_31, C_32))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.55/2.07  tff(c_14, plain, (![A_33, B_34, C_35, D_36]: (k3_enumset1(A_33, A_33, B_34, C_35, D_36)=k2_enumset1(A_33, B_34, C_35, D_36))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.55/2.07  tff(c_890, plain, (![D_115, G_113, F_118, B_119, C_117, E_120, A_114, H_116]: (k2_xboole_0(k3_enumset1(A_114, B_119, C_117, D_115, E_120), k1_enumset1(F_118, G_113, H_116))=k6_enumset1(A_114, B_119, C_117, D_115, E_120, F_118, G_113, H_116))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.55/2.07  tff(c_2824, plain, (![F_214, C_211, H_215, D_212, B_216, A_210, G_213]: (k6_enumset1(A_210, A_210, B_216, C_211, D_212, F_214, G_213, H_215)=k2_xboole_0(k2_enumset1(A_210, B_216, C_211, D_212), k1_enumset1(F_214, G_213, H_215)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_890])).
% 5.55/2.07  tff(c_2926, plain, (![F_214, H_215, A_30, C_32, G_213, B_31]: (k6_enumset1(A_30, A_30, A_30, B_31, C_32, F_214, G_213, H_215)=k2_xboole_0(k1_enumset1(A_30, B_31, C_32), k1_enumset1(F_214, G_213, H_215)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_2824])).
% 5.55/2.07  tff(c_2952, plain, (![F_214, H_215, A_30, C_32, G_213, B_31]: (k6_enumset1(A_30, A_30, A_30, B_31, C_32, F_214, G_213, H_215)=k4_enumset1(A_30, B_31, C_32, F_214, G_213, H_215))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_2926])).
% 5.55/2.07  tff(c_18, plain, (k6_enumset1('#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')!=k4_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.55/2.07  tff(c_4282, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2952, c_18])).
% 5.55/2.07  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.55/2.07  
% 5.55/2.07  Inference rules
% 5.55/2.07  ----------------------
% 5.55/2.07  #Ref     : 0
% 5.55/2.07  #Sup     : 984
% 5.55/2.07  #Fact    : 0
% 5.55/2.07  #Define  : 0
% 5.55/2.07  #Split   : 0
% 5.55/2.07  #Chain   : 0
% 5.55/2.07  #Close   : 0
% 5.55/2.07  
% 5.55/2.07  Ordering : KBO
% 5.55/2.07  
% 5.55/2.07  Simplification rules
% 5.55/2.07  ----------------------
% 5.55/2.07  #Subsume      : 139
% 5.55/2.07  #Demod        : 1151
% 5.55/2.07  #Tautology    : 717
% 5.55/2.07  #SimpNegUnit  : 0
% 5.55/2.07  #BackRed      : 2
% 5.55/2.07  
% 5.55/2.07  #Partial instantiations: 0
% 5.55/2.07  #Strategies tried      : 1
% 5.55/2.07  
% 5.55/2.07  Timing (in seconds)
% 5.55/2.07  ----------------------
% 5.55/2.08  Preprocessing        : 0.30
% 5.55/2.08  Parsing              : 0.16
% 5.55/2.08  CNF conversion       : 0.02
% 5.55/2.08  Main loop            : 1.01
% 5.55/2.08  Inferencing          : 0.42
% 5.55/2.08  Reduction            : 0.44
% 5.55/2.08  Demodulation         : 0.38
% 5.55/2.08  BG Simplification    : 0.03
% 5.55/2.08  Subsumption          : 0.08
% 5.55/2.08  Abstraction          : 0.08
% 5.55/2.08  MUC search           : 0.00
% 5.55/2.08  Cooper               : 0.00
% 5.55/2.08  Total                : 1.33
% 5.55/2.08  Index Insertion      : 0.00
% 5.55/2.08  Index Deletion       : 0.00
% 5.55/2.08  Index Matching       : 0.00
% 5.55/2.08  BG Taut test         : 0.00
%------------------------------------------------------------------------------
