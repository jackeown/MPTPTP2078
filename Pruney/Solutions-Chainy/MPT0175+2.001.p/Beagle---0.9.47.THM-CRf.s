%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:33 EST 2020

% Result     : Theorem 2.02s
% Output     : CNFRefutation 2.02s
% Verified   : 
% Statistics : Number of formulae       :   39 (  43 expanded)
%              Number of leaves         :   23 (  25 expanded)
%              Depth                    :    6
%              Number of atoms          :   24 (  28 expanded)
%              Number of equality atoms :   23 (  27 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_33,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_35,axiom,(
    ! [A,B] : k2_enumset1(A,A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_enumset1)).

tff(f_43,axiom,(
    ! [A] : k3_enumset1(A,A,A,A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k2_tarski(A,B),k1_tarski(C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k2_tarski(A,B),k3_enumset1(C,D,E,F,G)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D,E] : k5_enumset1(A,A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D] : k4_enumset1(A,A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_enumset1)).

tff(f_46,negated_conjecture,(
    ~ ! [A] : k4_enumset1(A,A,A,A,A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_enumset1)).

tff(c_50,plain,(
    ! [A_39,B_40,C_41] : k2_enumset1(A_39,A_39,B_40,C_41) = k1_enumset1(A_39,B_40,C_41) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [A_16,B_17] : k2_enumset1(A_16,A_16,A_16,B_17) = k2_tarski(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_57,plain,(
    ! [B_40,C_41] : k1_enumset1(B_40,B_40,C_41) = k2_tarski(B_40,C_41) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_10])).

tff(c_18,plain,(
    ! [A_33] : k3_enumset1(A_33,A_33,A_33,A_33,A_33) = k1_tarski(A_33) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_4,plain,(
    ! [A_3,B_4,C_5] : k2_xboole_0(k2_tarski(A_3,B_4),k1_tarski(C_5)) = k1_enumset1(A_3,B_4,C_5) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_112,plain,(
    ! [D_63,F_68,A_66,G_62,C_64,E_67,B_65] : k2_xboole_0(k2_tarski(A_66,B_65),k3_enumset1(C_64,D_63,E_67,F_68,G_62)) = k5_enumset1(A_66,B_65,C_64,D_63,E_67,F_68,G_62) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_121,plain,(
    ! [A_66,B_65,A_33] : k5_enumset1(A_66,B_65,A_33,A_33,A_33,A_33,A_33) = k2_xboole_0(k2_tarski(A_66,B_65),k1_tarski(A_33)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_112])).

tff(c_125,plain,(
    ! [A_69,B_70,A_71] : k5_enumset1(A_69,B_70,A_71,A_71,A_71,A_71,A_71) = k1_enumset1(A_69,B_70,A_71) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_121])).

tff(c_14,plain,(
    ! [E_26,A_22,B_23,D_25,C_24] : k5_enumset1(A_22,A_22,A_22,B_23,C_24,D_25,E_26) = k3_enumset1(A_22,B_23,C_24,D_25,E_26) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_132,plain,(
    ! [A_71] : k3_enumset1(A_71,A_71,A_71,A_71,A_71) = k1_enumset1(A_71,A_71,A_71) ),
    inference(superposition,[status(thm),theory(equality)],[c_125,c_14])).

tff(c_141,plain,(
    ! [A_71] : k2_tarski(A_71,A_71) = k1_tarski(A_71) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_18,c_132])).

tff(c_12,plain,(
    ! [A_18,B_19,C_20,D_21] : k4_enumset1(A_18,A_18,A_18,B_19,C_20,D_21) = k2_enumset1(A_18,B_19,C_20,D_21) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_20,plain,(
    k4_enumset1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_1') != k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_21,plain,(
    k2_enumset1('#skF_1','#skF_1','#skF_1','#skF_1') != k1_tarski('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_20])).

tff(c_22,plain,(
    k2_tarski('#skF_1','#skF_1') != k1_tarski('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_21])).

tff(c_146,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:03:55 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.02/1.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.02/1.34  
% 2.02/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.02/1.34  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1
% 2.02/1.34  
% 2.02/1.34  %Foreground sorts:
% 2.02/1.34  
% 2.02/1.34  
% 2.02/1.34  %Background operators:
% 2.02/1.34  
% 2.02/1.34  
% 2.02/1.34  %Foreground operators:
% 2.02/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.02/1.34  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.02/1.34  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.02/1.34  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.02/1.34  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.02/1.34  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.02/1.34  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.02/1.34  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.02/1.34  tff('#skF_1', type, '#skF_1': $i).
% 2.02/1.34  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.02/1.34  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.02/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.02/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.02/1.34  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.02/1.34  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.02/1.34  
% 2.02/1.36  tff(f_33, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 2.02/1.36  tff(f_35, axiom, (![A, B]: (k2_enumset1(A, A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_enumset1)).
% 2.02/1.36  tff(f_43, axiom, (![A]: (k3_enumset1(A, A, A, A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_enumset1)).
% 2.02/1.36  tff(f_29, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k2_tarski(A, B), k1_tarski(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_enumset1)).
% 2.02/1.36  tff(f_31, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k2_tarski(A, B), k3_enumset1(C, D, E, F, G)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_enumset1)).
% 2.02/1.36  tff(f_39, axiom, (![A, B, C, D, E]: (k5_enumset1(A, A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_enumset1)).
% 2.02/1.36  tff(f_37, axiom, (![A, B, C, D]: (k4_enumset1(A, A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_enumset1)).
% 2.02/1.36  tff(f_46, negated_conjecture, ~(![A]: (k4_enumset1(A, A, A, A, A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_enumset1)).
% 2.02/1.36  tff(c_50, plain, (![A_39, B_40, C_41]: (k2_enumset1(A_39, A_39, B_40, C_41)=k1_enumset1(A_39, B_40, C_41))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.02/1.36  tff(c_10, plain, (![A_16, B_17]: (k2_enumset1(A_16, A_16, A_16, B_17)=k2_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.02/1.36  tff(c_57, plain, (![B_40, C_41]: (k1_enumset1(B_40, B_40, C_41)=k2_tarski(B_40, C_41))), inference(superposition, [status(thm), theory('equality')], [c_50, c_10])).
% 2.02/1.36  tff(c_18, plain, (![A_33]: (k3_enumset1(A_33, A_33, A_33, A_33, A_33)=k1_tarski(A_33))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.02/1.36  tff(c_4, plain, (![A_3, B_4, C_5]: (k2_xboole_0(k2_tarski(A_3, B_4), k1_tarski(C_5))=k1_enumset1(A_3, B_4, C_5))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.02/1.36  tff(c_112, plain, (![D_63, F_68, A_66, G_62, C_64, E_67, B_65]: (k2_xboole_0(k2_tarski(A_66, B_65), k3_enumset1(C_64, D_63, E_67, F_68, G_62))=k5_enumset1(A_66, B_65, C_64, D_63, E_67, F_68, G_62))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.02/1.36  tff(c_121, plain, (![A_66, B_65, A_33]: (k5_enumset1(A_66, B_65, A_33, A_33, A_33, A_33, A_33)=k2_xboole_0(k2_tarski(A_66, B_65), k1_tarski(A_33)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_112])).
% 2.02/1.36  tff(c_125, plain, (![A_69, B_70, A_71]: (k5_enumset1(A_69, B_70, A_71, A_71, A_71, A_71, A_71)=k1_enumset1(A_69, B_70, A_71))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_121])).
% 2.02/1.36  tff(c_14, plain, (![E_26, A_22, B_23, D_25, C_24]: (k5_enumset1(A_22, A_22, A_22, B_23, C_24, D_25, E_26)=k3_enumset1(A_22, B_23, C_24, D_25, E_26))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.02/1.36  tff(c_132, plain, (![A_71]: (k3_enumset1(A_71, A_71, A_71, A_71, A_71)=k1_enumset1(A_71, A_71, A_71))), inference(superposition, [status(thm), theory('equality')], [c_125, c_14])).
% 2.02/1.36  tff(c_141, plain, (![A_71]: (k2_tarski(A_71, A_71)=k1_tarski(A_71))), inference(demodulation, [status(thm), theory('equality')], [c_57, c_18, c_132])).
% 2.02/1.36  tff(c_12, plain, (![A_18, B_19, C_20, D_21]: (k4_enumset1(A_18, A_18, A_18, B_19, C_20, D_21)=k2_enumset1(A_18, B_19, C_20, D_21))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.02/1.36  tff(c_20, plain, (k4_enumset1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1')!=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.02/1.36  tff(c_21, plain, (k2_enumset1('#skF_1', '#skF_1', '#skF_1', '#skF_1')!=k1_tarski('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_20])).
% 2.02/1.36  tff(c_22, plain, (k2_tarski('#skF_1', '#skF_1')!=k1_tarski('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_21])).
% 2.02/1.36  tff(c_146, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_141, c_22])).
% 2.02/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.02/1.36  
% 2.02/1.36  Inference rules
% 2.02/1.36  ----------------------
% 2.02/1.36  #Ref     : 0
% 2.02/1.36  #Sup     : 27
% 2.02/1.36  #Fact    : 0
% 2.02/1.36  #Define  : 0
% 2.02/1.36  #Split   : 0
% 2.02/1.36  #Chain   : 0
% 2.02/1.36  #Close   : 0
% 2.02/1.36  
% 2.02/1.36  Ordering : KBO
% 2.02/1.36  
% 2.02/1.36  Simplification rules
% 2.02/1.36  ----------------------
% 2.02/1.36  #Subsume      : 0
% 2.02/1.36  #Demod        : 9
% 2.02/1.36  #Tautology    : 23
% 2.02/1.36  #SimpNegUnit  : 0
% 2.02/1.36  #BackRed      : 1
% 2.02/1.36  
% 2.02/1.36  #Partial instantiations: 0
% 2.02/1.36  #Strategies tried      : 1
% 2.02/1.36  
% 2.02/1.36  Timing (in seconds)
% 2.02/1.36  ----------------------
% 2.02/1.36  Preprocessing        : 0.37
% 2.02/1.36  Parsing              : 0.18
% 2.02/1.36  CNF conversion       : 0.02
% 2.02/1.36  Main loop            : 0.16
% 2.02/1.36  Inferencing          : 0.06
% 2.02/1.36  Reduction            : 0.06
% 2.02/1.36  Demodulation         : 0.05
% 2.02/1.36  BG Simplification    : 0.02
% 2.02/1.36  Subsumption          : 0.02
% 2.02/1.36  Abstraction          : 0.01
% 2.02/1.36  MUC search           : 0.00
% 2.02/1.36  Cooper               : 0.00
% 2.02/1.36  Total                : 0.58
% 2.02/1.36  Index Insertion      : 0.00
% 2.02/1.36  Index Deletion       : 0.00
% 2.02/1.36  Index Matching       : 0.00
% 2.02/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
