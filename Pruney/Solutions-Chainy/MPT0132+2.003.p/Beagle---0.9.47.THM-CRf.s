%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:41 EST 2020

% Result     : Theorem 1.97s
% Output     : CNFRefutation 2.24s
% Verified   : 
% Statistics : Number of formulae       :   37 (  46 expanded)
%              Number of leaves         :   20 (  25 expanded)
%              Depth                    :    8
%              Number of atoms          :   23 (  32 expanded)
%              Number of equality atoms :   22 (  31 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_35,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_tarski(A),k2_enumset1(B,C,D,E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k2_tarski(A,B),k2_tarski(C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k1_tarski(A),k2_tarski(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_38,negated_conjecture,(
    ~ ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k2_tarski(A,B),k1_enumset1(C,D,E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_enumset1)).

tff(c_10,plain,(
    ! [E_17,A_13,B_14,C_15,D_16] : k2_xboole_0(k1_tarski(A_13),k2_enumset1(B_14,C_15,D_16,E_17)) = k3_enumset1(A_13,B_14,C_15,D_16,E_17) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_4,plain,(
    ! [A_4,B_5,C_6,D_7] : k2_xboole_0(k2_tarski(A_4,B_5),k2_tarski(C_6,D_7)) = k2_enumset1(A_4,B_5,C_6,D_7) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_8,plain,(
    ! [A_10,B_11,C_12] : k2_xboole_0(k1_tarski(A_10),k2_tarski(B_11,C_12)) = k1_enumset1(A_10,B_11,C_12) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_31,plain,(
    ! [A_23,B_24,C_25] : k2_xboole_0(k2_xboole_0(A_23,B_24),C_25) = k2_xboole_0(A_23,k2_xboole_0(B_24,C_25)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_135,plain,(
    ! [A_45,B_46,C_47,C_48] : k2_xboole_0(k1_tarski(A_45),k2_xboole_0(k2_tarski(B_46,C_47),C_48)) = k2_xboole_0(k1_enumset1(A_45,B_46,C_47),C_48) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_31])).

tff(c_153,plain,(
    ! [B_5,D_7,A_4,A_45,C_6] : k2_xboole_0(k1_enumset1(A_45,A_4,B_5),k2_tarski(C_6,D_7)) = k2_xboole_0(k1_tarski(A_45),k2_enumset1(A_4,B_5,C_6,D_7)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_135])).

tff(c_158,plain,(
    ! [B_5,D_7,A_4,A_45,C_6] : k2_xboole_0(k1_enumset1(A_45,A_4,B_5),k2_tarski(C_6,D_7)) = k3_enumset1(A_45,A_4,B_5,C_6,D_7) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_153])).

tff(c_6,plain,(
    ! [A_8,B_9] : k2_xboole_0(k1_tarski(A_8),k1_tarski(B_9)) = k2_tarski(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_66,plain,(
    ! [A_30,B_31,C_32] : k2_xboole_0(k1_tarski(A_30),k2_xboole_0(k1_tarski(B_31),C_32)) = k2_xboole_0(k2_tarski(A_30,B_31),C_32) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_31])).

tff(c_87,plain,(
    ! [A_30,A_8,B_9] : k2_xboole_0(k2_tarski(A_30,A_8),k1_tarski(B_9)) = k2_xboole_0(k1_tarski(A_30),k2_tarski(A_8,B_9)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_66])).

tff(c_93,plain,(
    ! [A_33,A_34,B_35] : k2_xboole_0(k2_tarski(A_33,A_34),k1_tarski(B_35)) = k1_enumset1(A_33,A_34,B_35) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_87])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] : k2_xboole_0(k2_xboole_0(A_1,B_2),C_3) = k2_xboole_0(A_1,k2_xboole_0(B_2,C_3)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_183,plain,(
    ! [A_58,A_59,B_60,C_61] : k2_xboole_0(k2_tarski(A_58,A_59),k2_xboole_0(k1_tarski(B_60),C_61)) = k2_xboole_0(k1_enumset1(A_58,A_59,B_60),C_61) ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_2])).

tff(c_210,plain,(
    ! [B_11,A_10,A_58,C_12,A_59] : k2_xboole_0(k1_enumset1(A_58,A_59,A_10),k2_tarski(B_11,C_12)) = k2_xboole_0(k2_tarski(A_58,A_59),k1_enumset1(A_10,B_11,C_12)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_183])).

tff(c_217,plain,(
    ! [B_11,A_10,A_58,C_12,A_59] : k2_xboole_0(k2_tarski(A_58,A_59),k1_enumset1(A_10,B_11,C_12)) = k3_enumset1(A_58,A_59,A_10,B_11,C_12) ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_210])).

tff(c_12,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_2'),k1_enumset1('#skF_3','#skF_4','#skF_5')) != k3_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_221,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_217,c_12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:41:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.97/1.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.24/1.33  
% 2.24/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.24/1.33  %$ k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.24/1.33  
% 2.24/1.33  %Foreground sorts:
% 2.24/1.33  
% 2.24/1.33  
% 2.24/1.33  %Background operators:
% 2.24/1.33  
% 2.24/1.33  
% 2.24/1.33  %Foreground operators:
% 2.24/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.24/1.33  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.24/1.33  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.24/1.33  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.24/1.33  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.24/1.33  tff('#skF_5', type, '#skF_5': $i).
% 2.24/1.33  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.24/1.33  tff('#skF_2', type, '#skF_2': $i).
% 2.24/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.24/1.33  tff('#skF_1', type, '#skF_1': $i).
% 2.24/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.24/1.33  tff('#skF_4', type, '#skF_4': $i).
% 2.24/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.24/1.33  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.24/1.33  
% 2.24/1.34  tff(f_35, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_tarski(A), k2_enumset1(B, C, D, E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_enumset1)).
% 2.24/1.34  tff(f_29, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k2_tarski(A, B), k2_tarski(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l53_enumset1)).
% 2.24/1.34  tff(f_33, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k1_tarski(A), k2_tarski(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_enumset1)).
% 2.24/1.34  tff(f_27, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 2.24/1.34  tff(f_31, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 2.24/1.34  tff(f_38, negated_conjecture, ~(![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k2_tarski(A, B), k1_enumset1(C, D, E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_enumset1)).
% 2.24/1.34  tff(c_10, plain, (![E_17, A_13, B_14, C_15, D_16]: (k2_xboole_0(k1_tarski(A_13), k2_enumset1(B_14, C_15, D_16, E_17))=k3_enumset1(A_13, B_14, C_15, D_16, E_17))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.24/1.34  tff(c_4, plain, (![A_4, B_5, C_6, D_7]: (k2_xboole_0(k2_tarski(A_4, B_5), k2_tarski(C_6, D_7))=k2_enumset1(A_4, B_5, C_6, D_7))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.24/1.34  tff(c_8, plain, (![A_10, B_11, C_12]: (k2_xboole_0(k1_tarski(A_10), k2_tarski(B_11, C_12))=k1_enumset1(A_10, B_11, C_12))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.24/1.34  tff(c_31, plain, (![A_23, B_24, C_25]: (k2_xboole_0(k2_xboole_0(A_23, B_24), C_25)=k2_xboole_0(A_23, k2_xboole_0(B_24, C_25)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.24/1.34  tff(c_135, plain, (![A_45, B_46, C_47, C_48]: (k2_xboole_0(k1_tarski(A_45), k2_xboole_0(k2_tarski(B_46, C_47), C_48))=k2_xboole_0(k1_enumset1(A_45, B_46, C_47), C_48))), inference(superposition, [status(thm), theory('equality')], [c_8, c_31])).
% 2.24/1.34  tff(c_153, plain, (![B_5, D_7, A_4, A_45, C_6]: (k2_xboole_0(k1_enumset1(A_45, A_4, B_5), k2_tarski(C_6, D_7))=k2_xboole_0(k1_tarski(A_45), k2_enumset1(A_4, B_5, C_6, D_7)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_135])).
% 2.24/1.34  tff(c_158, plain, (![B_5, D_7, A_4, A_45, C_6]: (k2_xboole_0(k1_enumset1(A_45, A_4, B_5), k2_tarski(C_6, D_7))=k3_enumset1(A_45, A_4, B_5, C_6, D_7))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_153])).
% 2.24/1.34  tff(c_6, plain, (![A_8, B_9]: (k2_xboole_0(k1_tarski(A_8), k1_tarski(B_9))=k2_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.24/1.34  tff(c_66, plain, (![A_30, B_31, C_32]: (k2_xboole_0(k1_tarski(A_30), k2_xboole_0(k1_tarski(B_31), C_32))=k2_xboole_0(k2_tarski(A_30, B_31), C_32))), inference(superposition, [status(thm), theory('equality')], [c_6, c_31])).
% 2.24/1.34  tff(c_87, plain, (![A_30, A_8, B_9]: (k2_xboole_0(k2_tarski(A_30, A_8), k1_tarski(B_9))=k2_xboole_0(k1_tarski(A_30), k2_tarski(A_8, B_9)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_66])).
% 2.24/1.34  tff(c_93, plain, (![A_33, A_34, B_35]: (k2_xboole_0(k2_tarski(A_33, A_34), k1_tarski(B_35))=k1_enumset1(A_33, A_34, B_35))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_87])).
% 2.24/1.34  tff(c_2, plain, (![A_1, B_2, C_3]: (k2_xboole_0(k2_xboole_0(A_1, B_2), C_3)=k2_xboole_0(A_1, k2_xboole_0(B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.24/1.34  tff(c_183, plain, (![A_58, A_59, B_60, C_61]: (k2_xboole_0(k2_tarski(A_58, A_59), k2_xboole_0(k1_tarski(B_60), C_61))=k2_xboole_0(k1_enumset1(A_58, A_59, B_60), C_61))), inference(superposition, [status(thm), theory('equality')], [c_93, c_2])).
% 2.24/1.34  tff(c_210, plain, (![B_11, A_10, A_58, C_12, A_59]: (k2_xboole_0(k1_enumset1(A_58, A_59, A_10), k2_tarski(B_11, C_12))=k2_xboole_0(k2_tarski(A_58, A_59), k1_enumset1(A_10, B_11, C_12)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_183])).
% 2.24/1.34  tff(c_217, plain, (![B_11, A_10, A_58, C_12, A_59]: (k2_xboole_0(k2_tarski(A_58, A_59), k1_enumset1(A_10, B_11, C_12))=k3_enumset1(A_58, A_59, A_10, B_11, C_12))), inference(demodulation, [status(thm), theory('equality')], [c_158, c_210])).
% 2.24/1.34  tff(c_12, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), k1_enumset1('#skF_3', '#skF_4', '#skF_5'))!=k3_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.24/1.34  tff(c_221, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_217, c_12])).
% 2.24/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.24/1.34  
% 2.24/1.34  Inference rules
% 2.24/1.34  ----------------------
% 2.24/1.34  #Ref     : 0
% 2.24/1.34  #Sup     : 53
% 2.24/1.34  #Fact    : 0
% 2.24/1.34  #Define  : 0
% 2.24/1.34  #Split   : 0
% 2.24/1.34  #Chain   : 0
% 2.24/1.34  #Close   : 0
% 2.24/1.34  
% 2.24/1.34  Ordering : KBO
% 2.24/1.34  
% 2.24/1.34  Simplification rules
% 2.24/1.34  ----------------------
% 2.24/1.34  #Subsume      : 0
% 2.24/1.34  #Demod        : 23
% 2.24/1.34  #Tautology    : 30
% 2.24/1.34  #SimpNegUnit  : 0
% 2.24/1.34  #BackRed      : 1
% 2.24/1.34  
% 2.24/1.34  #Partial instantiations: 0
% 2.24/1.34  #Strategies tried      : 1
% 2.24/1.34  
% 2.24/1.34  Timing (in seconds)
% 2.24/1.34  ----------------------
% 2.24/1.35  Preprocessing        : 0.34
% 2.24/1.35  Parsing              : 0.18
% 2.24/1.35  CNF conversion       : 0.02
% 2.24/1.35  Main loop            : 0.20
% 2.24/1.35  Inferencing          : 0.09
% 2.24/1.35  Reduction            : 0.06
% 2.24/1.35  Demodulation         : 0.05
% 2.24/1.35  BG Simplification    : 0.02
% 2.24/1.35  Subsumption          : 0.02
% 2.24/1.35  Abstraction          : 0.01
% 2.24/1.35  MUC search           : 0.00
% 2.24/1.35  Cooper               : 0.00
% 2.24/1.35  Total                : 0.57
% 2.24/1.35  Index Insertion      : 0.00
% 2.24/1.35  Index Deletion       : 0.00
% 2.24/1.35  Index Matching       : 0.00
% 2.24/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
