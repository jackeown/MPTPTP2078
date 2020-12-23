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
% DateTime   : Thu Dec  3 09:45:45 EST 2020

% Result     : Theorem 15.72s
% Output     : CNFRefutation 15.72s
% Verified   : 
% Statistics : Number of formulae       :   40 (  43 expanded)
%              Number of leaves         :   26 (  28 expanded)
%              Depth                    :    7
%              Number of atoms          :   20 (  23 expanded)
%              Number of equality atoms :   19 (  22 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k4_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_3 > #skF_10 > #skF_5 > #skF_2 > #skF_6 > #skF_9 > #skF_8 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_57,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k1_enumset1(A,B,C),k1_enumset1(D,E,F)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l62_enumset1)).

tff(f_61,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k2_tarski(A,B),k1_tarski(C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_enumset1)).

tff(f_59,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_63,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_66,negated_conjecture,(
    ~ ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k2_enumset1(A,B,C,D),k2_tarski(E,F)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_enumset1)).

tff(c_46,plain,(
    ! [A_24,B_25,F_29,D_27,C_26,E_28] : k2_xboole_0(k1_enumset1(A_24,B_25,C_26),k1_enumset1(D_27,E_28,F_29)) = k4_enumset1(A_24,B_25,C_26,D_27,E_28,F_29) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_50,plain,(
    ! [A_32,B_33,C_34] : k2_xboole_0(k2_tarski(A_32,B_33),k1_tarski(C_34)) = k1_enumset1(A_32,B_33,C_34) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_48,plain,(
    ! [A_30,B_31] : k2_xboole_0(k1_tarski(A_30),k1_tarski(B_31)) = k2_tarski(A_30,B_31) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_144,plain,(
    ! [A_59,B_60,C_61] : k2_xboole_0(k2_xboole_0(A_59,B_60),C_61) = k2_xboole_0(A_59,k2_xboole_0(B_60,C_61)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_950,plain,(
    ! [A_1070,B_1071,C_1072] : k2_xboole_0(k1_tarski(A_1070),k2_xboole_0(k1_tarski(B_1071),C_1072)) = k2_xboole_0(k2_tarski(A_1070,B_1071),C_1072) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_144])).

tff(c_1101,plain,(
    ! [A_1070,A_30,B_31] : k2_xboole_0(k2_tarski(A_1070,A_30),k1_tarski(B_31)) = k2_xboole_0(k1_tarski(A_1070),k2_tarski(A_30,B_31)) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_950])).

tff(c_1124,plain,(
    ! [A_1070,A_30,B_31] : k2_xboole_0(k1_tarski(A_1070),k2_tarski(A_30,B_31)) = k1_enumset1(A_1070,A_30,B_31) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_1101])).

tff(c_656,plain,(
    ! [A_654,B_655,C_656,D_657] : k2_xboole_0(k1_enumset1(A_654,B_655,C_656),k1_tarski(D_657)) = k2_enumset1(A_654,B_655,C_656,D_657) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_6,plain,(
    ! [A_7,B_8,C_9] : k2_xboole_0(k2_xboole_0(A_7,B_8),C_9) = k2_xboole_0(A_7,k2_xboole_0(B_8,C_9)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8753,plain,(
    ! [B_4104,C_4101,D_4102,C_4100,A_4103] : k2_xboole_0(k1_enumset1(A_4103,B_4104,C_4100),k2_xboole_0(k1_tarski(D_4102),C_4101)) = k2_xboole_0(k2_enumset1(A_4103,B_4104,C_4100,D_4102),C_4101) ),
    inference(superposition,[status(thm),theory(equality)],[c_656,c_6])).

tff(c_8838,plain,(
    ! [B_4104,C_4100,A_30,A_4103,A_1070,B_31] : k2_xboole_0(k2_enumset1(A_4103,B_4104,C_4100,A_1070),k2_tarski(A_30,B_31)) = k2_xboole_0(k1_enumset1(A_4103,B_4104,C_4100),k1_enumset1(A_1070,A_30,B_31)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1124,c_8753])).

tff(c_8946,plain,(
    ! [B_4104,C_4100,A_30,A_4103,A_1070,B_31] : k2_xboole_0(k2_enumset1(A_4103,B_4104,C_4100,A_1070),k2_tarski(A_30,B_31)) = k4_enumset1(A_4103,B_4104,C_4100,A_1070,A_30,B_31) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_8838])).

tff(c_54,plain,(
    k2_xboole_0(k2_enumset1('#skF_5','#skF_6','#skF_7','#skF_8'),k2_tarski('#skF_9','#skF_10')) != k4_enumset1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_9','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_51595,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8946,c_54])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:04:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 15.72/8.12  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.72/8.12  
% 15.72/8.12  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.72/8.12  %$ r2_hidden > k4_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_3 > #skF_10 > #skF_5 > #skF_2 > #skF_6 > #skF_9 > #skF_8 > #skF_1 > #skF_4
% 15.72/8.12  
% 15.72/8.12  %Foreground sorts:
% 15.72/8.12  
% 15.72/8.12  
% 15.72/8.12  %Background operators:
% 15.72/8.12  
% 15.72/8.12  
% 15.72/8.12  %Foreground operators:
% 15.72/8.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 15.72/8.12  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 15.72/8.12  tff(k1_tarski, type, k1_tarski: $i > $i).
% 15.72/8.12  tff('#skF_7', type, '#skF_7': $i).
% 15.72/8.12  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 15.72/8.12  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 15.72/8.12  tff('#skF_10', type, '#skF_10': $i).
% 15.72/8.12  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 15.72/8.12  tff('#skF_5', type, '#skF_5': $i).
% 15.72/8.12  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 15.72/8.12  tff('#skF_6', type, '#skF_6': $i).
% 15.72/8.12  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 15.72/8.12  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 15.72/8.12  tff('#skF_9', type, '#skF_9': $i).
% 15.72/8.12  tff('#skF_8', type, '#skF_8': $i).
% 15.72/8.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 15.72/8.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 15.72/8.12  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 15.72/8.12  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 15.72/8.12  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 15.72/8.12  
% 15.72/8.13  tff(f_57, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k1_enumset1(A, B, C), k1_enumset1(D, E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l62_enumset1)).
% 15.72/8.13  tff(f_61, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k2_tarski(A, B), k1_tarski(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_enumset1)).
% 15.72/8.13  tff(f_59, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 15.72/8.13  tff(f_31, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 15.72/8.13  tff(f_63, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_enumset1)).
% 15.72/8.13  tff(f_66, negated_conjecture, ~(![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k2_enumset1(A, B, C, D), k2_tarski(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t54_enumset1)).
% 15.72/8.13  tff(c_46, plain, (![A_24, B_25, F_29, D_27, C_26, E_28]: (k2_xboole_0(k1_enumset1(A_24, B_25, C_26), k1_enumset1(D_27, E_28, F_29))=k4_enumset1(A_24, B_25, C_26, D_27, E_28, F_29))), inference(cnfTransformation, [status(thm)], [f_57])).
% 15.72/8.13  tff(c_50, plain, (![A_32, B_33, C_34]: (k2_xboole_0(k2_tarski(A_32, B_33), k1_tarski(C_34))=k1_enumset1(A_32, B_33, C_34))), inference(cnfTransformation, [status(thm)], [f_61])).
% 15.72/8.13  tff(c_48, plain, (![A_30, B_31]: (k2_xboole_0(k1_tarski(A_30), k1_tarski(B_31))=k2_tarski(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_59])).
% 15.72/8.13  tff(c_144, plain, (![A_59, B_60, C_61]: (k2_xboole_0(k2_xboole_0(A_59, B_60), C_61)=k2_xboole_0(A_59, k2_xboole_0(B_60, C_61)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 15.72/8.13  tff(c_950, plain, (![A_1070, B_1071, C_1072]: (k2_xboole_0(k1_tarski(A_1070), k2_xboole_0(k1_tarski(B_1071), C_1072))=k2_xboole_0(k2_tarski(A_1070, B_1071), C_1072))), inference(superposition, [status(thm), theory('equality')], [c_48, c_144])).
% 15.72/8.13  tff(c_1101, plain, (![A_1070, A_30, B_31]: (k2_xboole_0(k2_tarski(A_1070, A_30), k1_tarski(B_31))=k2_xboole_0(k1_tarski(A_1070), k2_tarski(A_30, B_31)))), inference(superposition, [status(thm), theory('equality')], [c_48, c_950])).
% 15.72/8.13  tff(c_1124, plain, (![A_1070, A_30, B_31]: (k2_xboole_0(k1_tarski(A_1070), k2_tarski(A_30, B_31))=k1_enumset1(A_1070, A_30, B_31))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_1101])).
% 15.72/8.13  tff(c_656, plain, (![A_654, B_655, C_656, D_657]: (k2_xboole_0(k1_enumset1(A_654, B_655, C_656), k1_tarski(D_657))=k2_enumset1(A_654, B_655, C_656, D_657))), inference(cnfTransformation, [status(thm)], [f_63])).
% 15.72/8.13  tff(c_6, plain, (![A_7, B_8, C_9]: (k2_xboole_0(k2_xboole_0(A_7, B_8), C_9)=k2_xboole_0(A_7, k2_xboole_0(B_8, C_9)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 15.72/8.13  tff(c_8753, plain, (![B_4104, C_4101, D_4102, C_4100, A_4103]: (k2_xboole_0(k1_enumset1(A_4103, B_4104, C_4100), k2_xboole_0(k1_tarski(D_4102), C_4101))=k2_xboole_0(k2_enumset1(A_4103, B_4104, C_4100, D_4102), C_4101))), inference(superposition, [status(thm), theory('equality')], [c_656, c_6])).
% 15.72/8.13  tff(c_8838, plain, (![B_4104, C_4100, A_30, A_4103, A_1070, B_31]: (k2_xboole_0(k2_enumset1(A_4103, B_4104, C_4100, A_1070), k2_tarski(A_30, B_31))=k2_xboole_0(k1_enumset1(A_4103, B_4104, C_4100), k1_enumset1(A_1070, A_30, B_31)))), inference(superposition, [status(thm), theory('equality')], [c_1124, c_8753])).
% 15.72/8.13  tff(c_8946, plain, (![B_4104, C_4100, A_30, A_4103, A_1070, B_31]: (k2_xboole_0(k2_enumset1(A_4103, B_4104, C_4100, A_1070), k2_tarski(A_30, B_31))=k4_enumset1(A_4103, B_4104, C_4100, A_1070, A_30, B_31))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_8838])).
% 15.72/8.13  tff(c_54, plain, (k2_xboole_0(k2_enumset1('#skF_5', '#skF_6', '#skF_7', '#skF_8'), k2_tarski('#skF_9', '#skF_10'))!=k4_enumset1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9', '#skF_10')), inference(cnfTransformation, [status(thm)], [f_66])).
% 15.72/8.13  tff(c_51595, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8946, c_54])).
% 15.72/8.13  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.72/8.13  
% 15.72/8.13  Inference rules
% 15.72/8.13  ----------------------
% 15.72/8.13  #Ref     : 0
% 15.72/8.13  #Sup     : 10751
% 15.72/8.13  #Fact    : 6
% 15.72/8.13  #Define  : 0
% 15.72/8.13  #Split   : 6
% 15.72/8.13  #Chain   : 0
% 15.72/8.13  #Close   : 0
% 15.72/8.13  
% 15.72/8.13  Ordering : KBO
% 15.72/8.13  
% 15.72/8.13  Simplification rules
% 15.72/8.13  ----------------------
% 15.72/8.13  #Subsume      : 440
% 15.72/8.13  #Demod        : 22975
% 15.72/8.13  #Tautology    : 8059
% 15.72/8.13  #SimpNegUnit  : 0
% 15.72/8.13  #BackRed      : 4
% 15.72/8.13  
% 15.72/8.13  #Partial instantiations: 4320
% 15.72/8.13  #Strategies tried      : 1
% 15.72/8.13  
% 15.72/8.13  Timing (in seconds)
% 15.72/8.13  ----------------------
% 15.72/8.14  Preprocessing        : 0.35
% 15.72/8.14  Parsing              : 0.18
% 15.72/8.14  CNF conversion       : 0.03
% 15.72/8.14  Main loop            : 6.93
% 15.72/8.14  Inferencing          : 1.78
% 15.72/8.14  Reduction            : 3.96
% 15.72/8.14  Demodulation         : 3.62
% 15.72/8.14  BG Simplification    : 0.15
% 15.72/8.14  Subsumption          : 0.82
% 15.72/8.14  Abstraction          : 0.36
% 15.72/8.14  MUC search           : 0.00
% 15.72/8.14  Cooper               : 0.00
% 15.72/8.14  Total                : 7.30
% 15.72/8.14  Index Insertion      : 0.00
% 15.72/8.14  Index Deletion       : 0.00
% 15.72/8.14  Index Matching       : 0.00
% 15.72/8.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
