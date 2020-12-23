%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:46 EST 2020

% Result     : Theorem 2.32s
% Output     : CNFRefutation 2.32s
% Verified   : 
% Statistics : Number of formulae       :   30 (  30 expanded)
%              Number of leaves         :   21 (  21 expanded)
%              Depth                    :    5
%              Number of atoms          :   14 (  14 expanded)
%              Number of equality atoms :   13 (  13 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_41,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k2_tarski(A,B),k2_enumset1(C,D,E,F)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k2_tarski(A,B),k1_enumset1(C,D,E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_46,negated_conjecture,(
    ~ ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k1_tarski(F)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_enumset1)).

tff(c_16,plain,(
    ! [C_29,D_30,B_28,F_32,A_27,E_31] : k2_xboole_0(k2_tarski(A_27,B_28),k2_enumset1(C_29,D_30,E_31,F_32)) = k4_enumset1(A_27,B_28,C_29,D_30,E_31,F_32) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_12,plain,(
    ! [A_18,B_19,C_20,D_21] : k2_xboole_0(k1_enumset1(A_18,B_19,C_20),k1_tarski(D_21)) = k2_enumset1(A_18,B_19,C_20,D_21) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_152,plain,(
    ! [E_72,D_73,B_74,A_70,C_71] : k2_xboole_0(k2_tarski(A_70,B_74),k1_enumset1(C_71,D_73,E_72)) = k3_enumset1(A_70,B_74,C_71,D_73,E_72) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] : k2_xboole_0(k2_xboole_0(A_1,B_2),C_3) = k2_xboole_0(A_1,k2_xboole_0(B_2,C_3)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_403,plain,(
    ! [B_129,A_127,D_126,C_130,C_131,E_128] : k2_xboole_0(k2_tarski(A_127,B_129),k2_xboole_0(k1_enumset1(C_130,D_126,E_128),C_131)) = k2_xboole_0(k3_enumset1(A_127,B_129,C_130,D_126,E_128),C_131) ),
    inference(superposition,[status(thm),theory(equality)],[c_152,c_2])).

tff(c_430,plain,(
    ! [B_129,D_21,A_127,A_18,C_20,B_19] : k2_xboole_0(k3_enumset1(A_127,B_129,A_18,B_19,C_20),k1_tarski(D_21)) = k2_xboole_0(k2_tarski(A_127,B_129),k2_enumset1(A_18,B_19,C_20,D_21)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_403])).

tff(c_434,plain,(
    ! [B_129,D_21,A_127,A_18,C_20,B_19] : k2_xboole_0(k3_enumset1(A_127,B_129,A_18,B_19,C_20),k1_tarski(D_21)) = k4_enumset1(A_127,B_129,A_18,B_19,C_20,D_21) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_430])).

tff(c_20,plain,(
    k2_xboole_0(k3_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5'),k1_tarski('#skF_6')) != k4_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_478,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_434,c_20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:43:23 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.32/1.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.32/1.32  
% 2.32/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.32/1.32  %$ k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.32/1.32  
% 2.32/1.32  %Foreground sorts:
% 2.32/1.32  
% 2.32/1.32  
% 2.32/1.32  %Background operators:
% 2.32/1.32  
% 2.32/1.32  
% 2.32/1.32  %Foreground operators:
% 2.32/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.32/1.32  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.32/1.32  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.32/1.32  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.32/1.32  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.32/1.32  tff('#skF_5', type, '#skF_5': $i).
% 2.32/1.32  tff('#skF_6', type, '#skF_6': $i).
% 2.32/1.32  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.32/1.32  tff('#skF_2', type, '#skF_2': $i).
% 2.32/1.32  tff('#skF_3', type, '#skF_3': $i).
% 2.32/1.32  tff('#skF_1', type, '#skF_1': $i).
% 2.32/1.32  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.32/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.32/1.32  tff('#skF_4', type, '#skF_4': $i).
% 2.32/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.32/1.32  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.32/1.32  
% 2.32/1.33  tff(f_41, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k2_tarski(A, B), k2_enumset1(C, D, E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_enumset1)).
% 2.32/1.33  tff(f_37, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_enumset1)).
% 2.32/1.33  tff(f_39, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k2_tarski(A, B), k1_enumset1(C, D, E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_enumset1)).
% 2.32/1.33  tff(f_27, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 2.32/1.33  tff(f_46, negated_conjecture, ~(![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k1_tarski(F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_enumset1)).
% 2.32/1.33  tff(c_16, plain, (![C_29, D_30, B_28, F_32, A_27, E_31]: (k2_xboole_0(k2_tarski(A_27, B_28), k2_enumset1(C_29, D_30, E_31, F_32))=k4_enumset1(A_27, B_28, C_29, D_30, E_31, F_32))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.32/1.33  tff(c_12, plain, (![A_18, B_19, C_20, D_21]: (k2_xboole_0(k1_enumset1(A_18, B_19, C_20), k1_tarski(D_21))=k2_enumset1(A_18, B_19, C_20, D_21))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.32/1.33  tff(c_152, plain, (![E_72, D_73, B_74, A_70, C_71]: (k2_xboole_0(k2_tarski(A_70, B_74), k1_enumset1(C_71, D_73, E_72))=k3_enumset1(A_70, B_74, C_71, D_73, E_72))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.32/1.33  tff(c_2, plain, (![A_1, B_2, C_3]: (k2_xboole_0(k2_xboole_0(A_1, B_2), C_3)=k2_xboole_0(A_1, k2_xboole_0(B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.32/1.33  tff(c_403, plain, (![B_129, A_127, D_126, C_130, C_131, E_128]: (k2_xboole_0(k2_tarski(A_127, B_129), k2_xboole_0(k1_enumset1(C_130, D_126, E_128), C_131))=k2_xboole_0(k3_enumset1(A_127, B_129, C_130, D_126, E_128), C_131))), inference(superposition, [status(thm), theory('equality')], [c_152, c_2])).
% 2.32/1.33  tff(c_430, plain, (![B_129, D_21, A_127, A_18, C_20, B_19]: (k2_xboole_0(k3_enumset1(A_127, B_129, A_18, B_19, C_20), k1_tarski(D_21))=k2_xboole_0(k2_tarski(A_127, B_129), k2_enumset1(A_18, B_19, C_20, D_21)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_403])).
% 2.32/1.33  tff(c_434, plain, (![B_129, D_21, A_127, A_18, C_20, B_19]: (k2_xboole_0(k3_enumset1(A_127, B_129, A_18, B_19, C_20), k1_tarski(D_21))=k4_enumset1(A_127, B_129, A_18, B_19, C_20, D_21))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_430])).
% 2.32/1.33  tff(c_20, plain, (k2_xboole_0(k3_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), k1_tarski('#skF_6'))!=k4_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.32/1.33  tff(c_478, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_434, c_20])).
% 2.32/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.32/1.33  
% 2.32/1.33  Inference rules
% 2.32/1.33  ----------------------
% 2.32/1.33  #Ref     : 0
% 2.32/1.33  #Sup     : 121
% 2.32/1.33  #Fact    : 0
% 2.32/1.33  #Define  : 0
% 2.32/1.33  #Split   : 0
% 2.32/1.33  #Chain   : 0
% 2.32/1.33  #Close   : 0
% 2.32/1.33  
% 2.32/1.33  Ordering : KBO
% 2.32/1.33  
% 2.32/1.33  Simplification rules
% 2.32/1.33  ----------------------
% 2.32/1.33  #Subsume      : 0
% 2.32/1.33  #Demod        : 56
% 2.32/1.33  #Tautology    : 63
% 2.32/1.33  #SimpNegUnit  : 0
% 2.32/1.33  #BackRed      : 1
% 2.32/1.33  
% 2.32/1.33  #Partial instantiations: 0
% 2.32/1.33  #Strategies tried      : 1
% 2.32/1.33  
% 2.32/1.33  Timing (in seconds)
% 2.32/1.33  ----------------------
% 2.64/1.33  Preprocessing        : 0.28
% 2.64/1.33  Parsing              : 0.15
% 2.64/1.33  CNF conversion       : 0.02
% 2.64/1.33  Main loop            : 0.30
% 2.64/1.33  Inferencing          : 0.14
% 2.64/1.33  Reduction            : 0.09
% 2.64/1.33  Demodulation         : 0.08
% 2.64/1.33  BG Simplification    : 0.02
% 2.64/1.33  Subsumption          : 0.03
% 2.64/1.33  Abstraction          : 0.02
% 2.64/1.33  MUC search           : 0.00
% 2.64/1.33  Cooper               : 0.00
% 2.64/1.33  Total                : 0.60
% 2.64/1.33  Index Insertion      : 0.00
% 2.64/1.33  Index Deletion       : 0.00
% 2.64/1.33  Index Matching       : 0.00
% 2.64/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
