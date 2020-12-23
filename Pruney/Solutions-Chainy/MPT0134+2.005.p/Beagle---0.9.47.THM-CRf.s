%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:43 EST 2020

% Result     : Theorem 2.17s
% Output     : CNFRefutation 2.27s
% Verified   : 
% Statistics : Number of formulae       :   30 (  30 expanded)
%              Number of leaves         :   21 (  21 expanded)
%              Depth                    :    5
%              Number of atoms          :   14 (  14 expanded)
%              Number of equality atoms :   13 (  13 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_37,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_enumset1(A,B,C),k2_tarski(D,E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_enumset1)).

tff(f_31,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_40,negated_conjecture,(
    ~ ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k2_enumset1(A,B,C,D),k1_tarski(E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_enumset1)).

tff(c_12,plain,(
    ! [B_16,A_15,D_18,E_19,C_17] : k2_xboole_0(k1_enumset1(A_15,B_16,C_17),k2_tarski(D_18,E_19)) = k3_enumset1(A_15,B_16,C_17,D_18,E_19) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_6,plain,(
    ! [A_6,B_7] : k2_xboole_0(k1_tarski(A_6),k1_tarski(B_7)) = k2_tarski(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_65,plain,(
    ! [A_30,B_31,C_32,D_33] : k2_xboole_0(k1_enumset1(A_30,B_31,C_32),k1_tarski(D_33)) = k2_enumset1(A_30,B_31,C_32,D_33) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] : k2_xboole_0(k2_xboole_0(A_1,B_2),C_3) = k2_xboole_0(A_1,k2_xboole_0(B_2,C_3)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_245,plain,(
    ! [C_74,B_72,D_75,C_71,A_73] : k2_xboole_0(k1_enumset1(A_73,B_72,C_71),k2_xboole_0(k1_tarski(D_75),C_74)) = k2_xboole_0(k2_enumset1(A_73,B_72,C_71,D_75),C_74) ),
    inference(superposition,[status(thm),theory(equality)],[c_65,c_2])).

tff(c_272,plain,(
    ! [B_7,B_72,C_71,A_73,A_6] : k2_xboole_0(k2_enumset1(A_73,B_72,C_71,A_6),k1_tarski(B_7)) = k2_xboole_0(k1_enumset1(A_73,B_72,C_71),k2_tarski(A_6,B_7)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_245])).

tff(c_276,plain,(
    ! [B_7,B_72,C_71,A_73,A_6] : k2_xboole_0(k2_enumset1(A_73,B_72,C_71,A_6),k1_tarski(B_7)) = k3_enumset1(A_73,B_72,C_71,A_6,B_7) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_272])).

tff(c_14,plain,(
    k2_xboole_0(k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4'),k1_tarski('#skF_5')) != k3_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_279,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_276,c_14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:55:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.17/1.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.17/1.24  
% 2.17/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.17/1.25  %$ k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.17/1.25  
% 2.17/1.25  %Foreground sorts:
% 2.17/1.25  
% 2.17/1.25  
% 2.17/1.25  %Background operators:
% 2.17/1.25  
% 2.17/1.25  
% 2.17/1.25  %Foreground operators:
% 2.17/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.17/1.25  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.17/1.25  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.17/1.25  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.17/1.25  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.17/1.25  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.17/1.25  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.17/1.25  tff('#skF_5', type, '#skF_5': $i).
% 2.17/1.25  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.17/1.25  tff('#skF_2', type, '#skF_2': $i).
% 2.17/1.25  tff('#skF_3', type, '#skF_3': $i).
% 2.17/1.25  tff('#skF_1', type, '#skF_1': $i).
% 2.17/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.17/1.25  tff('#skF_4', type, '#skF_4': $i).
% 2.17/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.17/1.25  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.17/1.25  
% 2.27/1.26  tff(f_37, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_enumset1(A, B, C), k2_tarski(D, E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_enumset1)).
% 2.27/1.26  tff(f_31, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 2.27/1.26  tff(f_35, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_enumset1)).
% 2.27/1.26  tff(f_27, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 2.27/1.26  tff(f_40, negated_conjecture, ~(![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k2_enumset1(A, B, C, D), k1_tarski(E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_enumset1)).
% 2.27/1.26  tff(c_12, plain, (![B_16, A_15, D_18, E_19, C_17]: (k2_xboole_0(k1_enumset1(A_15, B_16, C_17), k2_tarski(D_18, E_19))=k3_enumset1(A_15, B_16, C_17, D_18, E_19))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.27/1.26  tff(c_6, plain, (![A_6, B_7]: (k2_xboole_0(k1_tarski(A_6), k1_tarski(B_7))=k2_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.27/1.26  tff(c_65, plain, (![A_30, B_31, C_32, D_33]: (k2_xboole_0(k1_enumset1(A_30, B_31, C_32), k1_tarski(D_33))=k2_enumset1(A_30, B_31, C_32, D_33))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.27/1.26  tff(c_2, plain, (![A_1, B_2, C_3]: (k2_xboole_0(k2_xboole_0(A_1, B_2), C_3)=k2_xboole_0(A_1, k2_xboole_0(B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.27/1.26  tff(c_245, plain, (![C_74, B_72, D_75, C_71, A_73]: (k2_xboole_0(k1_enumset1(A_73, B_72, C_71), k2_xboole_0(k1_tarski(D_75), C_74))=k2_xboole_0(k2_enumset1(A_73, B_72, C_71, D_75), C_74))), inference(superposition, [status(thm), theory('equality')], [c_65, c_2])).
% 2.27/1.26  tff(c_272, plain, (![B_7, B_72, C_71, A_73, A_6]: (k2_xboole_0(k2_enumset1(A_73, B_72, C_71, A_6), k1_tarski(B_7))=k2_xboole_0(k1_enumset1(A_73, B_72, C_71), k2_tarski(A_6, B_7)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_245])).
% 2.27/1.26  tff(c_276, plain, (![B_7, B_72, C_71, A_73, A_6]: (k2_xboole_0(k2_enumset1(A_73, B_72, C_71, A_6), k1_tarski(B_7))=k3_enumset1(A_73, B_72, C_71, A_6, B_7))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_272])).
% 2.27/1.26  tff(c_14, plain, (k2_xboole_0(k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k1_tarski('#skF_5'))!=k3_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.27/1.26  tff(c_279, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_276, c_14])).
% 2.27/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.27/1.26  
% 2.27/1.26  Inference rules
% 2.27/1.26  ----------------------
% 2.27/1.26  #Ref     : 0
% 2.27/1.26  #Sup     : 68
% 2.27/1.26  #Fact    : 0
% 2.27/1.26  #Define  : 0
% 2.27/1.26  #Split   : 0
% 2.27/1.26  #Chain   : 0
% 2.27/1.26  #Close   : 0
% 2.27/1.26  
% 2.27/1.26  Ordering : KBO
% 2.27/1.26  
% 2.27/1.26  Simplification rules
% 2.27/1.26  ----------------------
% 2.27/1.26  #Subsume      : 0
% 2.27/1.26  #Demod        : 27
% 2.27/1.26  #Tautology    : 37
% 2.27/1.26  #SimpNegUnit  : 0
% 2.27/1.26  #BackRed      : 1
% 2.27/1.26  
% 2.27/1.26  #Partial instantiations: 0
% 2.27/1.26  #Strategies tried      : 1
% 2.27/1.26  
% 2.27/1.26  Timing (in seconds)
% 2.27/1.26  ----------------------
% 2.27/1.27  Preprocessing        : 0.26
% 2.27/1.27  Parsing              : 0.14
% 2.27/1.27  CNF conversion       : 0.02
% 2.27/1.27  Main loop            : 0.23
% 2.27/1.27  Inferencing          : 0.11
% 2.27/1.27  Reduction            : 0.07
% 2.27/1.27  Demodulation         : 0.06
% 2.27/1.27  BG Simplification    : 0.02
% 2.27/1.27  Subsumption          : 0.03
% 2.27/1.27  Abstraction          : 0.02
% 2.27/1.27  MUC search           : 0.00
% 2.27/1.27  Cooper               : 0.00
% 2.27/1.27  Total                : 0.52
% 2.27/1.27  Index Insertion      : 0.00
% 2.27/1.27  Index Deletion       : 0.00
% 2.27/1.27  Index Matching       : 0.00
% 2.27/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
