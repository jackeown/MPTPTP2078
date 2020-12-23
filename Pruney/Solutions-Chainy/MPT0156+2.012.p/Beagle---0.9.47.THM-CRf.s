%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:15 EST 2020

% Result     : Theorem 1.78s
% Output     : CNFRefutation 1.81s
% Verified   : 
% Statistics : Number of formulae       :   26 (  26 expanded)
%              Number of leaves         :   19 (  19 expanded)
%              Depth                    :    4
%              Number of atoms          :   11 (  11 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_31,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k2_enumset1(A,B,C,D),k1_tarski(E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_enumset1)).

tff(f_38,negated_conjecture,(
    ~ ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(c_6,plain,(
    ! [A_5,B_6,C_7,D_8] : k2_xboole_0(k1_enumset1(A_5,B_6,C_7),k1_tarski(D_8)) = k2_enumset1(A_5,B_6,C_7,D_8) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    ! [A_14,B_15,C_16] : k2_enumset1(A_14,A_14,B_15,C_16) = k1_enumset1(A_14,B_15,C_16) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_49,plain,(
    ! [C_29,D_30,B_28,A_32,E_31] : k2_xboole_0(k2_enumset1(A_32,B_28,C_29,D_30),k1_tarski(E_31)) = k3_enumset1(A_32,B_28,C_29,D_30,E_31) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_58,plain,(
    ! [A_14,B_15,C_16,E_31] : k3_enumset1(A_14,A_14,B_15,C_16,E_31) = k2_xboole_0(k1_enumset1(A_14,B_15,C_16),k1_tarski(E_31)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_49])).

tff(c_61,plain,(
    ! [A_14,B_15,C_16,E_31] : k3_enumset1(A_14,A_14,B_15,C_16,E_31) = k2_enumset1(A_14,B_15,C_16,E_31) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_58])).

tff(c_12,plain,(
    k3_enumset1('#skF_1','#skF_1','#skF_2','#skF_3','#skF_4') != k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_64,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:35:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.78/1.19  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.78/1.20  
% 1.78/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.81/1.20  %$ k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.81/1.20  
% 1.81/1.20  %Foreground sorts:
% 1.81/1.20  
% 1.81/1.20  
% 1.81/1.20  %Background operators:
% 1.81/1.20  
% 1.81/1.20  
% 1.81/1.20  %Foreground operators:
% 1.81/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.81/1.20  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.81/1.20  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.81/1.20  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.81/1.20  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.81/1.20  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.81/1.20  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.81/1.20  tff('#skF_2', type, '#skF_2': $i).
% 1.81/1.20  tff('#skF_3', type, '#skF_3': $i).
% 1.81/1.20  tff('#skF_1', type, '#skF_1': $i).
% 1.81/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.81/1.20  tff('#skF_4', type, '#skF_4': $i).
% 1.81/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.81/1.20  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.81/1.20  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.81/1.20  
% 1.81/1.21  tff(f_31, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_enumset1)).
% 1.81/1.21  tff(f_35, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 1.81/1.21  tff(f_33, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k2_enumset1(A, B, C, D), k1_tarski(E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_enumset1)).
% 1.81/1.21  tff(f_38, negated_conjecture, ~(![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 1.81/1.21  tff(c_6, plain, (![A_5, B_6, C_7, D_8]: (k2_xboole_0(k1_enumset1(A_5, B_6, C_7), k1_tarski(D_8))=k2_enumset1(A_5, B_6, C_7, D_8))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.81/1.21  tff(c_10, plain, (![A_14, B_15, C_16]: (k2_enumset1(A_14, A_14, B_15, C_16)=k1_enumset1(A_14, B_15, C_16))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.81/1.21  tff(c_49, plain, (![C_29, D_30, B_28, A_32, E_31]: (k2_xboole_0(k2_enumset1(A_32, B_28, C_29, D_30), k1_tarski(E_31))=k3_enumset1(A_32, B_28, C_29, D_30, E_31))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.81/1.21  tff(c_58, plain, (![A_14, B_15, C_16, E_31]: (k3_enumset1(A_14, A_14, B_15, C_16, E_31)=k2_xboole_0(k1_enumset1(A_14, B_15, C_16), k1_tarski(E_31)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_49])).
% 1.81/1.21  tff(c_61, plain, (![A_14, B_15, C_16, E_31]: (k3_enumset1(A_14, A_14, B_15, C_16, E_31)=k2_enumset1(A_14, B_15, C_16, E_31))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_58])).
% 1.81/1.21  tff(c_12, plain, (k3_enumset1('#skF_1', '#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.81/1.21  tff(c_64, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_61, c_12])).
% 1.81/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.81/1.21  
% 1.81/1.21  Inference rules
% 1.81/1.21  ----------------------
% 1.81/1.21  #Ref     : 0
% 1.81/1.21  #Sup     : 11
% 1.81/1.21  #Fact    : 0
% 1.81/1.21  #Define  : 0
% 1.81/1.21  #Split   : 0
% 1.81/1.21  #Chain   : 0
% 1.81/1.21  #Close   : 0
% 1.81/1.21  
% 1.81/1.21  Ordering : KBO
% 1.81/1.21  
% 1.81/1.21  Simplification rules
% 1.81/1.21  ----------------------
% 1.81/1.21  #Subsume      : 0
% 1.81/1.21  #Demod        : 2
% 1.81/1.21  #Tautology    : 10
% 1.81/1.21  #SimpNegUnit  : 0
% 1.81/1.21  #BackRed      : 1
% 1.81/1.21  
% 1.81/1.21  #Partial instantiations: 0
% 1.81/1.21  #Strategies tried      : 1
% 1.81/1.21  
% 1.81/1.21  Timing (in seconds)
% 1.81/1.21  ----------------------
% 1.81/1.22  Preprocessing        : 0.33
% 1.81/1.22  Parsing              : 0.16
% 1.81/1.22  CNF conversion       : 0.02
% 1.81/1.22  Main loop            : 0.10
% 1.81/1.22  Inferencing          : 0.04
% 1.81/1.22  Reduction            : 0.03
% 1.81/1.22  Demodulation         : 0.03
% 1.81/1.22  BG Simplification    : 0.01
% 1.81/1.22  Subsumption          : 0.01
% 1.81/1.22  Abstraction          : 0.01
% 1.81/1.22  MUC search           : 0.00
% 1.81/1.22  Cooper               : 0.00
% 1.81/1.22  Total                : 0.47
% 1.81/1.22  Index Insertion      : 0.00
% 1.81/1.22  Index Deletion       : 0.00
% 1.81/1.22  Index Matching       : 0.00
% 1.81/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
