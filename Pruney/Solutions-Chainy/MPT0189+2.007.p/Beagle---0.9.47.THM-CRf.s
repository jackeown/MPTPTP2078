%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:51 EST 2020

% Result     : Theorem 4.51s
% Output     : CNFRefutation 4.90s
% Verified   : 
% Statistics : Number of formulae       :   33 (  40 expanded)
%              Number of leaves         :   21 (  25 expanded)
%              Depth                    :    5
%              Number of atoms          :   17 (  24 expanded)
%              Number of equality atoms :   16 (  23 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_35,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,B,D,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,D,C,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k2_tarski(A,B),k2_tarski(C,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l53_enumset1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_58,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,A,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_enumset1)).

tff(c_10,plain,(
    ! [A_14,B_15,D_17,C_16] : k2_enumset1(A_14,B_15,D_17,C_16) = k2_enumset1(A_14,B_15,C_16,D_17) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [A_18,D_21,C_20,B_19] : k2_enumset1(A_18,D_21,C_20,B_19) = k2_enumset1(A_18,B_19,C_20,D_21) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_6,plain,(
    ! [A_5,B_6,C_7,D_8] : k2_xboole_0(k2_tarski(A_5,B_6),k2_tarski(C_7,D_8)) = k2_enumset1(A_5,B_6,C_7,D_8) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_432,plain,(
    ! [A_89,B_90,C_91,D_92] : k2_xboole_0(k2_tarski(A_89,B_90),k2_tarski(C_91,D_92)) = k2_enumset1(A_89,B_90,C_91,D_92) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_3329,plain,(
    ! [C_198,D_199,A_200,B_201] : k2_xboole_0(k2_tarski(C_198,D_199),k2_tarski(A_200,B_201)) = k2_enumset1(A_200,B_201,C_198,D_199) ),
    inference(superposition,[status(thm),theory(equality)],[c_432,c_2])).

tff(c_3359,plain,(
    ! [C_7,D_8,A_5,B_6] : k2_enumset1(C_7,D_8,A_5,B_6) = k2_enumset1(A_5,B_6,C_7,D_8) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_3329])).

tff(c_32,plain,(
    k2_enumset1('#skF_2','#skF_1','#skF_3','#skF_4') != k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_33,plain,(
    k2_enumset1('#skF_2','#skF_4','#skF_3','#skF_1') != k2_enumset1('#skF_1','#skF_4','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_12,c_32])).

tff(c_34,plain,(
    k2_enumset1('#skF_2','#skF_4','#skF_1','#skF_3') != k2_enumset1('#skF_1','#skF_4','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_33])).

tff(c_3765,plain,(
    k2_enumset1('#skF_1','#skF_3','#skF_2','#skF_4') != k2_enumset1('#skF_1','#skF_4','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3359,c_34])).

tff(c_3768,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_12,c_3765])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:58:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.51/1.88  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.51/1.88  
% 4.51/1.88  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.51/1.88  %$ k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.51/1.88  
% 4.51/1.88  %Foreground sorts:
% 4.51/1.88  
% 4.51/1.88  
% 4.51/1.88  %Background operators:
% 4.51/1.88  
% 4.51/1.88  
% 4.51/1.88  %Foreground operators:
% 4.51/1.88  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.51/1.88  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.51/1.88  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.51/1.88  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.51/1.88  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.51/1.88  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.51/1.88  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.51/1.88  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.51/1.88  tff('#skF_2', type, '#skF_2': $i).
% 4.51/1.88  tff('#skF_3', type, '#skF_3': $i).
% 4.51/1.88  tff('#skF_1', type, '#skF_1': $i).
% 4.51/1.88  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.51/1.88  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.51/1.88  tff('#skF_4', type, '#skF_4': $i).
% 4.51/1.88  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.51/1.88  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.51/1.88  
% 4.90/1.89  tff(f_35, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, B, D, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t103_enumset1)).
% 4.90/1.89  tff(f_37, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, D, C, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t107_enumset1)).
% 4.90/1.89  tff(f_31, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k2_tarski(A, B), k2_tarski(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l53_enumset1)).
% 4.90/1.89  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 4.90/1.89  tff(f_58, negated_conjecture, ~(![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, A, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t108_enumset1)).
% 4.90/1.89  tff(c_10, plain, (![A_14, B_15, D_17, C_16]: (k2_enumset1(A_14, B_15, D_17, C_16)=k2_enumset1(A_14, B_15, C_16, D_17))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.90/1.89  tff(c_12, plain, (![A_18, D_21, C_20, B_19]: (k2_enumset1(A_18, D_21, C_20, B_19)=k2_enumset1(A_18, B_19, C_20, D_21))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.90/1.89  tff(c_6, plain, (![A_5, B_6, C_7, D_8]: (k2_xboole_0(k2_tarski(A_5, B_6), k2_tarski(C_7, D_8))=k2_enumset1(A_5, B_6, C_7, D_8))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.90/1.89  tff(c_432, plain, (![A_89, B_90, C_91, D_92]: (k2_xboole_0(k2_tarski(A_89, B_90), k2_tarski(C_91, D_92))=k2_enumset1(A_89, B_90, C_91, D_92))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.90/1.89  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.90/1.89  tff(c_3329, plain, (![C_198, D_199, A_200, B_201]: (k2_xboole_0(k2_tarski(C_198, D_199), k2_tarski(A_200, B_201))=k2_enumset1(A_200, B_201, C_198, D_199))), inference(superposition, [status(thm), theory('equality')], [c_432, c_2])).
% 4.90/1.89  tff(c_3359, plain, (![C_7, D_8, A_5, B_6]: (k2_enumset1(C_7, D_8, A_5, B_6)=k2_enumset1(A_5, B_6, C_7, D_8))), inference(superposition, [status(thm), theory('equality')], [c_6, c_3329])).
% 4.90/1.89  tff(c_32, plain, (k2_enumset1('#skF_2', '#skF_1', '#skF_3', '#skF_4')!=k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.90/1.89  tff(c_33, plain, (k2_enumset1('#skF_2', '#skF_4', '#skF_3', '#skF_1')!=k2_enumset1('#skF_1', '#skF_4', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_12, c_32])).
% 4.90/1.89  tff(c_34, plain, (k2_enumset1('#skF_2', '#skF_4', '#skF_1', '#skF_3')!=k2_enumset1('#skF_1', '#skF_4', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_33])).
% 4.90/1.89  tff(c_3765, plain, (k2_enumset1('#skF_1', '#skF_3', '#skF_2', '#skF_4')!=k2_enumset1('#skF_1', '#skF_4', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3359, c_34])).
% 4.90/1.89  tff(c_3768, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_12, c_3765])).
% 4.90/1.89  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.90/1.89  
% 4.90/1.89  Inference rules
% 4.90/1.89  ----------------------
% 4.90/1.89  #Ref     : 0
% 4.90/1.89  #Sup     : 917
% 4.90/1.89  #Fact    : 0
% 4.90/1.89  #Define  : 0
% 4.90/1.89  #Split   : 0
% 4.90/1.89  #Chain   : 0
% 4.90/1.89  #Close   : 0
% 4.90/1.89  
% 4.90/1.89  Ordering : KBO
% 4.90/1.89  
% 4.90/1.89  Simplification rules
% 4.90/1.89  ----------------------
% 4.90/1.89  #Subsume      : 184
% 4.90/1.89  #Demod        : 650
% 4.90/1.89  #Tautology    : 563
% 4.90/1.89  #SimpNegUnit  : 0
% 4.90/1.89  #BackRed      : 4
% 4.90/1.89  
% 4.90/1.89  #Partial instantiations: 0
% 4.90/1.89  #Strategies tried      : 1
% 4.90/1.89  
% 4.90/1.89  Timing (in seconds)
% 4.90/1.89  ----------------------
% 4.90/1.89  Preprocessing        : 0.32
% 4.90/1.89  Parsing              : 0.17
% 4.90/1.90  CNF conversion       : 0.02
% 4.90/1.90  Main loop            : 0.82
% 4.90/1.90  Inferencing          : 0.27
% 4.90/1.90  Reduction            : 0.37
% 4.90/1.90  Demodulation         : 0.32
% 4.90/1.90  BG Simplification    : 0.04
% 4.90/1.90  Subsumption          : 0.10
% 4.90/1.90  Abstraction          : 0.05
% 4.90/1.90  MUC search           : 0.00
% 4.90/1.90  Cooper               : 0.00
% 4.90/1.90  Total                : 1.16
% 4.90/1.90  Index Insertion      : 0.00
% 4.90/1.90  Index Deletion       : 0.00
% 4.90/1.90  Index Matching       : 0.00
% 4.90/1.90  BG Taut test         : 0.00
%------------------------------------------------------------------------------
