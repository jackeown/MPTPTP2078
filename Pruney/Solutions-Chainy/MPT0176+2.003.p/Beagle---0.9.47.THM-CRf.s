%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:34 EST 2020

% Result     : Theorem 1.80s
% Output     : CNFRefutation 1.80s
% Verified   : 
% Statistics : Number of formulae       :   28 (  28 expanded)
%              Number of leaves         :   18 (  18 expanded)
%              Depth                    :    5
%              Number of atoms          :   16 (  16 expanded)
%              Number of equality atoms :   15 (  15 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_35,axiom,(
    ! [A,B] : k3_enumset1(A,A,A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k1_enumset1(A,B,C),k1_enumset1(D,E,F)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k1_enumset1(A,B,C),k2_enumset1(D,E,F,G)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_enumset1)).

tff(f_38,negated_conjecture,(
    ~ ! [A,B] : k5_enumset1(A,A,A,A,A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_enumset1)).

tff(c_10,plain,(
    ! [A_22,B_23] : k3_enumset1(A_22,A_22,A_22,A_22,B_23) = k2_tarski(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_8,plain,(
    ! [E_21,D_20,C_19,B_18,A_17] : k4_enumset1(A_17,A_17,B_18,C_19,D_20,E_21) = k3_enumset1(A_17,B_18,C_19,D_20,E_21) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2,plain,(
    ! [B_2,C_3,A_1,E_5,D_4,F_6] : k2_xboole_0(k1_enumset1(A_1,B_2,C_3),k1_enumset1(D_4,E_5,F_6)) = k4_enumset1(A_1,B_2,C_3,D_4,E_5,F_6) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [A_14,B_15,C_16] : k2_enumset1(A_14,A_14,B_15,C_16) = k1_enumset1(A_14,B_15,C_16) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_49,plain,(
    ! [C_42,F_45,D_40,E_46,G_44,A_43,B_41] : k2_xboole_0(k1_enumset1(A_43,B_41,C_42),k2_enumset1(D_40,E_46,F_45,G_44)) = k5_enumset1(A_43,B_41,C_42,D_40,E_46,F_45,G_44) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_58,plain,(
    ! [C_42,C_16,A_43,A_14,B_41,B_15] : k5_enumset1(A_43,B_41,C_42,A_14,A_14,B_15,C_16) = k2_xboole_0(k1_enumset1(A_43,B_41,C_42),k1_enumset1(A_14,B_15,C_16)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_49])).

tff(c_61,plain,(
    ! [C_42,C_16,A_43,A_14,B_41,B_15] : k5_enumset1(A_43,B_41,C_42,A_14,A_14,B_15,C_16) = k4_enumset1(A_43,B_41,C_42,A_14,B_15,C_16) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_58])).

tff(c_12,plain,(
    k5_enumset1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_2') != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_62,plain,(
    k4_enumset1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_2') != k2_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_12])).

tff(c_65,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_8,c_62])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:32:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.80/1.16  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.80/1.16  
% 1.80/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.80/1.16  %$ k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > #skF_2 > #skF_1
% 1.80/1.16  
% 1.80/1.16  %Foreground sorts:
% 1.80/1.16  
% 1.80/1.16  
% 1.80/1.16  %Background operators:
% 1.80/1.16  
% 1.80/1.16  
% 1.80/1.16  %Foreground operators:
% 1.80/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.80/1.16  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.80/1.16  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.80/1.16  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.80/1.16  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.80/1.16  tff('#skF_2', type, '#skF_2': $i).
% 1.80/1.16  tff('#skF_1', type, '#skF_1': $i).
% 1.80/1.16  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.80/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.80/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.80/1.16  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.80/1.16  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.80/1.16  
% 1.80/1.17  tff(f_35, axiom, (![A, B]: (k3_enumset1(A, A, A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_enumset1)).
% 1.80/1.17  tff(f_33, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 1.80/1.17  tff(f_27, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k1_enumset1(A, B, C), k1_enumset1(D, E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t53_enumset1)).
% 1.80/1.17  tff(f_31, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 1.80/1.17  tff(f_29, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k1_enumset1(A, B, C), k2_enumset1(D, E, F, G)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_enumset1)).
% 1.80/1.17  tff(f_38, negated_conjecture, ~(![A, B]: (k5_enumset1(A, A, A, A, A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_enumset1)).
% 1.80/1.17  tff(c_10, plain, (![A_22, B_23]: (k3_enumset1(A_22, A_22, A_22, A_22, B_23)=k2_tarski(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.80/1.17  tff(c_8, plain, (![E_21, D_20, C_19, B_18, A_17]: (k4_enumset1(A_17, A_17, B_18, C_19, D_20, E_21)=k3_enumset1(A_17, B_18, C_19, D_20, E_21))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.80/1.17  tff(c_2, plain, (![B_2, C_3, A_1, E_5, D_4, F_6]: (k2_xboole_0(k1_enumset1(A_1, B_2, C_3), k1_enumset1(D_4, E_5, F_6))=k4_enumset1(A_1, B_2, C_3, D_4, E_5, F_6))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.80/1.17  tff(c_6, plain, (![A_14, B_15, C_16]: (k2_enumset1(A_14, A_14, B_15, C_16)=k1_enumset1(A_14, B_15, C_16))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.80/1.17  tff(c_49, plain, (![C_42, F_45, D_40, E_46, G_44, A_43, B_41]: (k2_xboole_0(k1_enumset1(A_43, B_41, C_42), k2_enumset1(D_40, E_46, F_45, G_44))=k5_enumset1(A_43, B_41, C_42, D_40, E_46, F_45, G_44))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.80/1.17  tff(c_58, plain, (![C_42, C_16, A_43, A_14, B_41, B_15]: (k5_enumset1(A_43, B_41, C_42, A_14, A_14, B_15, C_16)=k2_xboole_0(k1_enumset1(A_43, B_41, C_42), k1_enumset1(A_14, B_15, C_16)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_49])).
% 1.80/1.17  tff(c_61, plain, (![C_42, C_16, A_43, A_14, B_41, B_15]: (k5_enumset1(A_43, B_41, C_42, A_14, A_14, B_15, C_16)=k4_enumset1(A_43, B_41, C_42, A_14, B_15, C_16))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_58])).
% 1.80/1.17  tff(c_12, plain, (k5_enumset1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2')!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.80/1.17  tff(c_62, plain, (k4_enumset1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2')!=k2_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_61, c_12])).
% 1.80/1.17  tff(c_65, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_8, c_62])).
% 1.80/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.80/1.17  
% 1.80/1.17  Inference rules
% 1.80/1.17  ----------------------
% 1.80/1.17  #Ref     : 0
% 1.80/1.17  #Sup     : 11
% 1.80/1.17  #Fact    : 0
% 1.80/1.17  #Define  : 0
% 1.80/1.17  #Split   : 0
% 1.80/1.17  #Chain   : 0
% 1.80/1.17  #Close   : 0
% 1.80/1.17  
% 1.80/1.17  Ordering : KBO
% 1.80/1.17  
% 1.80/1.17  Simplification rules
% 1.80/1.17  ----------------------
% 1.80/1.17  #Subsume      : 0
% 1.80/1.17  #Demod        : 4
% 1.80/1.17  #Tautology    : 10
% 1.80/1.17  #SimpNegUnit  : 0
% 1.80/1.17  #BackRed      : 1
% 1.80/1.17  
% 1.80/1.17  #Partial instantiations: 0
% 1.80/1.17  #Strategies tried      : 1
% 1.80/1.17  
% 1.80/1.17  Timing (in seconds)
% 1.80/1.17  ----------------------
% 1.80/1.18  Preprocessing        : 0.29
% 1.80/1.18  Parsing              : 0.15
% 1.80/1.18  CNF conversion       : 0.02
% 1.80/1.18  Main loop            : 0.08
% 1.80/1.18  Inferencing          : 0.04
% 1.80/1.18  Reduction            : 0.02
% 1.80/1.18  Demodulation         : 0.02
% 1.80/1.18  BG Simplification    : 0.01
% 1.80/1.18  Subsumption          : 0.01
% 1.80/1.18  Abstraction          : 0.01
% 1.80/1.18  MUC search           : 0.00
% 1.80/1.18  Cooper               : 0.00
% 1.80/1.18  Total                : 0.39
% 1.80/1.18  Index Insertion      : 0.00
% 1.80/1.18  Index Deletion       : 0.00
% 1.80/1.18  Index Matching       : 0.00
% 1.80/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
