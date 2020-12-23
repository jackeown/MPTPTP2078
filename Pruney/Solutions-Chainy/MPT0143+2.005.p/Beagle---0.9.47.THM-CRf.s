%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:51 EST 2020

% Result     : Theorem 4.52s
% Output     : CNFRefutation 4.52s
% Verified   : 
% Statistics : Number of formulae       :   32 (  32 expanded)
%              Number of leaves         :   23 (  23 expanded)
%              Depth                    :    5
%              Number of atoms          :   14 (  14 expanded)
%              Number of equality atoms :   13 (  13 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k5_enumset1 > k4_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_39,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k1_tarski(A),k4_enumset1(B,C,D,E,F,G)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k1_enumset1(A,B,C),k1_enumset1(D,E,F)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_tarski(A),k1_enumset1(B,C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_42,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k2_enumset1(A,B,C,D),k1_enumset1(E,F,G)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_enumset1)).

tff(c_14,plain,(
    ! [G_28,E_26,F_27,A_22,B_23,D_25,C_24] : k2_xboole_0(k1_tarski(A_22),k4_enumset1(B_23,C_24,D_25,E_26,F_27,G_28)) = k5_enumset1(A_22,B_23,C_24,D_25,E_26,F_27,G_28) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_12,plain,(
    ! [C_18,B_17,A_16,D_19,E_20,F_21] : k2_xboole_0(k1_enumset1(A_16,B_17,C_18),k1_enumset1(D_19,E_20,F_21)) = k4_enumset1(A_16,B_17,C_18,D_19,E_20,F_21) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_91,plain,(
    ! [A_40,B_41,C_42,D_43] : k2_xboole_0(k1_tarski(A_40),k1_enumset1(B_41,C_42,D_43)) = k2_enumset1(A_40,B_41,C_42,D_43) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_4,plain,(
    ! [A_4,B_5,C_6] : k2_xboole_0(k2_xboole_0(A_4,B_5),C_6) = k2_xboole_0(A_4,k2_xboole_0(B_5,C_6)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_261,plain,(
    ! [B_63,C_62,A_59,C_61,D_60] : k2_xboole_0(k1_tarski(A_59),k2_xboole_0(k1_enumset1(B_63,C_61,D_60),C_62)) = k2_xboole_0(k2_enumset1(A_59,B_63,C_61,D_60),C_62) ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_4])).

tff(c_276,plain,(
    ! [C_18,B_17,A_16,A_59,D_19,E_20,F_21] : k2_xboole_0(k2_enumset1(A_59,A_16,B_17,C_18),k1_enumset1(D_19,E_20,F_21)) = k2_xboole_0(k1_tarski(A_59),k4_enumset1(A_16,B_17,C_18,D_19,E_20,F_21)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_261])).

tff(c_2004,plain,(
    ! [C_18,B_17,A_16,A_59,D_19,E_20,F_21] : k2_xboole_0(k2_enumset1(A_59,A_16,B_17,C_18),k1_enumset1(D_19,E_20,F_21)) = k5_enumset1(A_59,A_16,B_17,C_18,D_19,E_20,F_21) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_276])).

tff(c_16,plain,(
    k2_xboole_0(k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4'),k1_enumset1('#skF_5','#skF_6','#skF_7')) != k5_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_2007,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2004,c_16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n014.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:23:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.52/1.77  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.52/1.77  
% 4.52/1.77  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.52/1.77  %$ k5_enumset1 > k4_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.52/1.77  
% 4.52/1.77  %Foreground sorts:
% 4.52/1.77  
% 4.52/1.77  
% 4.52/1.77  %Background operators:
% 4.52/1.77  
% 4.52/1.77  
% 4.52/1.77  %Foreground operators:
% 4.52/1.77  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.52/1.77  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.52/1.77  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.52/1.77  tff('#skF_7', type, '#skF_7': $i).
% 4.52/1.77  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.52/1.77  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.52/1.77  tff('#skF_5', type, '#skF_5': $i).
% 4.52/1.77  tff('#skF_6', type, '#skF_6': $i).
% 4.52/1.77  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.52/1.77  tff('#skF_2', type, '#skF_2': $i).
% 4.52/1.77  tff('#skF_3', type, '#skF_3': $i).
% 4.52/1.77  tff('#skF_1', type, '#skF_1': $i).
% 4.52/1.77  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.52/1.77  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.52/1.77  tff('#skF_4', type, '#skF_4': $i).
% 4.52/1.77  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.52/1.77  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.52/1.77  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.52/1.77  
% 4.52/1.78  tff(f_39, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k1_tarski(A), k4_enumset1(B, C, D, E, F, G)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_enumset1)).
% 4.52/1.78  tff(f_37, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k1_enumset1(A, B, C), k1_enumset1(D, E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t53_enumset1)).
% 4.52/1.78  tff(f_35, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_tarski(A), k1_enumset1(B, C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_enumset1)).
% 4.52/1.78  tff(f_29, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 4.52/1.78  tff(f_42, negated_conjecture, ~(![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k2_enumset1(A, B, C, D), k1_enumset1(E, F, G)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_enumset1)).
% 4.52/1.78  tff(c_14, plain, (![G_28, E_26, F_27, A_22, B_23, D_25, C_24]: (k2_xboole_0(k1_tarski(A_22), k4_enumset1(B_23, C_24, D_25, E_26, F_27, G_28))=k5_enumset1(A_22, B_23, C_24, D_25, E_26, F_27, G_28))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.52/1.78  tff(c_12, plain, (![C_18, B_17, A_16, D_19, E_20, F_21]: (k2_xboole_0(k1_enumset1(A_16, B_17, C_18), k1_enumset1(D_19, E_20, F_21))=k4_enumset1(A_16, B_17, C_18, D_19, E_20, F_21))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.52/1.78  tff(c_91, plain, (![A_40, B_41, C_42, D_43]: (k2_xboole_0(k1_tarski(A_40), k1_enumset1(B_41, C_42, D_43))=k2_enumset1(A_40, B_41, C_42, D_43))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.52/1.78  tff(c_4, plain, (![A_4, B_5, C_6]: (k2_xboole_0(k2_xboole_0(A_4, B_5), C_6)=k2_xboole_0(A_4, k2_xboole_0(B_5, C_6)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.52/1.78  tff(c_261, plain, (![B_63, C_62, A_59, C_61, D_60]: (k2_xboole_0(k1_tarski(A_59), k2_xboole_0(k1_enumset1(B_63, C_61, D_60), C_62))=k2_xboole_0(k2_enumset1(A_59, B_63, C_61, D_60), C_62))), inference(superposition, [status(thm), theory('equality')], [c_91, c_4])).
% 4.52/1.78  tff(c_276, plain, (![C_18, B_17, A_16, A_59, D_19, E_20, F_21]: (k2_xboole_0(k2_enumset1(A_59, A_16, B_17, C_18), k1_enumset1(D_19, E_20, F_21))=k2_xboole_0(k1_tarski(A_59), k4_enumset1(A_16, B_17, C_18, D_19, E_20, F_21)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_261])).
% 4.52/1.78  tff(c_2004, plain, (![C_18, B_17, A_16, A_59, D_19, E_20, F_21]: (k2_xboole_0(k2_enumset1(A_59, A_16, B_17, C_18), k1_enumset1(D_19, E_20, F_21))=k5_enumset1(A_59, A_16, B_17, C_18, D_19, E_20, F_21))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_276])).
% 4.52/1.78  tff(c_16, plain, (k2_xboole_0(k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k1_enumset1('#skF_5', '#skF_6', '#skF_7'))!=k5_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.52/1.78  tff(c_2007, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2004, c_16])).
% 4.52/1.78  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.52/1.78  
% 4.52/1.78  Inference rules
% 4.52/1.78  ----------------------
% 4.52/1.78  #Ref     : 0
% 4.52/1.78  #Sup     : 485
% 4.52/1.78  #Fact    : 0
% 4.52/1.78  #Define  : 0
% 4.52/1.78  #Split   : 0
% 4.52/1.78  #Chain   : 0
% 4.52/1.78  #Close   : 0
% 4.52/1.78  
% 4.52/1.78  Ordering : KBO
% 4.52/1.78  
% 4.52/1.78  Simplification rules
% 4.57/1.78  ----------------------
% 4.57/1.78  #Subsume      : 0
% 4.57/1.78  #Demod        : 999
% 4.57/1.78  #Tautology    : 211
% 4.57/1.78  #SimpNegUnit  : 0
% 4.57/1.78  #BackRed      : 1
% 4.57/1.78  
% 4.57/1.78  #Partial instantiations: 0
% 4.57/1.78  #Strategies tried      : 1
% 4.57/1.78  
% 4.57/1.78  Timing (in seconds)
% 4.57/1.78  ----------------------
% 4.57/1.78  Preprocessing        : 0.28
% 4.57/1.78  Parsing              : 0.16
% 4.57/1.78  CNF conversion       : 0.02
% 4.57/1.78  Main loop            : 0.74
% 4.57/1.78  Inferencing          : 0.26
% 4.57/1.78  Reduction            : 0.34
% 4.57/1.78  Demodulation         : 0.30
% 4.57/1.78  BG Simplification    : 0.05
% 4.57/1.78  Subsumption          : 0.07
% 4.57/1.78  Abstraction          : 0.07
% 4.57/1.78  MUC search           : 0.00
% 4.57/1.78  Cooper               : 0.00
% 4.57/1.78  Total                : 1.04
% 4.57/1.78  Index Insertion      : 0.00
% 4.57/1.78  Index Deletion       : 0.00
% 4.57/1.78  Index Matching       : 0.00
% 4.57/1.78  BG Taut test         : 0.00
%------------------------------------------------------------------------------
