%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:50 EST 2020

% Result     : Theorem 4.19s
% Output     : CNFRefutation 4.19s
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k1_enumset1(A,B,C),k1_enumset1(D,E,F)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l62_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_tarski(A),k1_enumset1(B,C,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_42,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k2_enumset1(A,B,C,D),k1_enumset1(E,F,G)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_enumset1)).

tff(c_14,plain,(
    ! [G_28,E_26,F_27,A_22,B_23,D_25,C_24] : k2_xboole_0(k1_tarski(A_22),k4_enumset1(B_23,C_24,D_25,E_26,F_27,G_28)) = k5_enumset1(A_22,B_23,C_24,D_25,E_26,F_27,G_28) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_10,plain,(
    ! [E_16,D_15,F_17,C_14,A_12,B_13] : k2_xboole_0(k1_enumset1(A_12,B_13,C_14),k1_enumset1(D_15,E_16,F_17)) = k4_enumset1(A_12,B_13,C_14,D_15,E_16,F_17) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_91,plain,(
    ! [A_40,B_41,C_42,D_43] : k2_xboole_0(k1_tarski(A_40),k1_enumset1(B_41,C_42,D_43)) = k2_enumset1(A_40,B_41,C_42,D_43) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_4,plain,(
    ! [A_4,B_5,C_6] : k2_xboole_0(k2_xboole_0(A_4,B_5),C_6) = k2_xboole_0(A_4,k2_xboole_0(B_5,C_6)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_261,plain,(
    ! [B_63,C_62,A_59,C_61,D_60] : k2_xboole_0(k1_tarski(A_59),k2_xboole_0(k1_enumset1(B_63,C_61,D_60),C_62)) = k2_xboole_0(k2_enumset1(A_59,B_63,C_61,D_60),C_62) ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_4])).

tff(c_276,plain,(
    ! [E_16,D_15,A_59,F_17,C_14,A_12,B_13] : k2_xboole_0(k2_enumset1(A_59,A_12,B_13,C_14),k1_enumset1(D_15,E_16,F_17)) = k2_xboole_0(k1_tarski(A_59),k4_enumset1(A_12,B_13,C_14,D_15,E_16,F_17)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_261])).

tff(c_2004,plain,(
    ! [E_16,D_15,A_59,F_17,C_14,A_12,B_13] : k2_xboole_0(k2_enumset1(A_59,A_12,B_13,C_14),k1_enumset1(D_15,E_16,F_17)) = k5_enumset1(A_59,A_12,B_13,C_14,D_15,E_16,F_17) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_276])).

tff(c_16,plain,(
    k2_xboole_0(k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4'),k1_enumset1('#skF_5','#skF_6','#skF_7')) != k5_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_2007,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2004,c_16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:53:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.19/1.74  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.19/1.74  
% 4.19/1.74  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.19/1.74  %$ k5_enumset1 > k4_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.19/1.74  
% 4.19/1.74  %Foreground sorts:
% 4.19/1.74  
% 4.19/1.74  
% 4.19/1.74  %Background operators:
% 4.19/1.74  
% 4.19/1.74  
% 4.19/1.74  %Foreground operators:
% 4.19/1.74  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.19/1.74  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.19/1.74  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.19/1.74  tff('#skF_7', type, '#skF_7': $i).
% 4.19/1.74  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.19/1.74  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.19/1.74  tff('#skF_5', type, '#skF_5': $i).
% 4.19/1.74  tff('#skF_6', type, '#skF_6': $i).
% 4.19/1.74  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.19/1.74  tff('#skF_2', type, '#skF_2': $i).
% 4.19/1.74  tff('#skF_3', type, '#skF_3': $i).
% 4.19/1.74  tff('#skF_1', type, '#skF_1': $i).
% 4.19/1.74  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.19/1.74  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.19/1.74  tff('#skF_4', type, '#skF_4': $i).
% 4.19/1.74  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.19/1.74  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.19/1.74  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.19/1.74  
% 4.19/1.75  tff(f_39, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k1_tarski(A), k4_enumset1(B, C, D, E, F, G)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_enumset1)).
% 4.19/1.75  tff(f_35, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k1_enumset1(A, B, C), k1_enumset1(D, E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l62_enumset1)).
% 4.19/1.75  tff(f_37, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_tarski(A), k1_enumset1(B, C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_enumset1)).
% 4.19/1.75  tff(f_29, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_1)).
% 4.19/1.75  tff(f_42, negated_conjecture, ~(![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k2_enumset1(A, B, C, D), k1_enumset1(E, F, G)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_enumset1)).
% 4.19/1.75  tff(c_14, plain, (![G_28, E_26, F_27, A_22, B_23, D_25, C_24]: (k2_xboole_0(k1_tarski(A_22), k4_enumset1(B_23, C_24, D_25, E_26, F_27, G_28))=k5_enumset1(A_22, B_23, C_24, D_25, E_26, F_27, G_28))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.19/1.75  tff(c_10, plain, (![E_16, D_15, F_17, C_14, A_12, B_13]: (k2_xboole_0(k1_enumset1(A_12, B_13, C_14), k1_enumset1(D_15, E_16, F_17))=k4_enumset1(A_12, B_13, C_14, D_15, E_16, F_17))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.19/1.75  tff(c_91, plain, (![A_40, B_41, C_42, D_43]: (k2_xboole_0(k1_tarski(A_40), k1_enumset1(B_41, C_42, D_43))=k2_enumset1(A_40, B_41, C_42, D_43))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.19/1.75  tff(c_4, plain, (![A_4, B_5, C_6]: (k2_xboole_0(k2_xboole_0(A_4, B_5), C_6)=k2_xboole_0(A_4, k2_xboole_0(B_5, C_6)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.19/1.75  tff(c_261, plain, (![B_63, C_62, A_59, C_61, D_60]: (k2_xboole_0(k1_tarski(A_59), k2_xboole_0(k1_enumset1(B_63, C_61, D_60), C_62))=k2_xboole_0(k2_enumset1(A_59, B_63, C_61, D_60), C_62))), inference(superposition, [status(thm), theory('equality')], [c_91, c_4])).
% 4.19/1.75  tff(c_276, plain, (![E_16, D_15, A_59, F_17, C_14, A_12, B_13]: (k2_xboole_0(k2_enumset1(A_59, A_12, B_13, C_14), k1_enumset1(D_15, E_16, F_17))=k2_xboole_0(k1_tarski(A_59), k4_enumset1(A_12, B_13, C_14, D_15, E_16, F_17)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_261])).
% 4.19/1.75  tff(c_2004, plain, (![E_16, D_15, A_59, F_17, C_14, A_12, B_13]: (k2_xboole_0(k2_enumset1(A_59, A_12, B_13, C_14), k1_enumset1(D_15, E_16, F_17))=k5_enumset1(A_59, A_12, B_13, C_14, D_15, E_16, F_17))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_276])).
% 4.19/1.75  tff(c_16, plain, (k2_xboole_0(k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k1_enumset1('#skF_5', '#skF_6', '#skF_7'))!=k5_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.19/1.75  tff(c_2007, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2004, c_16])).
% 4.19/1.75  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.19/1.75  
% 4.19/1.75  Inference rules
% 4.19/1.75  ----------------------
% 4.19/1.75  #Ref     : 0
% 4.19/1.75  #Sup     : 485
% 4.19/1.75  #Fact    : 0
% 4.19/1.75  #Define  : 0
% 4.19/1.75  #Split   : 0
% 4.19/1.75  #Chain   : 0
% 4.19/1.75  #Close   : 0
% 4.19/1.75  
% 4.19/1.75  Ordering : KBO
% 4.19/1.75  
% 4.19/1.75  Simplification rules
% 4.19/1.75  ----------------------
% 4.19/1.75  #Subsume      : 0
% 4.19/1.75  #Demod        : 999
% 4.19/1.75  #Tautology    : 211
% 4.19/1.75  #SimpNegUnit  : 0
% 4.19/1.75  #BackRed      : 1
% 4.19/1.75  
% 4.19/1.75  #Partial instantiations: 0
% 4.19/1.75  #Strategies tried      : 1
% 4.19/1.75  
% 4.19/1.75  Timing (in seconds)
% 4.19/1.75  ----------------------
% 4.19/1.75  Preprocessing        : 0.26
% 4.19/1.75  Parsing              : 0.14
% 4.19/1.75  CNF conversion       : 0.02
% 4.19/1.75  Main loop            : 0.73
% 4.19/1.75  Inferencing          : 0.26
% 4.19/1.75  Reduction            : 0.34
% 4.19/1.75  Demodulation         : 0.29
% 4.19/1.75  BG Simplification    : 0.05
% 4.19/1.75  Subsumption          : 0.07
% 4.19/1.75  Abstraction          : 0.07
% 4.19/1.75  MUC search           : 0.00
% 4.19/1.75  Cooper               : 0.00
% 4.19/1.75  Total                : 1.01
% 4.19/1.75  Index Insertion      : 0.00
% 4.19/1.75  Index Deletion       : 0.00
% 4.19/1.75  Index Matching       : 0.00
% 4.19/1.75  BG Taut test         : 0.00
%------------------------------------------------------------------------------
