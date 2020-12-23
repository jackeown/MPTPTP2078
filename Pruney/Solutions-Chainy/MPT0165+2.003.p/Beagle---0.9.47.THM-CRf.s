%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:25 EST 2020

% Result     : Theorem 2.22s
% Output     : CNFRefutation 2.22s
% Verified   : 
% Statistics : Number of formulae       :   32 (  32 expanded)
%              Number of leaves         :   23 (  23 expanded)
%              Depth                    :    5
%              Number of atoms          :   14 (  14 expanded)
%              Number of equality atoms :   13 (  13 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_39,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k1_enumset1(A,B,C),k2_enumset1(D,E,F,G)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k2_enumset1(A,B,C,D),k2_enumset1(E,F,G,H)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l75_enumset1)).

tff(f_42,negated_conjecture,(
    ~ ! [A,B,C,D,E,F] : k6_enumset1(A,A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_enumset1)).

tff(c_14,plain,(
    ! [D_33,A_30,C_32,B_31,E_34,F_35] : k5_enumset1(A_30,A_30,B_31,C_32,D_33,E_34,F_35) = k4_enumset1(A_30,B_31,C_32,D_33,E_34,F_35) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_6,plain,(
    ! [G_17,F_16,D_14,E_15,B_12,A_11,C_13] : k2_xboole_0(k1_enumset1(A_11,B_12,C_13),k2_enumset1(D_14,E_15,F_16,G_17)) = k5_enumset1(A_11,B_12,C_13,D_14,E_15,F_16,G_17) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [A_18,B_19,C_20] : k2_enumset1(A_18,A_18,B_19,C_20) = k1_enumset1(A_18,B_19,C_20) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_139,plain,(
    ! [H_79,C_80,B_81,A_78,F_77,E_75,G_74,D_76] : k2_xboole_0(k2_enumset1(A_78,B_81,C_80,D_76),k2_enumset1(E_75,F_77,G_74,H_79)) = k6_enumset1(A_78,B_81,C_80,D_76,E_75,F_77,G_74,H_79) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_148,plain,(
    ! [H_79,F_77,E_75,A_18,C_20,B_19,G_74] : k6_enumset1(A_18,A_18,B_19,C_20,E_75,F_77,G_74,H_79) = k2_xboole_0(k1_enumset1(A_18,B_19,C_20),k2_enumset1(E_75,F_77,G_74,H_79)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_139])).

tff(c_154,plain,(
    ! [H_79,F_77,E_75,A_18,C_20,B_19,G_74] : k6_enumset1(A_18,A_18,B_19,C_20,E_75,F_77,G_74,H_79) = k5_enumset1(A_18,B_19,C_20,E_75,F_77,G_74,H_79) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_148])).

tff(c_16,plain,(
    k6_enumset1('#skF_1','#skF_1','#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6') != k4_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_214,plain,(
    k5_enumset1('#skF_1','#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6') != k4_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_16])).

tff(c_217,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_214])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:48:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.22/1.48  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.22/1.48  
% 2.22/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.22/1.49  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.22/1.49  
% 2.22/1.49  %Foreground sorts:
% 2.22/1.49  
% 2.22/1.49  
% 2.22/1.49  %Background operators:
% 2.22/1.49  
% 2.22/1.49  
% 2.22/1.49  %Foreground operators:
% 2.22/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.22/1.49  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.22/1.49  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.22/1.49  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.22/1.49  tff('#skF_5', type, '#skF_5': $i).
% 2.22/1.49  tff('#skF_6', type, '#skF_6': $i).
% 2.22/1.49  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.22/1.49  tff('#skF_2', type, '#skF_2': $i).
% 2.22/1.49  tff('#skF_3', type, '#skF_3': $i).
% 2.22/1.49  tff('#skF_1', type, '#skF_1': $i).
% 2.22/1.49  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.22/1.49  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.22/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.22/1.49  tff('#skF_4', type, '#skF_4': $i).
% 2.22/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.22/1.49  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.22/1.49  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.22/1.49  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.22/1.49  
% 2.22/1.49  tff(f_39, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 2.22/1.49  tff(f_31, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k1_enumset1(A, B, C), k2_enumset1(D, E, F, G)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_enumset1)).
% 2.22/1.49  tff(f_33, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 2.22/1.49  tff(f_29, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k2_enumset1(A, B, C, D), k2_enumset1(E, F, G, H)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l75_enumset1)).
% 2.22/1.49  tff(f_42, negated_conjecture, ~(![A, B, C, D, E, F]: (k6_enumset1(A, A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_enumset1)).
% 2.22/1.49  tff(c_14, plain, (![D_33, A_30, C_32, B_31, E_34, F_35]: (k5_enumset1(A_30, A_30, B_31, C_32, D_33, E_34, F_35)=k4_enumset1(A_30, B_31, C_32, D_33, E_34, F_35))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.22/1.49  tff(c_6, plain, (![G_17, F_16, D_14, E_15, B_12, A_11, C_13]: (k2_xboole_0(k1_enumset1(A_11, B_12, C_13), k2_enumset1(D_14, E_15, F_16, G_17))=k5_enumset1(A_11, B_12, C_13, D_14, E_15, F_16, G_17))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.22/1.49  tff(c_8, plain, (![A_18, B_19, C_20]: (k2_enumset1(A_18, A_18, B_19, C_20)=k1_enumset1(A_18, B_19, C_20))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.22/1.49  tff(c_139, plain, (![H_79, C_80, B_81, A_78, F_77, E_75, G_74, D_76]: (k2_xboole_0(k2_enumset1(A_78, B_81, C_80, D_76), k2_enumset1(E_75, F_77, G_74, H_79))=k6_enumset1(A_78, B_81, C_80, D_76, E_75, F_77, G_74, H_79))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.22/1.49  tff(c_148, plain, (![H_79, F_77, E_75, A_18, C_20, B_19, G_74]: (k6_enumset1(A_18, A_18, B_19, C_20, E_75, F_77, G_74, H_79)=k2_xboole_0(k1_enumset1(A_18, B_19, C_20), k2_enumset1(E_75, F_77, G_74, H_79)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_139])).
% 2.22/1.49  tff(c_154, plain, (![H_79, F_77, E_75, A_18, C_20, B_19, G_74]: (k6_enumset1(A_18, A_18, B_19, C_20, E_75, F_77, G_74, H_79)=k5_enumset1(A_18, B_19, C_20, E_75, F_77, G_74, H_79))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_148])).
% 2.22/1.49  tff(c_16, plain, (k6_enumset1('#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')!=k4_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.22/1.49  tff(c_214, plain, (k5_enumset1('#skF_1', '#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')!=k4_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_154, c_16])).
% 2.22/1.49  tff(c_217, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_214])).
% 2.22/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.22/1.49  
% 2.22/1.49  Inference rules
% 2.22/1.49  ----------------------
% 2.22/1.49  #Ref     : 0
% 2.22/1.49  #Sup     : 47
% 2.22/1.49  #Fact    : 0
% 2.22/1.49  #Define  : 0
% 2.22/1.49  #Split   : 0
% 2.22/1.49  #Chain   : 0
% 2.22/1.49  #Close   : 0
% 2.22/1.49  
% 2.22/1.49  Ordering : KBO
% 2.22/1.49  
% 2.22/1.49  Simplification rules
% 2.22/1.49  ----------------------
% 2.22/1.49  #Subsume      : 4
% 2.22/1.49  #Demod        : 10
% 2.22/1.49  #Tautology    : 35
% 2.22/1.49  #SimpNegUnit  : 0
% 2.22/1.49  #BackRed      : 1
% 2.22/1.49  
% 2.22/1.49  #Partial instantiations: 0
% 2.22/1.49  #Strategies tried      : 1
% 2.22/1.49  
% 2.22/1.49  Timing (in seconds)
% 2.22/1.49  ----------------------
% 2.22/1.50  Preprocessing        : 0.37
% 2.22/1.50  Parsing              : 0.20
% 2.22/1.50  CNF conversion       : 0.02
% 2.22/1.50  Main loop            : 0.19
% 2.22/1.50  Inferencing          : 0.09
% 2.22/1.50  Reduction            : 0.06
% 2.22/1.50  Demodulation         : 0.05
% 2.22/1.50  BG Simplification    : 0.02
% 2.22/1.50  Subsumption          : 0.02
% 2.22/1.50  Abstraction          : 0.01
% 2.22/1.50  MUC search           : 0.00
% 2.22/1.50  Cooper               : 0.00
% 2.22/1.50  Total                : 0.58
% 2.22/1.50  Index Insertion      : 0.00
% 2.22/1.50  Index Deletion       : 0.00
% 2.22/1.50  Index Matching       : 0.00
% 2.22/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
