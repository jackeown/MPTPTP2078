%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:22 EST 2020

% Result     : Theorem 4.42s
% Output     : CNFRefutation 4.59s
% Verified   : 
% Statistics : Number of formulae       :   30 (  30 expanded)
%              Number of leaves         :   23 (  23 expanded)
%              Depth                    :    4
%              Number of atoms          :   11 (  11 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(f_33,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k1_enumset1(A,B,C),k2_enumset1(D,E,F,G)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k2_enumset1(A,B,C,D),k2_enumset1(E,F,G,H)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_enumset1)).

tff(f_46,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G] : k6_enumset1(A,A,B,C,D,E,F,G) = k5_enumset1(A,B,C,D,E,F,G) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

tff(c_8,plain,(
    ! [E_17,F_18,A_13,B_14,C_15,G_19,D_16] : k2_xboole_0(k1_enumset1(A_13,B_14,C_15),k2_enumset1(D_16,E_17,F_18,G_19)) = k5_enumset1(A_13,B_14,C_15,D_16,E_17,F_18,G_19) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_16,plain,(
    ! [A_43,B_44,C_45] : k2_enumset1(A_43,A_43,B_44,C_45) = k1_enumset1(A_43,B_44,C_45) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_918,plain,(
    ! [E_140,D_141,G_137,H_136,F_138,B_142,C_139,A_135] : k2_xboole_0(k2_enumset1(A_135,B_142,C_139,D_141),k2_enumset1(E_140,F_138,G_137,H_136)) = k6_enumset1(A_135,B_142,C_139,D_141,E_140,F_138,G_137,H_136) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_930,plain,(
    ! [E_140,G_137,H_136,F_138,C_45,A_43,B_44] : k6_enumset1(A_43,A_43,B_44,C_45,E_140,F_138,G_137,H_136) = k2_xboole_0(k1_enumset1(A_43,B_44,C_45),k2_enumset1(E_140,F_138,G_137,H_136)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_918])).

tff(c_936,plain,(
    ! [E_140,G_137,H_136,F_138,C_45,A_43,B_44] : k6_enumset1(A_43,A_43,B_44,C_45,E_140,F_138,G_137,H_136) = k5_enumset1(A_43,B_44,C_45,E_140,F_138,G_137,H_136) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_930])).

tff(c_20,plain,(
    k6_enumset1('#skF_1','#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7') != k5_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1918,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_936,c_20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:38:11 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.42/1.79  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.42/1.80  
% 4.42/1.80  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.42/1.80  %$ k6_enumset1 > k5_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.42/1.80  
% 4.42/1.80  %Foreground sorts:
% 4.42/1.80  
% 4.42/1.80  
% 4.42/1.80  %Background operators:
% 4.42/1.80  
% 4.42/1.80  
% 4.42/1.80  %Foreground operators:
% 4.42/1.80  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.42/1.80  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.42/1.80  tff('#skF_7', type, '#skF_7': $i).
% 4.42/1.80  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.42/1.80  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.42/1.80  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.42/1.80  tff('#skF_5', type, '#skF_5': $i).
% 4.42/1.80  tff('#skF_6', type, '#skF_6': $i).
% 4.42/1.80  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.42/1.80  tff('#skF_2', type, '#skF_2': $i).
% 4.42/1.80  tff('#skF_3', type, '#skF_3': $i).
% 4.42/1.80  tff('#skF_1', type, '#skF_1': $i).
% 4.42/1.80  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.42/1.80  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.42/1.80  tff('#skF_4', type, '#skF_4': $i).
% 4.42/1.80  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.42/1.80  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.42/1.80  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.42/1.80  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.42/1.80  
% 4.59/1.81  tff(f_33, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k1_enumset1(A, B, C), k2_enumset1(D, E, F, G)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_enumset1)).
% 4.59/1.81  tff(f_41, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 4.59/1.81  tff(f_39, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k2_enumset1(A, B, C, D), k2_enumset1(E, F, G, H)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_enumset1)).
% 4.59/1.81  tff(f_46, negated_conjecture, ~(![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 4.59/1.81  tff(c_8, plain, (![E_17, F_18, A_13, B_14, C_15, G_19, D_16]: (k2_xboole_0(k1_enumset1(A_13, B_14, C_15), k2_enumset1(D_16, E_17, F_18, G_19))=k5_enumset1(A_13, B_14, C_15, D_16, E_17, F_18, G_19))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.59/1.81  tff(c_16, plain, (![A_43, B_44, C_45]: (k2_enumset1(A_43, A_43, B_44, C_45)=k1_enumset1(A_43, B_44, C_45))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.59/1.81  tff(c_918, plain, (![E_140, D_141, G_137, H_136, F_138, B_142, C_139, A_135]: (k2_xboole_0(k2_enumset1(A_135, B_142, C_139, D_141), k2_enumset1(E_140, F_138, G_137, H_136))=k6_enumset1(A_135, B_142, C_139, D_141, E_140, F_138, G_137, H_136))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.59/1.81  tff(c_930, plain, (![E_140, G_137, H_136, F_138, C_45, A_43, B_44]: (k6_enumset1(A_43, A_43, B_44, C_45, E_140, F_138, G_137, H_136)=k2_xboole_0(k1_enumset1(A_43, B_44, C_45), k2_enumset1(E_140, F_138, G_137, H_136)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_918])).
% 4.59/1.81  tff(c_936, plain, (![E_140, G_137, H_136, F_138, C_45, A_43, B_44]: (k6_enumset1(A_43, A_43, B_44, C_45, E_140, F_138, G_137, H_136)=k5_enumset1(A_43, B_44, C_45, E_140, F_138, G_137, H_136))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_930])).
% 4.59/1.81  tff(c_20, plain, (k6_enumset1('#skF_1', '#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')!=k5_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.59/1.81  tff(c_1918, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_936, c_20])).
% 4.59/1.81  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.59/1.81  
% 4.59/1.81  Inference rules
% 4.59/1.81  ----------------------
% 4.59/1.81  #Ref     : 0
% 4.59/1.81  #Sup     : 499
% 4.59/1.81  #Fact    : 0
% 4.59/1.81  #Define  : 0
% 4.59/1.81  #Split   : 0
% 4.59/1.81  #Chain   : 0
% 4.59/1.81  #Close   : 0
% 4.59/1.81  
% 4.59/1.81  Ordering : KBO
% 4.59/1.81  
% 4.59/1.81  Simplification rules
% 4.59/1.81  ----------------------
% 4.59/1.81  #Subsume      : 108
% 4.59/1.81  #Demod        : 232
% 4.59/1.81  #Tautology    : 129
% 4.59/1.81  #SimpNegUnit  : 0
% 4.59/1.81  #BackRed      : 1
% 4.59/1.81  
% 4.59/1.81  #Partial instantiations: 0
% 4.59/1.81  #Strategies tried      : 1
% 4.59/1.81  
% 4.59/1.81  Timing (in seconds)
% 4.59/1.81  ----------------------
% 4.59/1.81  Preprocessing        : 0.30
% 4.59/1.81  Parsing              : 0.16
% 4.59/1.81  CNF conversion       : 0.02
% 4.59/1.81  Main loop            : 0.69
% 4.59/1.81  Inferencing          : 0.25
% 4.59/1.81  Reduction            : 0.29
% 4.59/1.81  Demodulation         : 0.26
% 4.59/1.81  BG Simplification    : 0.04
% 4.59/1.81  Subsumption          : 0.08
% 4.59/1.81  Abstraction          : 0.05
% 4.59/1.81  MUC search           : 0.00
% 4.59/1.81  Cooper               : 0.00
% 4.59/1.81  Total                : 1.01
% 4.59/1.81  Index Insertion      : 0.00
% 4.59/1.81  Index Deletion       : 0.00
% 4.59/1.81  Index Matching       : 0.00
% 4.59/1.81  BG Taut test         : 0.00
%------------------------------------------------------------------------------
