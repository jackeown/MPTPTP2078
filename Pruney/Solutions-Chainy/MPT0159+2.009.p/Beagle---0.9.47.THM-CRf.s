%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:22 EST 2020

% Result     : Theorem 3.90s
% Output     : CNFRefutation 3.90s
% Verified   : 
% Statistics : Number of formulae       :   34 (  34 expanded)
%              Number of leaves         :   25 (  25 expanded)
%              Depth                    :    5
%              Number of atoms          :   16 (  16 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(f_35,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k1_tarski(A),k5_enumset1(B,C,D,E,F,G,H)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k1_tarski(A),k4_enumset1(B,C,D,E,F,G)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_enumset1)).

tff(f_31,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_50,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G] : k6_enumset1(A,A,B,C,D,E,F,G) = k5_enumset1(A,B,C,D,E,F,G) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

tff(c_8,plain,(
    ! [E_16,D_15,H_19,F_17,C_14,A_12,B_13,G_18] : k2_xboole_0(k1_tarski(A_12),k5_enumset1(B_13,C_14,D_15,E_16,F_17,G_18,H_19)) = k6_enumset1(A_12,B_13,C_14,D_15,E_16,F_17,G_18,H_19) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_104,plain,(
    ! [E_74,C_72,D_68,A_73,B_71,F_69,G_70] : k2_xboole_0(k1_tarski(A_73),k4_enumset1(B_71,C_72,D_68,E_74,F_69,G_70)) = k5_enumset1(A_73,B_71,C_72,D_68,E_74,F_69,G_70) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_4,plain,(
    ! [A_3,B_4] : r1_tarski(A_3,k2_xboole_0(A_3,B_4)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_123,plain,(
    ! [C_78,E_77,B_79,F_81,G_76,D_75,A_80] : r1_tarski(k1_tarski(A_80),k5_enumset1(A_80,B_79,C_78,D_75,E_77,F_81,G_76)) ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_4])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k2_xboole_0(A_1,B_2) = B_2
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_991,plain,(
    ! [A_185,C_188,B_190,E_189,F_187,G_186,D_191] : k2_xboole_0(k1_tarski(A_185),k5_enumset1(A_185,B_190,C_188,D_191,E_189,F_187,G_186)) = k5_enumset1(A_185,B_190,C_188,D_191,E_189,F_187,G_186) ),
    inference(resolution,[status(thm)],[c_123,c_2])).

tff(c_1034,plain,(
    ! [E_16,D_15,H_19,F_17,C_14,B_13,G_18] : k6_enumset1(B_13,B_13,C_14,D_15,E_16,F_17,G_18,H_19) = k5_enumset1(B_13,C_14,D_15,E_16,F_17,G_18,H_19) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_991])).

tff(c_22,plain,(
    k6_enumset1('#skF_1','#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7') != k5_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_2630,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1034,c_22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n020.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:44:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.90/1.71  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.90/1.71  
% 3.90/1.71  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.90/1.71  %$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.90/1.71  
% 3.90/1.71  %Foreground sorts:
% 3.90/1.71  
% 3.90/1.71  
% 3.90/1.71  %Background operators:
% 3.90/1.71  
% 3.90/1.71  
% 3.90/1.71  %Foreground operators:
% 3.90/1.71  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.90/1.71  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.90/1.71  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.90/1.71  tff('#skF_7', type, '#skF_7': $i).
% 3.90/1.71  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.90/1.71  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.90/1.71  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.90/1.71  tff('#skF_5', type, '#skF_5': $i).
% 3.90/1.71  tff('#skF_6', type, '#skF_6': $i).
% 3.90/1.71  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.90/1.71  tff('#skF_2', type, '#skF_2': $i).
% 3.90/1.71  tff('#skF_3', type, '#skF_3': $i).
% 3.90/1.71  tff('#skF_1', type, '#skF_1': $i).
% 3.90/1.71  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.90/1.71  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.90/1.71  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.90/1.71  tff('#skF_4', type, '#skF_4': $i).
% 3.90/1.71  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.90/1.71  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.90/1.71  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.90/1.71  
% 3.90/1.72  tff(f_35, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k1_tarski(A), k5_enumset1(B, C, D, E, F, G, H)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_enumset1)).
% 3.90/1.72  tff(f_33, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k1_tarski(A), k4_enumset1(B, C, D, E, F, G)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_enumset1)).
% 3.90/1.72  tff(f_31, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.90/1.72  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.90/1.72  tff(f_50, negated_conjecture, ~(![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 3.90/1.72  tff(c_8, plain, (![E_16, D_15, H_19, F_17, C_14, A_12, B_13, G_18]: (k2_xboole_0(k1_tarski(A_12), k5_enumset1(B_13, C_14, D_15, E_16, F_17, G_18, H_19))=k6_enumset1(A_12, B_13, C_14, D_15, E_16, F_17, G_18, H_19))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.90/1.72  tff(c_104, plain, (![E_74, C_72, D_68, A_73, B_71, F_69, G_70]: (k2_xboole_0(k1_tarski(A_73), k4_enumset1(B_71, C_72, D_68, E_74, F_69, G_70))=k5_enumset1(A_73, B_71, C_72, D_68, E_74, F_69, G_70))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.90/1.72  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(A_3, k2_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.90/1.72  tff(c_123, plain, (![C_78, E_77, B_79, F_81, G_76, D_75, A_80]: (r1_tarski(k1_tarski(A_80), k5_enumset1(A_80, B_79, C_78, D_75, E_77, F_81, G_76)))), inference(superposition, [status(thm), theory('equality')], [c_104, c_4])).
% 3.90/1.72  tff(c_2, plain, (![A_1, B_2]: (k2_xboole_0(A_1, B_2)=B_2 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.90/1.72  tff(c_991, plain, (![A_185, C_188, B_190, E_189, F_187, G_186, D_191]: (k2_xboole_0(k1_tarski(A_185), k5_enumset1(A_185, B_190, C_188, D_191, E_189, F_187, G_186))=k5_enumset1(A_185, B_190, C_188, D_191, E_189, F_187, G_186))), inference(resolution, [status(thm)], [c_123, c_2])).
% 3.90/1.72  tff(c_1034, plain, (![E_16, D_15, H_19, F_17, C_14, B_13, G_18]: (k6_enumset1(B_13, B_13, C_14, D_15, E_16, F_17, G_18, H_19)=k5_enumset1(B_13, C_14, D_15, E_16, F_17, G_18, H_19))), inference(superposition, [status(thm), theory('equality')], [c_8, c_991])).
% 3.90/1.72  tff(c_22, plain, (k6_enumset1('#skF_1', '#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')!=k5_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.90/1.72  tff(c_2630, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1034, c_22])).
% 3.90/1.72  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.90/1.72  
% 3.90/1.72  Inference rules
% 3.90/1.72  ----------------------
% 3.90/1.72  #Ref     : 0
% 3.90/1.72  #Sup     : 612
% 3.90/1.72  #Fact    : 0
% 3.90/1.72  #Define  : 0
% 3.90/1.72  #Split   : 0
% 3.90/1.72  #Chain   : 0
% 3.90/1.72  #Close   : 0
% 3.90/1.72  
% 3.90/1.72  Ordering : KBO
% 3.90/1.72  
% 3.90/1.72  Simplification rules
% 3.90/1.72  ----------------------
% 3.90/1.72  #Subsume      : 31
% 3.90/1.72  #Demod        : 758
% 3.90/1.72  #Tautology    : 490
% 3.90/1.72  #SimpNegUnit  : 0
% 3.90/1.72  #BackRed      : 1
% 3.90/1.72  
% 3.90/1.72  #Partial instantiations: 0
% 3.90/1.72  #Strategies tried      : 1
% 3.90/1.72  
% 3.90/1.72  Timing (in seconds)
% 3.90/1.72  ----------------------
% 3.90/1.72  Preprocessing        : 0.31
% 3.90/1.72  Parsing              : 0.17
% 3.90/1.72  CNF conversion       : 0.02
% 3.90/1.72  Main loop            : 0.59
% 3.90/1.72  Inferencing          : 0.25
% 3.90/1.72  Reduction            : 0.24
% 3.90/1.72  Demodulation         : 0.21
% 3.90/1.72  BG Simplification    : 0.02
% 3.90/1.72  Subsumption          : 0.05
% 3.90/1.72  Abstraction          : 0.04
% 3.90/1.72  MUC search           : 0.00
% 3.90/1.73  Cooper               : 0.00
% 3.90/1.73  Total                : 0.93
% 3.90/1.73  Index Insertion      : 0.00
% 3.90/1.73  Index Deletion       : 0.00
% 3.90/1.73  Index Matching       : 0.00
% 3.90/1.73  BG Taut test         : 0.00
%------------------------------------------------------------------------------
