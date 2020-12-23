%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:25 EST 2020

% Result     : Theorem 2.17s
% Output     : CNFRefutation 2.17s
% Verified   : 
% Statistics : Number of formulae       :   31 (  31 expanded)
%              Number of leaves         :   22 (  22 expanded)
%              Depth                    :    5
%              Number of atoms          :   14 (  14 expanded)
%              Number of equality atoms :   13 (  13 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k5_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_29,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_tarski(A),k2_enumset1(B,C,D,E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_enumset1)).

tff(f_33,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_35,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k1_enumset1(A,B,C),k2_enumset1(D,E,F,G)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_enumset1)).

tff(f_40,negated_conjecture,(
    ~ ! [A,B,C,D,E] : k5_enumset1(A,A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_enumset1)).

tff(c_4,plain,(
    ! [A_3,D_6,C_5,E_7,B_4] : k2_xboole_0(k1_tarski(A_3),k2_enumset1(B_4,C_5,D_6,E_7)) = k3_enumset1(A_3,B_4,C_5,D_6,E_7) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_8,plain,(
    ! [A_15] : k2_tarski(A_15,A_15) = k1_tarski(A_15) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [A_16,B_17] : k1_enumset1(A_16,A_16,B_17) = k2_tarski(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_147,plain,(
    ! [C_47,A_44,D_49,G_48,B_46,F_43,E_45] : k2_xboole_0(k1_enumset1(A_44,B_46,C_47),k2_enumset1(D_49,E_45,F_43,G_48)) = k5_enumset1(A_44,B_46,C_47,D_49,E_45,F_43,G_48) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_370,plain,(
    ! [F_74,B_73,G_72,E_70,D_71,A_75] : k5_enumset1(A_75,A_75,B_73,D_71,E_70,F_74,G_72) = k2_xboole_0(k2_tarski(A_75,B_73),k2_enumset1(D_71,E_70,F_74,G_72)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_147])).

tff(c_424,plain,(
    ! [A_15,F_74,G_72,E_70,D_71] : k5_enumset1(A_15,A_15,A_15,D_71,E_70,F_74,G_72) = k2_xboole_0(k1_tarski(A_15),k2_enumset1(D_71,E_70,F_74,G_72)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_370])).

tff(c_439,plain,(
    ! [A_15,F_74,G_72,E_70,D_71] : k5_enumset1(A_15,A_15,A_15,D_71,E_70,F_74,G_72) = k3_enumset1(A_15,D_71,E_70,F_74,G_72) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_424])).

tff(c_14,plain,(
    k5_enumset1('#skF_1','#skF_1','#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') != k3_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_442,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_439,c_14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n012.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 10:38:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.17/1.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.17/1.24  
% 2.17/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.17/1.24  %$ k5_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.17/1.24  
% 2.17/1.24  %Foreground sorts:
% 2.17/1.24  
% 2.17/1.24  
% 2.17/1.24  %Background operators:
% 2.17/1.24  
% 2.17/1.24  
% 2.17/1.24  %Foreground operators:
% 2.17/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.17/1.24  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.17/1.24  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.17/1.24  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.17/1.24  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.17/1.24  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.17/1.24  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.17/1.24  tff('#skF_5', type, '#skF_5': $i).
% 2.17/1.24  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.17/1.24  tff('#skF_2', type, '#skF_2': $i).
% 2.17/1.24  tff('#skF_3', type, '#skF_3': $i).
% 2.17/1.24  tff('#skF_1', type, '#skF_1': $i).
% 2.17/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.17/1.24  tff('#skF_4', type, '#skF_4': $i).
% 2.17/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.17/1.24  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.17/1.24  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.17/1.24  
% 2.17/1.25  tff(f_29, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_tarski(A), k2_enumset1(B, C, D, E)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_enumset1)).
% 2.17/1.25  tff(f_33, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.17/1.25  tff(f_35, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.17/1.25  tff(f_31, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k1_enumset1(A, B, C), k2_enumset1(D, E, F, G)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_enumset1)).
% 2.17/1.25  tff(f_40, negated_conjecture, ~(![A, B, C, D, E]: (k5_enumset1(A, A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_enumset1)).
% 2.17/1.25  tff(c_4, plain, (![A_3, D_6, C_5, E_7, B_4]: (k2_xboole_0(k1_tarski(A_3), k2_enumset1(B_4, C_5, D_6, E_7))=k3_enumset1(A_3, B_4, C_5, D_6, E_7))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.17/1.25  tff(c_8, plain, (![A_15]: (k2_tarski(A_15, A_15)=k1_tarski(A_15))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.17/1.25  tff(c_10, plain, (![A_16, B_17]: (k1_enumset1(A_16, A_16, B_17)=k2_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.17/1.25  tff(c_147, plain, (![C_47, A_44, D_49, G_48, B_46, F_43, E_45]: (k2_xboole_0(k1_enumset1(A_44, B_46, C_47), k2_enumset1(D_49, E_45, F_43, G_48))=k5_enumset1(A_44, B_46, C_47, D_49, E_45, F_43, G_48))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.17/1.25  tff(c_370, plain, (![F_74, B_73, G_72, E_70, D_71, A_75]: (k5_enumset1(A_75, A_75, B_73, D_71, E_70, F_74, G_72)=k2_xboole_0(k2_tarski(A_75, B_73), k2_enumset1(D_71, E_70, F_74, G_72)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_147])).
% 2.17/1.25  tff(c_424, plain, (![A_15, F_74, G_72, E_70, D_71]: (k5_enumset1(A_15, A_15, A_15, D_71, E_70, F_74, G_72)=k2_xboole_0(k1_tarski(A_15), k2_enumset1(D_71, E_70, F_74, G_72)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_370])).
% 2.17/1.25  tff(c_439, plain, (![A_15, F_74, G_72, E_70, D_71]: (k5_enumset1(A_15, A_15, A_15, D_71, E_70, F_74, G_72)=k3_enumset1(A_15, D_71, E_70, F_74, G_72))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_424])).
% 2.17/1.25  tff(c_14, plain, (k5_enumset1('#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')!=k3_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.17/1.25  tff(c_442, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_439, c_14])).
% 2.17/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.17/1.25  
% 2.17/1.25  Inference rules
% 2.17/1.25  ----------------------
% 2.17/1.25  #Ref     : 0
% 2.17/1.25  #Sup     : 102
% 2.17/1.25  #Fact    : 0
% 2.17/1.25  #Define  : 0
% 2.17/1.25  #Split   : 0
% 2.17/1.25  #Chain   : 0
% 2.17/1.25  #Close   : 0
% 2.17/1.25  
% 2.17/1.25  Ordering : KBO
% 2.17/1.25  
% 2.17/1.25  Simplification rules
% 2.17/1.25  ----------------------
% 2.17/1.25  #Subsume      : 1
% 2.17/1.25  #Demod        : 74
% 2.17/1.25  #Tautology    : 84
% 2.17/1.25  #SimpNegUnit  : 0
% 2.17/1.25  #BackRed      : 1
% 2.17/1.25  
% 2.17/1.25  #Partial instantiations: 0
% 2.17/1.25  #Strategies tried      : 1
% 2.17/1.25  
% 2.17/1.25  Timing (in seconds)
% 2.17/1.25  ----------------------
% 2.17/1.26  Preprocessing        : 0.27
% 2.17/1.26  Parsing              : 0.14
% 2.17/1.26  CNF conversion       : 0.02
% 2.17/1.26  Main loop            : 0.24
% 2.17/1.26  Inferencing          : 0.11
% 2.17/1.26  Reduction            : 0.09
% 2.17/1.26  Demodulation         : 0.07
% 2.17/1.26  BG Simplification    : 0.01
% 2.17/1.26  Subsumption          : 0.02
% 2.17/1.26  Abstraction          : 0.02
% 2.17/1.26  MUC search           : 0.00
% 2.17/1.26  Cooper               : 0.00
% 2.17/1.26  Total                : 0.53
% 2.17/1.26  Index Insertion      : 0.00
% 2.17/1.26  Index Deletion       : 0.00
% 2.17/1.26  Index Matching       : 0.00
% 2.17/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
