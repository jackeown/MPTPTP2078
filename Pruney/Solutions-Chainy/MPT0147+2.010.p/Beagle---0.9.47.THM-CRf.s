%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:56 EST 2020

% Result     : Theorem 8.91s
% Output     : CNFRefutation 8.91s
% Verified   : 
% Statistics : Number of formulae       :   36 (  36 expanded)
%              Number of leaves         :   27 (  27 expanded)
%              Depth                    :    5
%              Number of atoms          :   14 (  14 expanded)
%              Number of equality atoms :   13 (  13 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff('#skF_8',type,(
    '#skF_8': $i )).

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

tff(f_43,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k1_tarski(A),k5_enumset1(B,C,D,E,F,G,H)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k1_tarski(A),k4_enumset1(B,C,D,E,F,G)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_enumset1)).

tff(f_35,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_46,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k2_tarski(A,B),k4_enumset1(C,D,E,F,G,H)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_enumset1)).

tff(c_18,plain,(
    ! [G_35,H_36,E_33,A_29,F_34,D_32,C_31,B_30] : k2_xboole_0(k1_tarski(A_29),k5_enumset1(B_30,C_31,D_32,E_33,F_34,G_35,H_36)) = k6_enumset1(A_29,B_30,C_31,D_32,E_33,F_34,G_35,H_36) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_498,plain,(
    ! [G_92,C_89,E_90,F_91,A_88,B_94,D_93] : k2_xboole_0(k1_tarski(A_88),k4_enumset1(B_94,C_89,D_93,E_90,F_91,G_92)) = k5_enumset1(A_88,B_94,C_89,D_93,E_90,F_91,G_92) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_10,plain,(
    ! [A_11,B_12] : k2_xboole_0(k1_tarski(A_11),k1_tarski(B_12)) = k2_tarski(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_48,plain,(
    ! [A_43,B_44,C_45] : k2_xboole_0(k2_xboole_0(A_43,B_44),C_45) = k2_xboole_0(A_43,k2_xboole_0(B_44,C_45)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_63,plain,(
    ! [A_11,B_12,C_45] : k2_xboole_0(k1_tarski(A_11),k2_xboole_0(k1_tarski(B_12),C_45)) = k2_xboole_0(k2_tarski(A_11,B_12),C_45) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_48])).

tff(c_507,plain,(
    ! [G_92,C_89,E_90,F_91,A_88,B_94,A_11,D_93] : k2_xboole_0(k2_tarski(A_11,A_88),k4_enumset1(B_94,C_89,D_93,E_90,F_91,G_92)) = k2_xboole_0(k1_tarski(A_11),k5_enumset1(A_88,B_94,C_89,D_93,E_90,F_91,G_92)) ),
    inference(superposition,[status(thm),theory(equality)],[c_498,c_63])).

tff(c_6626,plain,(
    ! [G_92,C_89,E_90,F_91,A_88,B_94,A_11,D_93] : k2_xboole_0(k2_tarski(A_11,A_88),k4_enumset1(B_94,C_89,D_93,E_90,F_91,G_92)) = k6_enumset1(A_11,A_88,B_94,C_89,D_93,E_90,F_91,G_92) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_507])).

tff(c_20,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_2'),k4_enumset1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8')) != k6_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_6629,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6626,c_20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 10:35:44 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.91/2.98  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.91/2.98  
% 8.91/2.98  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.91/2.98  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4
% 8.91/2.98  
% 8.91/2.98  %Foreground sorts:
% 8.91/2.98  
% 8.91/2.98  
% 8.91/2.98  %Background operators:
% 8.91/2.98  
% 8.91/2.98  
% 8.91/2.98  %Foreground operators:
% 8.91/2.98  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.91/2.98  tff(k1_tarski, type, k1_tarski: $i > $i).
% 8.91/2.98  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.91/2.98  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 8.91/2.98  tff('#skF_7', type, '#skF_7': $i).
% 8.91/2.98  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 8.91/2.98  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.91/2.98  tff('#skF_5', type, '#skF_5': $i).
% 8.91/2.98  tff('#skF_6', type, '#skF_6': $i).
% 8.91/2.98  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 8.91/2.98  tff('#skF_2', type, '#skF_2': $i).
% 8.91/2.98  tff('#skF_3', type, '#skF_3': $i).
% 8.91/2.98  tff('#skF_1', type, '#skF_1': $i).
% 8.91/2.98  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 8.91/2.98  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 8.91/2.98  tff('#skF_8', type, '#skF_8': $i).
% 8.91/2.98  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.91/2.98  tff('#skF_4', type, '#skF_4': $i).
% 8.91/2.98  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.91/2.98  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.91/2.98  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.91/2.98  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 8.91/2.98  
% 8.91/2.99  tff(f_43, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k1_tarski(A), k5_enumset1(B, C, D, E, F, G, H)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_enumset1)).
% 8.91/2.99  tff(f_41, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k1_tarski(A), k4_enumset1(B, C, D, E, F, G)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_enumset1)).
% 8.91/2.99  tff(f_35, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 8.91/2.99  tff(f_29, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_1)).
% 8.91/2.99  tff(f_46, negated_conjecture, ~(![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k2_tarski(A, B), k4_enumset1(C, D, E, F, G, H)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_enumset1)).
% 8.91/2.99  tff(c_18, plain, (![G_35, H_36, E_33, A_29, F_34, D_32, C_31, B_30]: (k2_xboole_0(k1_tarski(A_29), k5_enumset1(B_30, C_31, D_32, E_33, F_34, G_35, H_36))=k6_enumset1(A_29, B_30, C_31, D_32, E_33, F_34, G_35, H_36))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.91/2.99  tff(c_498, plain, (![G_92, C_89, E_90, F_91, A_88, B_94, D_93]: (k2_xboole_0(k1_tarski(A_88), k4_enumset1(B_94, C_89, D_93, E_90, F_91, G_92))=k5_enumset1(A_88, B_94, C_89, D_93, E_90, F_91, G_92))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.91/2.99  tff(c_10, plain, (![A_11, B_12]: (k2_xboole_0(k1_tarski(A_11), k1_tarski(B_12))=k2_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.91/2.99  tff(c_48, plain, (![A_43, B_44, C_45]: (k2_xboole_0(k2_xboole_0(A_43, B_44), C_45)=k2_xboole_0(A_43, k2_xboole_0(B_44, C_45)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 8.91/2.99  tff(c_63, plain, (![A_11, B_12, C_45]: (k2_xboole_0(k1_tarski(A_11), k2_xboole_0(k1_tarski(B_12), C_45))=k2_xboole_0(k2_tarski(A_11, B_12), C_45))), inference(superposition, [status(thm), theory('equality')], [c_10, c_48])).
% 8.91/2.99  tff(c_507, plain, (![G_92, C_89, E_90, F_91, A_88, B_94, A_11, D_93]: (k2_xboole_0(k2_tarski(A_11, A_88), k4_enumset1(B_94, C_89, D_93, E_90, F_91, G_92))=k2_xboole_0(k1_tarski(A_11), k5_enumset1(A_88, B_94, C_89, D_93, E_90, F_91, G_92)))), inference(superposition, [status(thm), theory('equality')], [c_498, c_63])).
% 8.91/2.99  tff(c_6626, plain, (![G_92, C_89, E_90, F_91, A_88, B_94, A_11, D_93]: (k2_xboole_0(k2_tarski(A_11, A_88), k4_enumset1(B_94, C_89, D_93, E_90, F_91, G_92))=k6_enumset1(A_11, A_88, B_94, C_89, D_93, E_90, F_91, G_92))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_507])).
% 8.91/2.99  tff(c_20, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), k4_enumset1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'))!=k6_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_46])).
% 8.91/2.99  tff(c_6629, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6626, c_20])).
% 8.91/2.99  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.91/2.99  
% 8.91/2.99  Inference rules
% 8.91/2.99  ----------------------
% 8.91/2.99  #Ref     : 0
% 8.91/2.99  #Sup     : 1603
% 8.91/2.99  #Fact    : 0
% 8.91/2.99  #Define  : 0
% 8.91/2.99  #Split   : 0
% 8.91/2.99  #Chain   : 0
% 8.91/2.99  #Close   : 0
% 8.91/2.99  
% 8.91/2.99  Ordering : KBO
% 8.91/2.99  
% 8.91/2.99  Simplification rules
% 8.91/2.99  ----------------------
% 8.91/2.99  #Subsume      : 0
% 8.91/2.99  #Demod        : 3668
% 8.91/2.99  #Tautology    : 728
% 8.91/2.99  #SimpNegUnit  : 0
% 8.91/2.99  #BackRed      : 1
% 8.91/2.99  
% 8.91/2.99  #Partial instantiations: 0
% 8.91/2.99  #Strategies tried      : 1
% 8.91/2.99  
% 8.91/2.99  Timing (in seconds)
% 8.91/2.99  ----------------------
% 8.91/2.99  Preprocessing        : 0.27
% 8.91/2.99  Parsing              : 0.15
% 8.91/2.99  CNF conversion       : 0.02
% 8.91/2.99  Main loop            : 1.97
% 8.91/2.99  Inferencing          : 0.61
% 8.91/2.99  Reduction            : 1.05
% 8.91/2.99  Demodulation         : 0.94
% 8.91/2.99  BG Simplification    : 0.10
% 8.91/2.99  Subsumption          : 0.16
% 8.91/2.99  Abstraction          : 0.18
% 8.91/2.99  MUC search           : 0.00
% 8.91/2.99  Cooper               : 0.00
% 8.91/2.99  Total                : 2.26
% 8.91/2.99  Index Insertion      : 0.00
% 8.91/3.00  Index Deletion       : 0.00
% 8.91/3.00  Index Matching       : 0.00
% 8.91/3.00  BG Taut test         : 0.00
%------------------------------------------------------------------------------
