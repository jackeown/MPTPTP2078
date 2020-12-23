%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:59 EST 2020

% Result     : Theorem 3.36s
% Output     : CNFRefutation 3.36s
% Verified   : 
% Statistics : Number of formulae       :   35 (  35 expanded)
%              Number of leaves         :   26 (  26 expanded)
%              Depth                    :    5
%              Number of atoms          :   14 (  14 expanded)
%              Number of equality atoms :   13 (  13 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k6_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_3 > #skF_9 > #skF_8 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_50,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k1_enumset1(A,B,C),k3_enumset1(D,E,F,G,H)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_enumset1)).

tff(f_46,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k2_tarski(A,B),k1_enumset1(C,D,E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_enumset1)).

tff(f_48,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_enumset1(A,B,C),k2_tarski(D,E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_53,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k1_enumset1(F,G,H)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_enumset1)).

tff(c_30,plain,(
    ! [E_44,H_47,C_42,G_46,F_45,A_40,D_43,B_41] : k2_xboole_0(k1_enumset1(A_40,B_41,C_42),k3_enumset1(D_43,E_44,F_45,G_46,H_47)) = k6_enumset1(A_40,B_41,C_42,D_43,E_44,F_45,G_46,H_47) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_26,plain,(
    ! [D_33,A_30,C_32,B_31,E_34] : k2_xboole_0(k2_tarski(A_30,B_31),k1_enumset1(C_32,D_33,E_34)) = k3_enumset1(A_30,B_31,C_32,D_33,E_34) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_174,plain,(
    ! [E_88,D_89,C_87,B_90,A_86] : k2_xboole_0(k1_enumset1(A_86,B_90,C_87),k2_tarski(D_89,E_88)) = k3_enumset1(A_86,B_90,C_87,D_89,E_88) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_4,plain,(
    ! [A_5,B_6,C_7] : k2_xboole_0(k2_xboole_0(A_5,B_6),C_7) = k2_xboole_0(A_5,k2_xboole_0(B_6,C_7)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_442,plain,(
    ! [C_151,D_150,E_152,B_149,A_148,C_153] : k2_xboole_0(k1_enumset1(A_148,B_149,C_153),k2_xboole_0(k2_tarski(D_150,E_152),C_151)) = k2_xboole_0(k3_enumset1(A_148,B_149,C_153,D_150,E_152),C_151) ),
    inference(superposition,[status(thm),theory(equality)],[c_174,c_4])).

tff(c_463,plain,(
    ! [D_33,A_30,C_32,B_149,A_148,B_31,E_34,C_153] : k2_xboole_0(k3_enumset1(A_148,B_149,C_153,A_30,B_31),k1_enumset1(C_32,D_33,E_34)) = k2_xboole_0(k1_enumset1(A_148,B_149,C_153),k3_enumset1(A_30,B_31,C_32,D_33,E_34)) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_442])).

tff(c_473,plain,(
    ! [D_33,A_30,C_32,B_149,A_148,B_31,E_34,C_153] : k2_xboole_0(k3_enumset1(A_148,B_149,C_153,A_30,B_31),k1_enumset1(C_32,D_33,E_34)) = k6_enumset1(A_148,B_149,C_153,A_30,B_31,C_32,D_33,E_34) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_463])).

tff(c_32,plain,(
    k2_xboole_0(k3_enumset1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),k1_enumset1('#skF_8','#skF_9','#skF_10')) != k6_enumset1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8','#skF_9','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_795,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_473,c_32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.32  % Computer   : n018.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % DateTime   : Tue Dec  1 17:53:57 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.36/1.57  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.36/1.57  
% 3.36/1.57  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.36/1.58  %$ r2_hidden > k6_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_3 > #skF_9 > #skF_8 > #skF_4 > #skF_2 > #skF_1
% 3.36/1.58  
% 3.36/1.58  %Foreground sorts:
% 3.36/1.58  
% 3.36/1.58  
% 3.36/1.58  %Background operators:
% 3.36/1.58  
% 3.36/1.58  
% 3.36/1.58  %Foreground operators:
% 3.36/1.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.36/1.58  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.36/1.58  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.36/1.58  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.36/1.58  tff('#skF_7', type, '#skF_7': $i).
% 3.36/1.58  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.36/1.58  tff('#skF_10', type, '#skF_10': $i).
% 3.36/1.58  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.36/1.58  tff('#skF_5', type, '#skF_5': $i).
% 3.36/1.58  tff('#skF_6', type, '#skF_6': $i).
% 3.36/1.58  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.36/1.58  tff('#skF_3', type, '#skF_3': $i).
% 3.36/1.58  tff('#skF_9', type, '#skF_9': $i).
% 3.36/1.58  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.36/1.58  tff('#skF_8', type, '#skF_8': $i).
% 3.36/1.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.36/1.58  tff('#skF_4', type, '#skF_4': $i).
% 3.36/1.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.36/1.58  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.36/1.58  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.36/1.58  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.36/1.58  
% 3.36/1.58  tff(f_50, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k1_enumset1(A, B, C), k3_enumset1(D, E, F, G, H)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_enumset1)).
% 3.36/1.58  tff(f_46, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k2_tarski(A, B), k1_enumset1(C, D, E)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_enumset1)).
% 3.36/1.58  tff(f_48, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_enumset1(A, B, C), k2_tarski(D, E)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_enumset1)).
% 3.36/1.58  tff(f_29, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_1)).
% 3.36/1.58  tff(f_53, negated_conjecture, ~(![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k1_enumset1(F, G, H)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_enumset1)).
% 3.36/1.58  tff(c_30, plain, (![E_44, H_47, C_42, G_46, F_45, A_40, D_43, B_41]: (k2_xboole_0(k1_enumset1(A_40, B_41, C_42), k3_enumset1(D_43, E_44, F_45, G_46, H_47))=k6_enumset1(A_40, B_41, C_42, D_43, E_44, F_45, G_46, H_47))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.36/1.58  tff(c_26, plain, (![D_33, A_30, C_32, B_31, E_34]: (k2_xboole_0(k2_tarski(A_30, B_31), k1_enumset1(C_32, D_33, E_34))=k3_enumset1(A_30, B_31, C_32, D_33, E_34))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.36/1.58  tff(c_174, plain, (![E_88, D_89, C_87, B_90, A_86]: (k2_xboole_0(k1_enumset1(A_86, B_90, C_87), k2_tarski(D_89, E_88))=k3_enumset1(A_86, B_90, C_87, D_89, E_88))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.36/1.58  tff(c_4, plain, (![A_5, B_6, C_7]: (k2_xboole_0(k2_xboole_0(A_5, B_6), C_7)=k2_xboole_0(A_5, k2_xboole_0(B_6, C_7)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.36/1.58  tff(c_442, plain, (![C_151, D_150, E_152, B_149, A_148, C_153]: (k2_xboole_0(k1_enumset1(A_148, B_149, C_153), k2_xboole_0(k2_tarski(D_150, E_152), C_151))=k2_xboole_0(k3_enumset1(A_148, B_149, C_153, D_150, E_152), C_151))), inference(superposition, [status(thm), theory('equality')], [c_174, c_4])).
% 3.36/1.58  tff(c_463, plain, (![D_33, A_30, C_32, B_149, A_148, B_31, E_34, C_153]: (k2_xboole_0(k3_enumset1(A_148, B_149, C_153, A_30, B_31), k1_enumset1(C_32, D_33, E_34))=k2_xboole_0(k1_enumset1(A_148, B_149, C_153), k3_enumset1(A_30, B_31, C_32, D_33, E_34)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_442])).
% 3.36/1.58  tff(c_473, plain, (![D_33, A_30, C_32, B_149, A_148, B_31, E_34, C_153]: (k2_xboole_0(k3_enumset1(A_148, B_149, C_153, A_30, B_31), k1_enumset1(C_32, D_33, E_34))=k6_enumset1(A_148, B_149, C_153, A_30, B_31, C_32, D_33, E_34))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_463])).
% 3.36/1.58  tff(c_32, plain, (k2_xboole_0(k3_enumset1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), k1_enumset1('#skF_8', '#skF_9', '#skF_10'))!=k6_enumset1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9', '#skF_10')), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.36/1.58  tff(c_795, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_473, c_32])).
% 3.36/1.58  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.36/1.58  
% 3.36/1.58  Inference rules
% 3.36/1.58  ----------------------
% 3.36/1.59  #Ref     : 0
% 3.36/1.59  #Sup     : 192
% 3.36/1.59  #Fact    : 0
% 3.36/1.59  #Define  : 0
% 3.36/1.59  #Split   : 0
% 3.36/1.59  #Chain   : 0
% 3.36/1.59  #Close   : 0
% 3.36/1.59  
% 3.36/1.59  Ordering : KBO
% 3.36/1.59  
% 3.36/1.59  Simplification rules
% 3.36/1.59  ----------------------
% 3.36/1.59  #Subsume      : 0
% 3.36/1.59  #Demod        : 115
% 3.36/1.59  #Tautology    : 106
% 3.36/1.59  #SimpNegUnit  : 0
% 3.36/1.59  #BackRed      : 4
% 3.36/1.59  
% 3.36/1.59  #Partial instantiations: 0
% 3.36/1.59  #Strategies tried      : 1
% 3.36/1.59  
% 3.36/1.59  Timing (in seconds)
% 3.36/1.59  ----------------------
% 3.36/1.59  Preprocessing        : 0.30
% 3.36/1.59  Parsing              : 0.16
% 3.36/1.59  CNF conversion       : 0.02
% 3.36/1.59  Main loop            : 0.54
% 3.36/1.59  Inferencing          : 0.24
% 3.36/1.59  Reduction            : 0.18
% 3.36/1.59  Demodulation         : 0.15
% 3.36/1.59  BG Simplification    : 0.04
% 3.36/1.59  Subsumption          : 0.06
% 3.36/1.59  Abstraction          : 0.05
% 3.36/1.59  MUC search           : 0.00
% 3.36/1.59  Cooper               : 0.00
% 3.36/1.59  Total                : 0.86
% 3.36/1.59  Index Insertion      : 0.00
% 3.36/1.59  Index Deletion       : 0.00
% 3.36/1.59  Index Matching       : 0.00
% 3.36/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
