%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:18 EST 2020

% Result     : Theorem 2.31s
% Output     : CNFRefutation 2.31s
% Verified   : 
% Statistics : Number of formulae       :   28 (  29 expanded)
%              Number of leaves         :   19 (  20 expanded)
%              Depth                    :    5
%              Number of atoms          :   13 (  14 expanded)
%              Number of equality atoms :   12 (  13 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff(f_29,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_tarski(A),k2_enumset1(B,C,D,E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_enumset1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,k2_xboole_0(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_1)).

tff(f_31,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k1_tarski(A),k3_enumset1(B,C,D,E,F)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_enumset1)).

tff(f_42,negated_conjecture,(
    ~ ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

tff(c_4,plain,(
    ! [A_3,D_6,C_5,E_7,B_4] : k2_xboole_0(k1_tarski(A_3),k2_enumset1(B_4,C_5,D_6,E_7)) = k3_enumset1(A_3,B_4,C_5,D_6,E_7) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_70,plain,(
    ! [C_39,D_37,E_36,A_38,B_40] : k2_xboole_0(k1_tarski(A_38),k2_enumset1(B_40,C_39,D_37,E_36)) = k3_enumset1(A_38,B_40,C_39,D_37,E_36) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2,plain,(
    ! [A_1,B_2] : k2_xboole_0(A_1,k2_xboole_0(A_1,B_2)) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_76,plain,(
    ! [C_39,D_37,E_36,A_38,B_40] : k2_xboole_0(k1_tarski(A_38),k3_enumset1(A_38,B_40,C_39,D_37,E_36)) = k2_xboole_0(k1_tarski(A_38),k2_enumset1(B_40,C_39,D_37,E_36)) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_2])).

tff(c_531,plain,(
    ! [A_76,C_80,E_77,D_78,B_79] : k2_xboole_0(k1_tarski(A_76),k3_enumset1(A_76,B_79,C_80,D_78,E_77)) = k3_enumset1(A_76,B_79,C_80,D_78,E_77) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_76])).

tff(c_6,plain,(
    ! [E_12,D_11,A_8,C_10,B_9,F_13] : k2_xboole_0(k1_tarski(A_8),k3_enumset1(B_9,C_10,D_11,E_12,F_13)) = k4_enumset1(A_8,B_9,C_10,D_11,E_12,F_13) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_537,plain,(
    ! [A_76,C_80,E_77,D_78,B_79] : k4_enumset1(A_76,A_76,B_79,C_80,D_78,E_77) = k3_enumset1(A_76,B_79,C_80,D_78,E_77) ),
    inference(superposition,[status(thm),theory(equality)],[c_531,c_6])).

tff(c_16,plain,(
    k4_enumset1('#skF_1','#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') != k3_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_753,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_537,c_16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:42:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.31/1.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.31/1.32  
% 2.31/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.31/1.32  %$ k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.31/1.32  
% 2.31/1.32  %Foreground sorts:
% 2.31/1.32  
% 2.31/1.32  
% 2.31/1.32  %Background operators:
% 2.31/1.32  
% 2.31/1.32  
% 2.31/1.32  %Foreground operators:
% 2.31/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.31/1.32  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.31/1.32  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.31/1.32  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.31/1.32  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.31/1.32  tff('#skF_5', type, '#skF_5': $i).
% 2.31/1.32  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.31/1.32  tff('#skF_2', type, '#skF_2': $i).
% 2.31/1.32  tff('#skF_3', type, '#skF_3': $i).
% 2.31/1.32  tff('#skF_1', type, '#skF_1': $i).
% 2.31/1.32  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.31/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.31/1.32  tff('#skF_4', type, '#skF_4': $i).
% 2.31/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.31/1.32  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.31/1.32  
% 2.31/1.33  tff(f_29, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_tarski(A), k2_enumset1(B, C, D, E)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_enumset1)).
% 2.31/1.33  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, k2_xboole_0(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_xboole_1)).
% 2.31/1.33  tff(f_31, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k1_tarski(A), k3_enumset1(B, C, D, E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_enumset1)).
% 2.31/1.33  tff(f_42, negated_conjecture, ~(![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 2.31/1.33  tff(c_4, plain, (![A_3, D_6, C_5, E_7, B_4]: (k2_xboole_0(k1_tarski(A_3), k2_enumset1(B_4, C_5, D_6, E_7))=k3_enumset1(A_3, B_4, C_5, D_6, E_7))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.31/1.33  tff(c_70, plain, (![C_39, D_37, E_36, A_38, B_40]: (k2_xboole_0(k1_tarski(A_38), k2_enumset1(B_40, C_39, D_37, E_36))=k3_enumset1(A_38, B_40, C_39, D_37, E_36))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.31/1.33  tff(c_2, plain, (![A_1, B_2]: (k2_xboole_0(A_1, k2_xboole_0(A_1, B_2))=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.31/1.33  tff(c_76, plain, (![C_39, D_37, E_36, A_38, B_40]: (k2_xboole_0(k1_tarski(A_38), k3_enumset1(A_38, B_40, C_39, D_37, E_36))=k2_xboole_0(k1_tarski(A_38), k2_enumset1(B_40, C_39, D_37, E_36)))), inference(superposition, [status(thm), theory('equality')], [c_70, c_2])).
% 2.31/1.33  tff(c_531, plain, (![A_76, C_80, E_77, D_78, B_79]: (k2_xboole_0(k1_tarski(A_76), k3_enumset1(A_76, B_79, C_80, D_78, E_77))=k3_enumset1(A_76, B_79, C_80, D_78, E_77))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_76])).
% 2.31/1.33  tff(c_6, plain, (![E_12, D_11, A_8, C_10, B_9, F_13]: (k2_xboole_0(k1_tarski(A_8), k3_enumset1(B_9, C_10, D_11, E_12, F_13))=k4_enumset1(A_8, B_9, C_10, D_11, E_12, F_13))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.31/1.33  tff(c_537, plain, (![A_76, C_80, E_77, D_78, B_79]: (k4_enumset1(A_76, A_76, B_79, C_80, D_78, E_77)=k3_enumset1(A_76, B_79, C_80, D_78, E_77))), inference(superposition, [status(thm), theory('equality')], [c_531, c_6])).
% 2.31/1.33  tff(c_16, plain, (k4_enumset1('#skF_1', '#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')!=k3_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.31/1.33  tff(c_753, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_537, c_16])).
% 2.31/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.31/1.33  
% 2.31/1.33  Inference rules
% 2.31/1.33  ----------------------
% 2.31/1.33  #Ref     : 0
% 2.31/1.33  #Sup     : 174
% 2.31/1.33  #Fact    : 0
% 2.31/1.33  #Define  : 0
% 2.31/1.33  #Split   : 0
% 2.31/1.33  #Chain   : 0
% 2.31/1.33  #Close   : 0
% 2.31/1.33  
% 2.31/1.33  Ordering : KBO
% 2.31/1.33  
% 2.31/1.33  Simplification rules
% 2.31/1.33  ----------------------
% 2.31/1.33  #Subsume      : 5
% 2.31/1.33  #Demod        : 137
% 2.31/1.33  #Tautology    : 132
% 2.31/1.33  #SimpNegUnit  : 0
% 2.31/1.33  #BackRed      : 1
% 2.31/1.33  
% 2.31/1.33  #Partial instantiations: 0
% 2.31/1.33  #Strategies tried      : 1
% 2.31/1.33  
% 2.31/1.33  Timing (in seconds)
% 2.31/1.33  ----------------------
% 2.31/1.33  Preprocessing        : 0.28
% 2.31/1.33  Parsing              : 0.15
% 2.31/1.33  CNF conversion       : 0.02
% 2.31/1.33  Main loop            : 0.30
% 2.31/1.33  Inferencing          : 0.12
% 2.31/1.33  Reduction            : 0.11
% 2.31/1.33  Demodulation         : 0.09
% 2.31/1.33  BG Simplification    : 0.02
% 2.31/1.33  Subsumption          : 0.03
% 2.31/1.33  Abstraction          : 0.02
% 2.31/1.33  MUC search           : 0.00
% 2.31/1.33  Cooper               : 0.00
% 2.31/1.33  Total                : 0.60
% 2.31/1.33  Index Insertion      : 0.00
% 2.31/1.33  Index Deletion       : 0.00
% 2.31/1.33  Index Matching       : 0.00
% 2.31/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
