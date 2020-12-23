%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:17 EST 2020

% Result     : Theorem 4.20s
% Output     : CNFRefutation 4.20s
% Verified   : 
% Statistics : Number of formulae       :   31 (  32 expanded)
%              Number of leaves         :   20 (  21 expanded)
%              Depth                    :    6
%              Number of atoms          :   16 (  17 expanded)
%              Number of equality atoms :   15 (  16 expanded)
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

tff(f_31,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_tarski(A),k2_enumset1(B,C,D,E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_enumset1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_29,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k1_tarski(A),k3_enumset1(B,C,D,E,F)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_enumset1)).

tff(f_44,negated_conjecture,(
    ~ ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

tff(c_6,plain,(
    ! [B_7,D_9,C_8,E_10,A_6] : k2_xboole_0(k1_tarski(A_6),k2_enumset1(B_7,C_8,D_9,E_10)) = k3_enumset1(A_6,B_7,C_8,D_9,E_10) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_198,plain,(
    ! [C_46,B_47,D_45,A_48,E_49] : k2_xboole_0(k1_tarski(A_48),k2_enumset1(B_47,C_46,D_45,E_49)) = k3_enumset1(A_48,B_47,C_46,D_45,E_49) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_55,plain,(
    ! [A_34,B_35,C_36] : k2_xboole_0(k2_xboole_0(A_34,B_35),C_36) = k2_xboole_0(A_34,k2_xboole_0(B_35,C_36)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_74,plain,(
    ! [A_1,C_36] : k2_xboole_0(A_1,k2_xboole_0(A_1,C_36)) = k2_xboole_0(A_1,C_36) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_55])).

tff(c_207,plain,(
    ! [C_46,B_47,D_45,A_48,E_49] : k2_xboole_0(k1_tarski(A_48),k3_enumset1(A_48,B_47,C_46,D_45,E_49)) = k2_xboole_0(k1_tarski(A_48),k2_enumset1(B_47,C_46,D_45,E_49)) ),
    inference(superposition,[status(thm),theory(equality)],[c_198,c_74])).

tff(c_2642,plain,(
    ! [B_147,A_148,D_146,E_150,C_149] : k2_xboole_0(k1_tarski(A_148),k3_enumset1(A_148,B_147,C_149,D_146,E_150)) = k3_enumset1(A_148,B_147,C_149,D_146,E_150) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_207])).

tff(c_8,plain,(
    ! [F_16,D_14,E_15,B_12,A_11,C_13] : k2_xboole_0(k1_tarski(A_11),k3_enumset1(B_12,C_13,D_14,E_15,F_16)) = k4_enumset1(A_11,B_12,C_13,D_14,E_15,F_16) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2661,plain,(
    ! [B_147,A_148,D_146,E_150,C_149] : k4_enumset1(A_148,A_148,B_147,C_149,D_146,E_150) = k3_enumset1(A_148,B_147,C_149,D_146,E_150) ),
    inference(superposition,[status(thm),theory(equality)],[c_2642,c_8])).

tff(c_18,plain,(
    k4_enumset1('#skF_1','#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') != k3_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_2716,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2661,c_18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n025.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 16:38:20 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.20/1.73  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.20/1.73  
% 4.20/1.73  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.20/1.74  %$ k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.20/1.74  
% 4.20/1.74  %Foreground sorts:
% 4.20/1.74  
% 4.20/1.74  
% 4.20/1.74  %Background operators:
% 4.20/1.74  
% 4.20/1.74  
% 4.20/1.74  %Foreground operators:
% 4.20/1.74  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.20/1.74  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.20/1.74  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.20/1.74  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.20/1.74  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.20/1.74  tff('#skF_5', type, '#skF_5': $i).
% 4.20/1.74  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.20/1.74  tff('#skF_2', type, '#skF_2': $i).
% 4.20/1.74  tff('#skF_3', type, '#skF_3': $i).
% 4.20/1.74  tff('#skF_1', type, '#skF_1': $i).
% 4.20/1.74  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.20/1.74  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.20/1.74  tff('#skF_4', type, '#skF_4': $i).
% 4.20/1.74  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.20/1.74  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.20/1.74  
% 4.20/1.75  tff(f_31, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_tarski(A), k2_enumset1(B, C, D, E)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_enumset1)).
% 4.20/1.75  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 4.20/1.75  tff(f_29, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_1)).
% 4.20/1.75  tff(f_33, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k1_tarski(A), k3_enumset1(B, C, D, E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_enumset1)).
% 4.20/1.75  tff(f_44, negated_conjecture, ~(![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 4.20/1.75  tff(c_6, plain, (![B_7, D_9, C_8, E_10, A_6]: (k2_xboole_0(k1_tarski(A_6), k2_enumset1(B_7, C_8, D_9, E_10))=k3_enumset1(A_6, B_7, C_8, D_9, E_10))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.20/1.75  tff(c_198, plain, (![C_46, B_47, D_45, A_48, E_49]: (k2_xboole_0(k1_tarski(A_48), k2_enumset1(B_47, C_46, D_45, E_49))=k3_enumset1(A_48, B_47, C_46, D_45, E_49))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.20/1.75  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.20/1.75  tff(c_55, plain, (![A_34, B_35, C_36]: (k2_xboole_0(k2_xboole_0(A_34, B_35), C_36)=k2_xboole_0(A_34, k2_xboole_0(B_35, C_36)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.20/1.75  tff(c_74, plain, (![A_1, C_36]: (k2_xboole_0(A_1, k2_xboole_0(A_1, C_36))=k2_xboole_0(A_1, C_36))), inference(superposition, [status(thm), theory('equality')], [c_2, c_55])).
% 4.20/1.75  tff(c_207, plain, (![C_46, B_47, D_45, A_48, E_49]: (k2_xboole_0(k1_tarski(A_48), k3_enumset1(A_48, B_47, C_46, D_45, E_49))=k2_xboole_0(k1_tarski(A_48), k2_enumset1(B_47, C_46, D_45, E_49)))), inference(superposition, [status(thm), theory('equality')], [c_198, c_74])).
% 4.20/1.75  tff(c_2642, plain, (![B_147, A_148, D_146, E_150, C_149]: (k2_xboole_0(k1_tarski(A_148), k3_enumset1(A_148, B_147, C_149, D_146, E_150))=k3_enumset1(A_148, B_147, C_149, D_146, E_150))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_207])).
% 4.20/1.75  tff(c_8, plain, (![F_16, D_14, E_15, B_12, A_11, C_13]: (k2_xboole_0(k1_tarski(A_11), k3_enumset1(B_12, C_13, D_14, E_15, F_16))=k4_enumset1(A_11, B_12, C_13, D_14, E_15, F_16))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.20/1.75  tff(c_2661, plain, (![B_147, A_148, D_146, E_150, C_149]: (k4_enumset1(A_148, A_148, B_147, C_149, D_146, E_150)=k3_enumset1(A_148, B_147, C_149, D_146, E_150))), inference(superposition, [status(thm), theory('equality')], [c_2642, c_8])).
% 4.20/1.75  tff(c_18, plain, (k4_enumset1('#skF_1', '#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')!=k3_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.20/1.75  tff(c_2716, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2661, c_18])).
% 4.20/1.75  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.20/1.75  
% 4.20/1.75  Inference rules
% 4.20/1.75  ----------------------
% 4.20/1.75  #Ref     : 0
% 4.20/1.75  #Sup     : 631
% 4.20/1.75  #Fact    : 0
% 4.20/1.75  #Define  : 0
% 4.20/1.75  #Split   : 0
% 4.20/1.75  #Chain   : 0
% 4.20/1.75  #Close   : 0
% 4.20/1.75  
% 4.20/1.75  Ordering : KBO
% 4.20/1.75  
% 4.20/1.75  Simplification rules
% 4.20/1.75  ----------------------
% 4.20/1.75  #Subsume      : 35
% 4.20/1.75  #Demod        : 870
% 4.20/1.75  #Tautology    : 427
% 4.20/1.75  #SimpNegUnit  : 0
% 4.20/1.75  #BackRed      : 1
% 4.20/1.75  
% 4.20/1.75  #Partial instantiations: 0
% 4.20/1.75  #Strategies tried      : 1
% 4.20/1.75  
% 4.20/1.75  Timing (in seconds)
% 4.20/1.75  ----------------------
% 4.20/1.75  Preprocessing        : 0.28
% 4.20/1.75  Parsing              : 0.15
% 4.20/1.75  CNF conversion       : 0.02
% 4.20/1.75  Main loop            : 0.70
% 4.20/1.75  Inferencing          : 0.26
% 4.20/1.75  Reduction            : 0.32
% 4.20/1.75  Demodulation         : 0.28
% 4.20/1.75  BG Simplification    : 0.03
% 4.20/1.75  Subsumption          : 0.06
% 4.20/1.75  Abstraction          : 0.05
% 4.20/1.75  MUC search           : 0.00
% 4.20/1.75  Cooper               : 0.00
% 4.20/1.75  Total                : 1.01
% 4.20/1.75  Index Insertion      : 0.00
% 4.20/1.75  Index Deletion       : 0.00
% 4.20/1.75  Index Matching       : 0.00
% 4.20/1.75  BG Taut test         : 0.00
%------------------------------------------------------------------------------
