%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:47 EST 2020

% Result     : Theorem 1.82s
% Output     : CNFRefutation 1.82s
% Verified   : 
% Statistics : Number of formulae       :   30 (  30 expanded)
%              Number of leaves         :   21 (  21 expanded)
%              Depth                    :    5
%              Number of atoms          :   14 (  14 expanded)
%              Number of equality atoms :   13 (  13 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k4_enumset1 > k3_enumset1 > k2_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff(f_35,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k1_tarski(A),k3_enumset1(B,C,D,E,F)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k2_enumset1(A,B,C,D),k1_tarski(E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_tarski(A),k2_enumset1(B,C,D,E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_38,negated_conjecture,(
    ~ ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k1_tarski(F)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_enumset1)).

tff(c_10,plain,(
    ! [C_18,B_17,A_16,D_19,E_20,F_21] : k2_xboole_0(k1_tarski(A_16),k3_enumset1(B_17,C_18,D_19,E_20,F_21)) = k4_enumset1(A_16,B_17,C_18,D_19,E_20,F_21) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_8,plain,(
    ! [D_14,E_15,B_12,A_11,C_13] : k2_xboole_0(k2_enumset1(A_11,B_12,C_13,D_14),k1_tarski(E_15)) = k3_enumset1(A_11,B_12,C_13,D_14,E_15) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_39,plain,(
    ! [D_27,A_30,B_29,E_31,C_28] : k2_xboole_0(k1_tarski(A_30),k2_enumset1(B_29,C_28,D_27,E_31)) = k3_enumset1(A_30,B_29,C_28,D_27,E_31) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] : k2_xboole_0(k2_xboole_0(A_1,B_2),C_3) = k2_xboole_0(A_1,k2_xboole_0(B_2,C_3)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_94,plain,(
    ! [C_51,C_52,B_50,A_49,D_54,E_53] : k2_xboole_0(k1_tarski(A_49),k2_xboole_0(k2_enumset1(B_50,C_52,D_54,E_53),C_51)) = k2_xboole_0(k3_enumset1(A_49,B_50,C_52,D_54,E_53),C_51) ),
    inference(superposition,[status(thm),theory(equality)],[c_39,c_2])).

tff(c_112,plain,(
    ! [D_14,A_49,E_15,B_12,A_11,C_13] : k2_xboole_0(k3_enumset1(A_49,A_11,B_12,C_13,D_14),k1_tarski(E_15)) = k2_xboole_0(k1_tarski(A_49),k3_enumset1(A_11,B_12,C_13,D_14,E_15)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_94])).

tff(c_116,plain,(
    ! [D_14,A_49,E_15,B_12,A_11,C_13] : k2_xboole_0(k3_enumset1(A_49,A_11,B_12,C_13,D_14),k1_tarski(E_15)) = k4_enumset1(A_49,A_11,B_12,C_13,D_14,E_15) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_112])).

tff(c_12,plain,(
    k2_xboole_0(k3_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5'),k1_tarski('#skF_6')) != k4_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_119,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 17:53:07 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.82/1.16  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.82/1.16  
% 1.82/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.82/1.16  %$ k4_enumset1 > k3_enumset1 > k2_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.82/1.16  
% 1.82/1.16  %Foreground sorts:
% 1.82/1.16  
% 1.82/1.16  
% 1.82/1.16  %Background operators:
% 1.82/1.16  
% 1.82/1.16  
% 1.82/1.16  %Foreground operators:
% 1.82/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.82/1.16  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.82/1.16  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.82/1.16  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.82/1.16  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.82/1.16  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.82/1.16  tff('#skF_5', type, '#skF_5': $i).
% 1.82/1.16  tff('#skF_6', type, '#skF_6': $i).
% 1.82/1.16  tff('#skF_2', type, '#skF_2': $i).
% 1.82/1.16  tff('#skF_3', type, '#skF_3': $i).
% 1.82/1.16  tff('#skF_1', type, '#skF_1': $i).
% 1.82/1.16  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.82/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.82/1.16  tff('#skF_4', type, '#skF_4': $i).
% 1.82/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.82/1.16  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.82/1.16  
% 1.82/1.17  tff(f_35, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k1_tarski(A), k3_enumset1(B, C, D, E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_enumset1)).
% 1.82/1.17  tff(f_33, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k2_enumset1(A, B, C, D), k1_tarski(E)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_enumset1)).
% 1.82/1.17  tff(f_31, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_tarski(A), k2_enumset1(B, C, D, E)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_enumset1)).
% 1.82/1.17  tff(f_27, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_1)).
% 1.82/1.17  tff(f_38, negated_conjecture, ~(![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k1_tarski(F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_enumset1)).
% 1.82/1.17  tff(c_10, plain, (![C_18, B_17, A_16, D_19, E_20, F_21]: (k2_xboole_0(k1_tarski(A_16), k3_enumset1(B_17, C_18, D_19, E_20, F_21))=k4_enumset1(A_16, B_17, C_18, D_19, E_20, F_21))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.82/1.17  tff(c_8, plain, (![D_14, E_15, B_12, A_11, C_13]: (k2_xboole_0(k2_enumset1(A_11, B_12, C_13, D_14), k1_tarski(E_15))=k3_enumset1(A_11, B_12, C_13, D_14, E_15))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.82/1.17  tff(c_39, plain, (![D_27, A_30, B_29, E_31, C_28]: (k2_xboole_0(k1_tarski(A_30), k2_enumset1(B_29, C_28, D_27, E_31))=k3_enumset1(A_30, B_29, C_28, D_27, E_31))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.82/1.17  tff(c_2, plain, (![A_1, B_2, C_3]: (k2_xboole_0(k2_xboole_0(A_1, B_2), C_3)=k2_xboole_0(A_1, k2_xboole_0(B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.82/1.17  tff(c_94, plain, (![C_51, C_52, B_50, A_49, D_54, E_53]: (k2_xboole_0(k1_tarski(A_49), k2_xboole_0(k2_enumset1(B_50, C_52, D_54, E_53), C_51))=k2_xboole_0(k3_enumset1(A_49, B_50, C_52, D_54, E_53), C_51))), inference(superposition, [status(thm), theory('equality')], [c_39, c_2])).
% 1.82/1.17  tff(c_112, plain, (![D_14, A_49, E_15, B_12, A_11, C_13]: (k2_xboole_0(k3_enumset1(A_49, A_11, B_12, C_13, D_14), k1_tarski(E_15))=k2_xboole_0(k1_tarski(A_49), k3_enumset1(A_11, B_12, C_13, D_14, E_15)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_94])).
% 1.82/1.17  tff(c_116, plain, (![D_14, A_49, E_15, B_12, A_11, C_13]: (k2_xboole_0(k3_enumset1(A_49, A_11, B_12, C_13, D_14), k1_tarski(E_15))=k4_enumset1(A_49, A_11, B_12, C_13, D_14, E_15))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_112])).
% 1.82/1.17  tff(c_12, plain, (k2_xboole_0(k3_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), k1_tarski('#skF_6'))!=k4_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.82/1.17  tff(c_119, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_116, c_12])).
% 1.82/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.82/1.17  
% 1.82/1.17  Inference rules
% 1.82/1.17  ----------------------
% 1.82/1.17  #Ref     : 0
% 1.82/1.17  #Sup     : 26
% 1.82/1.17  #Fact    : 0
% 1.82/1.17  #Define  : 0
% 1.82/1.17  #Split   : 0
% 1.82/1.17  #Chain   : 0
% 1.82/1.17  #Close   : 0
% 1.82/1.17  
% 1.82/1.17  Ordering : KBO
% 1.82/1.17  
% 1.82/1.17  Simplification rules
% 1.82/1.17  ----------------------
% 1.82/1.17  #Subsume      : 0
% 1.82/1.17  #Demod        : 14
% 1.82/1.17  #Tautology    : 18
% 1.82/1.17  #SimpNegUnit  : 0
% 1.82/1.17  #BackRed      : 1
% 1.82/1.17  
% 1.82/1.17  #Partial instantiations: 0
% 1.82/1.17  #Strategies tried      : 1
% 1.82/1.17  
% 1.82/1.17  Timing (in seconds)
% 1.82/1.17  ----------------------
% 1.82/1.17  Preprocessing        : 0.27
% 1.82/1.17  Parsing              : 0.15
% 1.82/1.17  CNF conversion       : 0.02
% 1.82/1.17  Main loop            : 0.14
% 1.82/1.18  Inferencing          : 0.07
% 1.82/1.18  Reduction            : 0.04
% 1.82/1.18  Demodulation         : 0.03
% 1.82/1.18  BG Simplification    : 0.01
% 1.82/1.18  Subsumption          : 0.02
% 1.82/1.18  Abstraction          : 0.01
% 1.82/1.18  MUC search           : 0.00
% 1.82/1.18  Cooper               : 0.00
% 1.82/1.18  Total                : 0.43
% 1.82/1.18  Index Insertion      : 0.00
% 1.82/1.18  Index Deletion       : 0.00
% 1.82/1.18  Index Matching       : 0.00
% 1.82/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
