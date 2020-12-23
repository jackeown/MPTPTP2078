%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:00 EST 2020

% Result     : Theorem 3.18s
% Output     : CNFRefutation 3.18s
% Verified   : 
% Statistics : Number of formulae       :   38 (  38 expanded)
%              Number of leaves         :   25 (  25 expanded)
%              Depth                    :    7
%              Number of atoms          :   20 (  20 expanded)
%              Number of equality atoms :   19 (  19 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_31,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k2_enumset1(A,B,C,D),k2_enumset1(E,F,G,H)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l75_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k2_tarski(A,B),k2_tarski(C,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l53_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k1_tarski(F)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_enumset1)).

tff(f_33,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k2_enumset1(A,B,C,D),k1_tarski(E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C,D] : k2_xboole_0(k2_xboole_0(k2_xboole_0(A,B),C),D) = k2_xboole_0(A,k2_xboole_0(k2_xboole_0(B,C),D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_xboole_1)).

tff(f_40,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k4_enumset1(A,B,C,D,E,F),k2_tarski(G,H)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_enumset1)).

tff(c_6,plain,(
    ! [C_11,E_13,B_10,H_16,F_14,G_15,D_12,A_9] : k2_xboole_0(k2_enumset1(A_9,B_10,C_11,D_12),k2_enumset1(E_13,F_14,G_15,H_16)) = k6_enumset1(A_9,B_10,C_11,D_12,E_13,F_14,G_15,H_16) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4,plain,(
    ! [A_5,B_6,C_7,D_8] : k2_xboole_0(k2_tarski(A_5,B_6),k2_tarski(C_7,D_8)) = k2_enumset1(A_5,B_6,C_7,D_8) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_12,plain,(
    ! [A_24,B_25,F_29,D_27,C_26,E_28] : k2_xboole_0(k3_enumset1(A_24,B_25,C_26,D_27,E_28),k1_tarski(F_29)) = k4_enumset1(A_24,B_25,C_26,D_27,E_28,F_29) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_8,plain,(
    ! [A_17,B_18] : k2_xboole_0(k1_tarski(A_17),k1_tarski(B_18)) = k2_tarski(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [A_19,C_21,D_22,B_20,E_23] : k2_xboole_0(k2_enumset1(A_19,B_20,C_21,D_22),k1_tarski(E_23)) = k3_enumset1(A_19,B_20,C_21,D_22,E_23) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_42,plain,(
    ! [A_41,B_42,C_43,D_44] : k2_xboole_0(k2_xboole_0(k2_xboole_0(A_41,B_42),C_43),D_44) = k2_xboole_0(A_41,k2_xboole_0(k2_xboole_0(B_42,C_43),D_44)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_574,plain,(
    ! [C_99,E_100,B_103,C_101,A_104,D_105,D_102] : k2_xboole_0(k2_enumset1(A_104,B_103,C_99,D_105),k2_xboole_0(k2_xboole_0(k1_tarski(E_100),C_101),D_102)) = k2_xboole_0(k2_xboole_0(k3_enumset1(A_104,B_103,C_99,D_105,E_100),C_101),D_102) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_42])).

tff(c_610,plain,(
    ! [C_99,B_103,A_104,B_18,A_17,D_105,D_102] : k2_xboole_0(k2_xboole_0(k3_enumset1(A_104,B_103,C_99,D_105,A_17),k1_tarski(B_18)),D_102) = k2_xboole_0(k2_enumset1(A_104,B_103,C_99,D_105),k2_xboole_0(k2_tarski(A_17,B_18),D_102)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_574])).

tff(c_621,plain,(
    ! [C_110,B_111,A_108,D_109,B_107,A_106,D_112] : k2_xboole_0(k2_enumset1(A_108,B_111,C_110,D_109),k2_xboole_0(k2_tarski(A_106,B_107),D_112)) = k2_xboole_0(k4_enumset1(A_108,B_111,C_110,D_109,A_106,B_107),D_112) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_610])).

tff(c_646,plain,(
    ! [C_110,B_111,A_108,D_109,B_6,C_7,D_8,A_5] : k2_xboole_0(k4_enumset1(A_108,B_111,C_110,D_109,A_5,B_6),k2_tarski(C_7,D_8)) = k2_xboole_0(k2_enumset1(A_108,B_111,C_110,D_109),k2_enumset1(A_5,B_6,C_7,D_8)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_621])).

tff(c_652,plain,(
    ! [C_110,B_111,A_108,D_109,B_6,C_7,D_8,A_5] : k2_xboole_0(k4_enumset1(A_108,B_111,C_110,D_109,A_5,B_6),k2_tarski(C_7,D_8)) = k6_enumset1(A_108,B_111,C_110,D_109,A_5,B_6,C_7,D_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_646])).

tff(c_14,plain,(
    k2_xboole_0(k4_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k2_tarski('#skF_7','#skF_8')) != k6_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_655,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_652,c_14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:50:41 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.18/1.49  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.18/1.49  
% 3.18/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.18/1.49  %$ k6_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4
% 3.18/1.49  
% 3.18/1.49  %Foreground sorts:
% 3.18/1.49  
% 3.18/1.49  
% 3.18/1.49  %Background operators:
% 3.18/1.49  
% 3.18/1.49  
% 3.18/1.49  %Foreground operators:
% 3.18/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.18/1.49  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.18/1.49  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.18/1.49  tff('#skF_7', type, '#skF_7': $i).
% 3.18/1.49  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.18/1.49  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.18/1.49  tff('#skF_5', type, '#skF_5': $i).
% 3.18/1.49  tff('#skF_6', type, '#skF_6': $i).
% 3.18/1.49  tff('#skF_2', type, '#skF_2': $i).
% 3.18/1.49  tff('#skF_3', type, '#skF_3': $i).
% 3.18/1.49  tff('#skF_1', type, '#skF_1': $i).
% 3.18/1.49  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.18/1.49  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.18/1.49  tff('#skF_8', type, '#skF_8': $i).
% 3.18/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.18/1.49  tff('#skF_4', type, '#skF_4': $i).
% 3.18/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.18/1.49  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.18/1.49  
% 3.18/1.50  tff(f_31, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k2_enumset1(A, B, C, D), k2_enumset1(E, F, G, H)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l75_enumset1)).
% 3.18/1.50  tff(f_29, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k2_tarski(A, B), k2_tarski(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l53_enumset1)).
% 3.18/1.50  tff(f_37, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k1_tarski(F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_enumset1)).
% 3.18/1.50  tff(f_33, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 3.18/1.50  tff(f_35, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k2_enumset1(A, B, C, D), k1_tarski(E)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_enumset1)).
% 3.18/1.50  tff(f_27, axiom, (![A, B, C, D]: (k2_xboole_0(k2_xboole_0(k2_xboole_0(A, B), C), D) = k2_xboole_0(A, k2_xboole_0(k2_xboole_0(B, C), D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_xboole_1)).
% 3.18/1.50  tff(f_40, negated_conjecture, ~(![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k4_enumset1(A, B, C, D, E, F), k2_tarski(G, H)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_enumset1)).
% 3.18/1.50  tff(c_6, plain, (![C_11, E_13, B_10, H_16, F_14, G_15, D_12, A_9]: (k2_xboole_0(k2_enumset1(A_9, B_10, C_11, D_12), k2_enumset1(E_13, F_14, G_15, H_16))=k6_enumset1(A_9, B_10, C_11, D_12, E_13, F_14, G_15, H_16))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.18/1.50  tff(c_4, plain, (![A_5, B_6, C_7, D_8]: (k2_xboole_0(k2_tarski(A_5, B_6), k2_tarski(C_7, D_8))=k2_enumset1(A_5, B_6, C_7, D_8))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.18/1.50  tff(c_12, plain, (![A_24, B_25, F_29, D_27, C_26, E_28]: (k2_xboole_0(k3_enumset1(A_24, B_25, C_26, D_27, E_28), k1_tarski(F_29))=k4_enumset1(A_24, B_25, C_26, D_27, E_28, F_29))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.18/1.50  tff(c_8, plain, (![A_17, B_18]: (k2_xboole_0(k1_tarski(A_17), k1_tarski(B_18))=k2_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.18/1.50  tff(c_10, plain, (![A_19, C_21, D_22, B_20, E_23]: (k2_xboole_0(k2_enumset1(A_19, B_20, C_21, D_22), k1_tarski(E_23))=k3_enumset1(A_19, B_20, C_21, D_22, E_23))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.18/1.50  tff(c_42, plain, (![A_41, B_42, C_43, D_44]: (k2_xboole_0(k2_xboole_0(k2_xboole_0(A_41, B_42), C_43), D_44)=k2_xboole_0(A_41, k2_xboole_0(k2_xboole_0(B_42, C_43), D_44)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.18/1.50  tff(c_574, plain, (![C_99, E_100, B_103, C_101, A_104, D_105, D_102]: (k2_xboole_0(k2_enumset1(A_104, B_103, C_99, D_105), k2_xboole_0(k2_xboole_0(k1_tarski(E_100), C_101), D_102))=k2_xboole_0(k2_xboole_0(k3_enumset1(A_104, B_103, C_99, D_105, E_100), C_101), D_102))), inference(superposition, [status(thm), theory('equality')], [c_10, c_42])).
% 3.18/1.50  tff(c_610, plain, (![C_99, B_103, A_104, B_18, A_17, D_105, D_102]: (k2_xboole_0(k2_xboole_0(k3_enumset1(A_104, B_103, C_99, D_105, A_17), k1_tarski(B_18)), D_102)=k2_xboole_0(k2_enumset1(A_104, B_103, C_99, D_105), k2_xboole_0(k2_tarski(A_17, B_18), D_102)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_574])).
% 3.18/1.50  tff(c_621, plain, (![C_110, B_111, A_108, D_109, B_107, A_106, D_112]: (k2_xboole_0(k2_enumset1(A_108, B_111, C_110, D_109), k2_xboole_0(k2_tarski(A_106, B_107), D_112))=k2_xboole_0(k4_enumset1(A_108, B_111, C_110, D_109, A_106, B_107), D_112))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_610])).
% 3.18/1.50  tff(c_646, plain, (![C_110, B_111, A_108, D_109, B_6, C_7, D_8, A_5]: (k2_xboole_0(k4_enumset1(A_108, B_111, C_110, D_109, A_5, B_6), k2_tarski(C_7, D_8))=k2_xboole_0(k2_enumset1(A_108, B_111, C_110, D_109), k2_enumset1(A_5, B_6, C_7, D_8)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_621])).
% 3.18/1.50  tff(c_652, plain, (![C_110, B_111, A_108, D_109, B_6, C_7, D_8, A_5]: (k2_xboole_0(k4_enumset1(A_108, B_111, C_110, D_109, A_5, B_6), k2_tarski(C_7, D_8))=k6_enumset1(A_108, B_111, C_110, D_109, A_5, B_6, C_7, D_8))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_646])).
% 3.18/1.50  tff(c_14, plain, (k2_xboole_0(k4_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k2_tarski('#skF_7', '#skF_8'))!=k6_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.18/1.50  tff(c_655, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_652, c_14])).
% 3.18/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.18/1.50  
% 3.18/1.50  Inference rules
% 3.18/1.50  ----------------------
% 3.18/1.50  #Ref     : 0
% 3.18/1.50  #Sup     : 153
% 3.18/1.50  #Fact    : 0
% 3.18/1.51  #Define  : 0
% 3.18/1.51  #Split   : 0
% 3.18/1.51  #Chain   : 0
% 3.18/1.51  #Close   : 0
% 3.18/1.51  
% 3.18/1.51  Ordering : KBO
% 3.18/1.51  
% 3.18/1.51  Simplification rules
% 3.18/1.51  ----------------------
% 3.18/1.51  #Subsume      : 0
% 3.18/1.51  #Demod        : 239
% 3.18/1.51  #Tautology    : 79
% 3.18/1.51  #SimpNegUnit  : 0
% 3.18/1.51  #BackRed      : 1
% 3.18/1.51  
% 3.18/1.51  #Partial instantiations: 0
% 3.18/1.51  #Strategies tried      : 1
% 3.18/1.51  
% 3.18/1.51  Timing (in seconds)
% 3.18/1.51  ----------------------
% 3.18/1.51  Preprocessing        : 0.28
% 3.18/1.51  Parsing              : 0.16
% 3.18/1.51  CNF conversion       : 0.02
% 3.18/1.51  Main loop            : 0.41
% 3.18/1.51  Inferencing          : 0.16
% 3.18/1.51  Reduction            : 0.18
% 3.18/1.51  Demodulation         : 0.16
% 3.18/1.51  BG Simplification    : 0.03
% 3.18/1.51  Subsumption          : 0.03
% 3.18/1.51  Abstraction          : 0.04
% 3.18/1.51  MUC search           : 0.00
% 3.18/1.51  Cooper               : 0.00
% 3.18/1.51  Total                : 0.71
% 3.18/1.51  Index Insertion      : 0.00
% 3.18/1.51  Index Deletion       : 0.00
% 3.18/1.51  Index Matching       : 0.00
% 3.18/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
