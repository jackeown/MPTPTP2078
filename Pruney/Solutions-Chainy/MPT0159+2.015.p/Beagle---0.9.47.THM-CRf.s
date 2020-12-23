%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:23 EST 2020

% Result     : Theorem 1.70s
% Output     : CNFRefutation 1.70s
% Verified   : 
% Statistics : Number of formulae       :   26 (  26 expanded)
%              Number of leaves         :   19 (  19 expanded)
%              Depth                    :    4
%              Number of atoms          :   11 (  11 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k2_xboole_0 > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

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

tff(f_27,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k4_enumset1(A,B,C,D,E,F),k1_tarski(G)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k5_enumset1(A,B,C,D,E,F,G),k1_tarski(H)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_enumset1)).

tff(f_34,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G] : k6_enumset1(A,A,B,C,D,E,F,G) = k5_enumset1(A,B,C,D,E,F,G) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

tff(c_2,plain,(
    ! [B_2,C_3,A_1,E_5,D_4,G_7,F_6] : k2_xboole_0(k4_enumset1(A_1,B_2,C_3,D_4,E_5,F_6),k1_tarski(G_7)) = k5_enumset1(A_1,B_2,C_3,D_4,E_5,F_6,G_7) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [C_18,B_17,A_16,D_19,E_20,F_21] : k5_enumset1(A_16,A_16,B_17,C_18,D_19,E_20,F_21) = k4_enumset1(A_16,B_17,C_18,D_19,E_20,F_21) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_27,plain,(
    ! [C_39,B_38,H_41,A_36,E_37,D_42,G_40,F_35] : k2_xboole_0(k5_enumset1(A_36,B_38,C_39,D_42,E_37,F_35,G_40),k1_tarski(H_41)) = k6_enumset1(A_36,B_38,C_39,D_42,E_37,F_35,G_40,H_41) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_36,plain,(
    ! [H_41,C_18,B_17,A_16,D_19,E_20,F_21] : k6_enumset1(A_16,A_16,B_17,C_18,D_19,E_20,F_21,H_41) = k2_xboole_0(k4_enumset1(A_16,B_17,C_18,D_19,E_20,F_21),k1_tarski(H_41)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_27])).

tff(c_39,plain,(
    ! [H_41,C_18,B_17,A_16,D_19,E_20,F_21] : k6_enumset1(A_16,A_16,B_17,C_18,D_19,E_20,F_21,H_41) = k5_enumset1(A_16,B_17,C_18,D_19,E_20,F_21,H_41) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_36])).

tff(c_8,plain,(
    k6_enumset1('#skF_1','#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7') != k5_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_42,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_39,c_8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:56:08 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.70/1.09  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.70/1.09  
% 1.70/1.09  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.70/1.09  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k2_xboole_0 > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.70/1.09  
% 1.70/1.09  %Foreground sorts:
% 1.70/1.09  
% 1.70/1.09  
% 1.70/1.09  %Background operators:
% 1.70/1.09  
% 1.70/1.09  
% 1.70/1.09  %Foreground operators:
% 1.70/1.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.70/1.09  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.70/1.09  tff('#skF_7', type, '#skF_7': $i).
% 1.70/1.09  tff('#skF_5', type, '#skF_5': $i).
% 1.70/1.09  tff('#skF_6', type, '#skF_6': $i).
% 1.70/1.09  tff('#skF_2', type, '#skF_2': $i).
% 1.70/1.09  tff('#skF_3', type, '#skF_3': $i).
% 1.70/1.09  tff('#skF_1', type, '#skF_1': $i).
% 1.70/1.09  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.70/1.09  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 1.70/1.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.70/1.09  tff('#skF_4', type, '#skF_4': $i).
% 1.70/1.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.70/1.09  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.70/1.09  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.70/1.09  
% 1.70/1.10  tff(f_27, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k4_enumset1(A, B, C, D, E, F), k1_tarski(G)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_enumset1)).
% 1.70/1.10  tff(f_31, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 1.70/1.10  tff(f_29, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k5_enumset1(A, B, C, D, E, F, G), k1_tarski(H)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t68_enumset1)).
% 1.70/1.10  tff(f_34, negated_conjecture, ~(![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 1.70/1.10  tff(c_2, plain, (![B_2, C_3, A_1, E_5, D_4, G_7, F_6]: (k2_xboole_0(k4_enumset1(A_1, B_2, C_3, D_4, E_5, F_6), k1_tarski(G_7))=k5_enumset1(A_1, B_2, C_3, D_4, E_5, F_6, G_7))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.70/1.10  tff(c_6, plain, (![C_18, B_17, A_16, D_19, E_20, F_21]: (k5_enumset1(A_16, A_16, B_17, C_18, D_19, E_20, F_21)=k4_enumset1(A_16, B_17, C_18, D_19, E_20, F_21))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.70/1.10  tff(c_27, plain, (![C_39, B_38, H_41, A_36, E_37, D_42, G_40, F_35]: (k2_xboole_0(k5_enumset1(A_36, B_38, C_39, D_42, E_37, F_35, G_40), k1_tarski(H_41))=k6_enumset1(A_36, B_38, C_39, D_42, E_37, F_35, G_40, H_41))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.70/1.10  tff(c_36, plain, (![H_41, C_18, B_17, A_16, D_19, E_20, F_21]: (k6_enumset1(A_16, A_16, B_17, C_18, D_19, E_20, F_21, H_41)=k2_xboole_0(k4_enumset1(A_16, B_17, C_18, D_19, E_20, F_21), k1_tarski(H_41)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_27])).
% 1.70/1.10  tff(c_39, plain, (![H_41, C_18, B_17, A_16, D_19, E_20, F_21]: (k6_enumset1(A_16, A_16, B_17, C_18, D_19, E_20, F_21, H_41)=k5_enumset1(A_16, B_17, C_18, D_19, E_20, F_21, H_41))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_36])).
% 1.70/1.10  tff(c_8, plain, (k6_enumset1('#skF_1', '#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')!=k5_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.70/1.10  tff(c_42, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_39, c_8])).
% 1.70/1.10  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.70/1.10  
% 1.70/1.10  Inference rules
% 1.70/1.10  ----------------------
% 1.70/1.10  #Ref     : 0
% 1.70/1.10  #Sup     : 7
% 1.70/1.10  #Fact    : 0
% 1.70/1.10  #Define  : 0
% 1.70/1.10  #Split   : 0
% 1.70/1.10  #Chain   : 0
% 1.70/1.10  #Close   : 0
% 1.70/1.10  
% 1.70/1.10  Ordering : KBO
% 1.70/1.10  
% 1.70/1.10  Simplification rules
% 1.70/1.10  ----------------------
% 1.70/1.10  #Subsume      : 0
% 1.70/1.10  #Demod        : 2
% 1.70/1.10  #Tautology    : 6
% 1.70/1.10  #SimpNegUnit  : 0
% 1.70/1.10  #BackRed      : 1
% 1.70/1.10  
% 1.70/1.10  #Partial instantiations: 0
% 1.70/1.10  #Strategies tried      : 1
% 1.70/1.10  
% 1.70/1.10  Timing (in seconds)
% 1.70/1.10  ----------------------
% 1.70/1.10  Preprocessing        : 0.27
% 1.70/1.10  Parsing              : 0.14
% 1.70/1.10  CNF conversion       : 0.02
% 1.70/1.10  Main loop            : 0.07
% 1.70/1.10  Inferencing          : 0.04
% 1.70/1.10  Reduction            : 0.02
% 1.70/1.10  Demodulation         : 0.02
% 1.70/1.11  BG Simplification    : 0.01
% 1.70/1.11  Subsumption          : 0.01
% 1.70/1.11  Abstraction          : 0.01
% 1.70/1.11  MUC search           : 0.00
% 1.70/1.11  Cooper               : 0.00
% 1.70/1.11  Total                : 0.37
% 1.70/1.11  Index Insertion      : 0.00
% 1.70/1.11  Index Deletion       : 0.00
% 1.70/1.11  Index Matching       : 0.00
% 1.70/1.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------
