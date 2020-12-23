%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:02 EST 2020

% Result     : Theorem 3.71s
% Output     : CNFRefutation 3.71s
% Verified   : 
% Statistics : Number of formulae       :   45 (  52 expanded)
%              Number of leaves         :   27 (  31 expanded)
%              Depth                    :    9
%              Number of atoms          :   25 (  32 expanded)
%              Number of equality atoms :   24 (  31 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_33,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k2_enumset1(A,B,C,D),k2_enumset1(E,F,G,H)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l75_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_tarski(A),k1_enumset1(B,C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k1_tarski(A),k2_tarski(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).

tff(f_35,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_31,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k2_enumset1(A,B,C,D),k1_enumset1(E,F,G)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l68_enumset1)).

tff(f_54,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k5_enumset1(A,B,C,D,E,F,G),k1_tarski(H)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_enumset1)).

tff(c_8,plain,(
    ! [C_18,B_17,A_16,D_19,G_22,E_20,H_23,F_21] : k2_xboole_0(k2_enumset1(A_16,B_17,C_18,D_19),k2_enumset1(E_20,F_21,G_22,H_23)) = k6_enumset1(A_16,B_17,C_18,D_19,E_20,F_21,G_22,H_23) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_14,plain,(
    ! [A_29,B_30,C_31,D_32] : k2_xboole_0(k1_tarski(A_29),k1_enumset1(B_30,C_31,D_32)) = k2_enumset1(A_29,B_30,C_31,D_32) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_12,plain,(
    ! [A_26,B_27,C_28] : k2_xboole_0(k1_tarski(A_26),k2_tarski(B_27,C_28)) = k1_enumset1(A_26,B_27,C_28) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_10,plain,(
    ! [A_24,B_25] : k2_xboole_0(k1_tarski(A_24),k1_tarski(B_25)) = k2_tarski(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_47,plain,(
    ! [A_75,B_76,C_77] : k2_xboole_0(k2_xboole_0(A_75,B_76),C_77) = k2_xboole_0(A_75,k2_xboole_0(B_76,C_77)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_82,plain,(
    ! [A_82,B_83,C_84] : k2_xboole_0(k1_tarski(A_82),k2_xboole_0(k1_tarski(B_83),C_84)) = k2_xboole_0(k2_tarski(A_82,B_83),C_84) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_47])).

tff(c_106,plain,(
    ! [A_82,A_24,B_25] : k2_xboole_0(k2_tarski(A_82,A_24),k1_tarski(B_25)) = k2_xboole_0(k1_tarski(A_82),k2_tarski(A_24,B_25)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_82])).

tff(c_111,plain,(
    ! [A_82,A_24,B_25] : k2_xboole_0(k2_tarski(A_82,A_24),k1_tarski(B_25)) = k1_enumset1(A_82,A_24,B_25) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_106])).

tff(c_175,plain,(
    ! [A_107,B_108,C_109,C_110] : k2_xboole_0(k1_tarski(A_107),k2_xboole_0(k2_tarski(B_108,C_109),C_110)) = k2_xboole_0(k1_enumset1(A_107,B_108,C_109),C_110) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_47])).

tff(c_193,plain,(
    ! [A_107,A_82,A_24,B_25] : k2_xboole_0(k1_enumset1(A_107,A_82,A_24),k1_tarski(B_25)) = k2_xboole_0(k1_tarski(A_107),k1_enumset1(A_82,A_24,B_25)) ),
    inference(superposition,[status(thm),theory(equality)],[c_111,c_175])).

tff(c_198,plain,(
    ! [A_107,A_82,A_24,B_25] : k2_xboole_0(k1_enumset1(A_107,A_82,A_24),k1_tarski(B_25)) = k2_enumset1(A_107,A_82,A_24,B_25) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_193])).

tff(c_434,plain,(
    ! [A_170,C_166,D_167,E_168,B_165,G_169,F_164] : k2_xboole_0(k2_enumset1(A_170,B_165,C_166,D_167),k1_enumset1(E_168,F_164,G_169)) = k5_enumset1(A_170,B_165,C_166,D_167,E_168,F_164,G_169) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] : k2_xboole_0(k2_xboole_0(A_1,B_2),C_3) = k2_xboole_0(A_1,k2_xboole_0(B_2,C_3)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_914,plain,(
    ! [A_279,G_280,C_285,F_284,C_286,E_283,D_281,B_282] : k2_xboole_0(k2_enumset1(A_279,B_282,C_286,D_281),k2_xboole_0(k1_enumset1(E_283,F_284,G_280),C_285)) = k2_xboole_0(k5_enumset1(A_279,B_282,C_286,D_281,E_283,F_284,G_280),C_285) ),
    inference(superposition,[status(thm),theory(equality)],[c_434,c_2])).

tff(c_947,plain,(
    ! [A_279,A_24,A_82,B_25,A_107,C_286,D_281,B_282] : k2_xboole_0(k5_enumset1(A_279,B_282,C_286,D_281,A_107,A_82,A_24),k1_tarski(B_25)) = k2_xboole_0(k2_enumset1(A_279,B_282,C_286,D_281),k2_enumset1(A_107,A_82,A_24,B_25)) ),
    inference(superposition,[status(thm),theory(equality)],[c_198,c_914])).

tff(c_954,plain,(
    ! [A_279,A_24,A_82,B_25,A_107,C_286,D_281,B_282] : k2_xboole_0(k5_enumset1(A_279,B_282,C_286,D_281,A_107,A_82,A_24),k1_tarski(B_25)) = k6_enumset1(A_279,B_282,C_286,D_281,A_107,A_82,A_24,B_25) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_947])).

tff(c_28,plain,(
    k2_xboole_0(k5_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),k1_tarski('#skF_8')) != k6_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1024,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_954,c_28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.30  % Computer   : n022.cluster.edu
% 0.11/0.30  % Model      : x86_64 x86_64
% 0.11/0.30  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.30  % Memory     : 8042.1875MB
% 0.11/0.30  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.30  % CPULimit   : 60
% 0.11/0.30  % DateTime   : Tue Dec  1 20:11:40 EST 2020
% 0.11/0.30  % CPUTime    : 
% 0.11/0.31  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.71/1.71  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.71/1.71  
% 3.71/1.71  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.71/1.72  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4
% 3.71/1.72  
% 3.71/1.72  %Foreground sorts:
% 3.71/1.72  
% 3.71/1.72  
% 3.71/1.72  %Background operators:
% 3.71/1.72  
% 3.71/1.72  
% 3.71/1.72  %Foreground operators:
% 3.71/1.72  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.71/1.72  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.71/1.72  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.71/1.72  tff('#skF_7', type, '#skF_7': $i).
% 3.71/1.72  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.71/1.72  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.71/1.72  tff('#skF_5', type, '#skF_5': $i).
% 3.71/1.72  tff('#skF_6', type, '#skF_6': $i).
% 3.71/1.72  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.71/1.72  tff('#skF_2', type, '#skF_2': $i).
% 3.71/1.72  tff('#skF_3', type, '#skF_3': $i).
% 3.71/1.72  tff('#skF_1', type, '#skF_1': $i).
% 3.71/1.72  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.71/1.72  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.71/1.72  tff('#skF_8', type, '#skF_8': $i).
% 3.71/1.72  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.71/1.72  tff('#skF_4', type, '#skF_4': $i).
% 3.71/1.72  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.71/1.72  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.71/1.72  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.71/1.72  
% 3.71/1.73  tff(f_33, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k2_enumset1(A, B, C, D), k2_enumset1(E, F, G, H)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l75_enumset1)).
% 3.71/1.73  tff(f_39, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_tarski(A), k1_enumset1(B, C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_enumset1)).
% 3.71/1.73  tff(f_37, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k1_tarski(A), k2_tarski(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_enumset1)).
% 3.71/1.73  tff(f_35, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 3.71/1.73  tff(f_27, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 3.71/1.73  tff(f_31, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k2_enumset1(A, B, C, D), k1_enumset1(E, F, G)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l68_enumset1)).
% 3.71/1.73  tff(f_54, negated_conjecture, ~(![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k5_enumset1(A, B, C, D, E, F, G), k1_tarski(H)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t68_enumset1)).
% 3.71/1.73  tff(c_8, plain, (![C_18, B_17, A_16, D_19, G_22, E_20, H_23, F_21]: (k2_xboole_0(k2_enumset1(A_16, B_17, C_18, D_19), k2_enumset1(E_20, F_21, G_22, H_23))=k6_enumset1(A_16, B_17, C_18, D_19, E_20, F_21, G_22, H_23))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.71/1.73  tff(c_14, plain, (![A_29, B_30, C_31, D_32]: (k2_xboole_0(k1_tarski(A_29), k1_enumset1(B_30, C_31, D_32))=k2_enumset1(A_29, B_30, C_31, D_32))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.71/1.73  tff(c_12, plain, (![A_26, B_27, C_28]: (k2_xboole_0(k1_tarski(A_26), k2_tarski(B_27, C_28))=k1_enumset1(A_26, B_27, C_28))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.71/1.73  tff(c_10, plain, (![A_24, B_25]: (k2_xboole_0(k1_tarski(A_24), k1_tarski(B_25))=k2_tarski(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.71/1.73  tff(c_47, plain, (![A_75, B_76, C_77]: (k2_xboole_0(k2_xboole_0(A_75, B_76), C_77)=k2_xboole_0(A_75, k2_xboole_0(B_76, C_77)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.71/1.73  tff(c_82, plain, (![A_82, B_83, C_84]: (k2_xboole_0(k1_tarski(A_82), k2_xboole_0(k1_tarski(B_83), C_84))=k2_xboole_0(k2_tarski(A_82, B_83), C_84))), inference(superposition, [status(thm), theory('equality')], [c_10, c_47])).
% 3.71/1.73  tff(c_106, plain, (![A_82, A_24, B_25]: (k2_xboole_0(k2_tarski(A_82, A_24), k1_tarski(B_25))=k2_xboole_0(k1_tarski(A_82), k2_tarski(A_24, B_25)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_82])).
% 3.71/1.73  tff(c_111, plain, (![A_82, A_24, B_25]: (k2_xboole_0(k2_tarski(A_82, A_24), k1_tarski(B_25))=k1_enumset1(A_82, A_24, B_25))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_106])).
% 3.71/1.73  tff(c_175, plain, (![A_107, B_108, C_109, C_110]: (k2_xboole_0(k1_tarski(A_107), k2_xboole_0(k2_tarski(B_108, C_109), C_110))=k2_xboole_0(k1_enumset1(A_107, B_108, C_109), C_110))), inference(superposition, [status(thm), theory('equality')], [c_12, c_47])).
% 3.71/1.73  tff(c_193, plain, (![A_107, A_82, A_24, B_25]: (k2_xboole_0(k1_enumset1(A_107, A_82, A_24), k1_tarski(B_25))=k2_xboole_0(k1_tarski(A_107), k1_enumset1(A_82, A_24, B_25)))), inference(superposition, [status(thm), theory('equality')], [c_111, c_175])).
% 3.71/1.73  tff(c_198, plain, (![A_107, A_82, A_24, B_25]: (k2_xboole_0(k1_enumset1(A_107, A_82, A_24), k1_tarski(B_25))=k2_enumset1(A_107, A_82, A_24, B_25))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_193])).
% 3.71/1.73  tff(c_434, plain, (![A_170, C_166, D_167, E_168, B_165, G_169, F_164]: (k2_xboole_0(k2_enumset1(A_170, B_165, C_166, D_167), k1_enumset1(E_168, F_164, G_169))=k5_enumset1(A_170, B_165, C_166, D_167, E_168, F_164, G_169))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.71/1.73  tff(c_2, plain, (![A_1, B_2, C_3]: (k2_xboole_0(k2_xboole_0(A_1, B_2), C_3)=k2_xboole_0(A_1, k2_xboole_0(B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.71/1.73  tff(c_914, plain, (![A_279, G_280, C_285, F_284, C_286, E_283, D_281, B_282]: (k2_xboole_0(k2_enumset1(A_279, B_282, C_286, D_281), k2_xboole_0(k1_enumset1(E_283, F_284, G_280), C_285))=k2_xboole_0(k5_enumset1(A_279, B_282, C_286, D_281, E_283, F_284, G_280), C_285))), inference(superposition, [status(thm), theory('equality')], [c_434, c_2])).
% 3.71/1.73  tff(c_947, plain, (![A_279, A_24, A_82, B_25, A_107, C_286, D_281, B_282]: (k2_xboole_0(k5_enumset1(A_279, B_282, C_286, D_281, A_107, A_82, A_24), k1_tarski(B_25))=k2_xboole_0(k2_enumset1(A_279, B_282, C_286, D_281), k2_enumset1(A_107, A_82, A_24, B_25)))), inference(superposition, [status(thm), theory('equality')], [c_198, c_914])).
% 3.71/1.73  tff(c_954, plain, (![A_279, A_24, A_82, B_25, A_107, C_286, D_281, B_282]: (k2_xboole_0(k5_enumset1(A_279, B_282, C_286, D_281, A_107, A_82, A_24), k1_tarski(B_25))=k6_enumset1(A_279, B_282, C_286, D_281, A_107, A_82, A_24, B_25))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_947])).
% 3.71/1.73  tff(c_28, plain, (k2_xboole_0(k5_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), k1_tarski('#skF_8'))!=k6_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.71/1.73  tff(c_1024, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_954, c_28])).
% 3.71/1.73  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.71/1.73  
% 3.71/1.73  Inference rules
% 3.71/1.73  ----------------------
% 3.71/1.73  #Ref     : 0
% 3.71/1.73  #Sup     : 267
% 3.71/1.73  #Fact    : 0
% 3.71/1.73  #Define  : 0
% 3.71/1.73  #Split   : 0
% 3.71/1.73  #Chain   : 0
% 3.71/1.73  #Close   : 0
% 3.71/1.73  
% 3.71/1.73  Ordering : KBO
% 3.71/1.73  
% 3.71/1.73  Simplification rules
% 3.71/1.73  ----------------------
% 3.71/1.73  #Subsume      : 0
% 3.71/1.73  #Demod        : 137
% 3.71/1.73  #Tautology    : 133
% 3.71/1.73  #SimpNegUnit  : 0
% 3.71/1.73  #BackRed      : 1
% 3.71/1.73  
% 3.71/1.73  #Partial instantiations: 0
% 3.71/1.73  #Strategies tried      : 1
% 3.71/1.73  
% 3.71/1.73  Timing (in seconds)
% 3.71/1.73  ----------------------
% 3.71/1.73  Preprocessing        : 0.39
% 3.71/1.73  Parsing              : 0.22
% 3.71/1.73  CNF conversion       : 0.02
% 3.71/1.73  Main loop            : 0.56
% 3.71/1.73  Inferencing          : 0.25
% 3.71/1.73  Reduction            : 0.19
% 3.71/1.73  Demodulation         : 0.16
% 3.71/1.73  BG Simplification    : 0.04
% 3.71/1.73  Subsumption          : 0.06
% 3.71/1.73  Abstraction          : 0.04
% 3.71/1.73  MUC search           : 0.00
% 3.71/1.73  Cooper               : 0.00
% 3.71/1.73  Total                : 0.98
% 3.71/1.73  Index Insertion      : 0.00
% 3.71/1.73  Index Deletion       : 0.00
% 3.71/1.73  Index Matching       : 0.00
% 3.71/1.73  BG Taut test         : 0.00
%------------------------------------------------------------------------------
