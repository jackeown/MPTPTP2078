%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:21 EST 2020

% Result     : Theorem 50.18s
% Output     : CNFRefutation 50.18s
% Verified   : 
% Statistics : Number of formulae       :   52 (  67 expanded)
%              Number of leaves         :   29 (  36 expanded)
%              Depth                    :    8
%              Number of atoms          :   32 (  47 expanded)
%              Number of equality atoms :   31 (  46 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

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

tff(f_37,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k1_enumset1(A,B,C),k2_enumset1(D,E,F,G)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_enumset1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_33,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k2_enumset1(A,B,C,D),k1_enumset1(E,F,G)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l68_enumset1)).

tff(f_47,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_tarski(A),k1_enumset1(B,C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k5_enumset1(A,B,C,D,E,F,G),k1_tarski(H)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_enumset1)).

tff(f_50,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G] : k6_enumset1(A,A,B,C,D,E,F,G) = k5_enumset1(A,B,C,D,E,F,G) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

tff(c_12,plain,(
    ! [A_19,C_21,D_22,B_20,F_24,E_23,G_25] : k2_xboole_0(k1_enumset1(A_19,B_20,C_21),k2_enumset1(D_22,E_23,F_24,G_25)) = k5_enumset1(A_19,B_20,C_21,D_22,E_23,F_24,G_25) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_1698,plain,(
    ! [E_111,A_110,D_115,F_109,G_114,C_113,B_112] : k2_xboole_0(k2_enumset1(A_110,B_112,C_113,D_115),k1_enumset1(E_111,F_109,G_114)) = k5_enumset1(A_110,B_112,C_113,D_115,E_111,F_109,G_114) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_20344,plain,(
    ! [D_253,E_251,G_249,B_254,A_248,C_250,F_252] : k2_xboole_0(k1_enumset1(E_251,F_252,G_249),k2_enumset1(A_248,B_254,C_250,D_253)) = k5_enumset1(A_248,B_254,C_250,D_253,E_251,F_252,G_249) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1698])).

tff(c_20515,plain,(
    ! [A_19,C_21,D_22,B_20,F_24,E_23,G_25] : k5_enumset1(D_22,E_23,F_24,G_25,A_19,B_20,C_21) = k5_enumset1(A_19,B_20,C_21,D_22,E_23,F_24,G_25) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_20344])).

tff(c_8,plain,(
    ! [E_12,D_11,A_8,C_10,B_9,F_13,G_14] : k2_xboole_0(k2_enumset1(A_8,B_9,C_10,D_11),k1_enumset1(E_12,F_13,G_14)) = k5_enumset1(A_8,B_9,C_10,D_11,E_12,F_13,G_14) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_22,plain,(
    ! [A_46,E_50,B_47,C_48,D_49,F_51] : k5_enumset1(A_46,A_46,B_47,C_48,D_49,E_50,F_51) = k4_enumset1(A_46,B_47,C_48,D_49,E_50,F_51) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_16,plain,(
    ! [A_34,B_35,C_36] : k2_enumset1(A_34,A_34,B_35,C_36) = k1_enumset1(A_34,B_35,C_36) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1749,plain,(
    ! [E_111,F_109,A_34,B_35,C_36,G_114] : k5_enumset1(A_34,A_34,B_35,C_36,E_111,F_109,G_114) = k2_xboole_0(k1_enumset1(A_34,B_35,C_36),k1_enumset1(E_111,F_109,G_114)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_1698])).

tff(c_1760,plain,(
    ! [E_111,F_109,A_34,B_35,C_36,G_114] : k2_xboole_0(k1_enumset1(A_34,B_35,C_36),k1_enumset1(E_111,F_109,G_114)) = k4_enumset1(A_34,B_35,C_36,E_111,F_109,G_114) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_1749])).

tff(c_685,plain,(
    ! [A_78,B_79,C_80,D_81] : k2_xboole_0(k1_tarski(A_78),k1_enumset1(B_79,C_80,D_81)) = k2_enumset1(A_78,B_79,C_80,D_81) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_4,plain,(
    ! [A_3,B_4,C_5] : k2_xboole_0(k2_xboole_0(A_3,B_4),C_5) = k2_xboole_0(A_3,k2_xboole_0(B_4,C_5)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_14770,plain,(
    ! [B_188,A_185,D_187,C_189,C_186] : k2_xboole_0(k1_tarski(A_185),k2_xboole_0(k1_enumset1(B_188,C_186,D_187),C_189)) = k2_xboole_0(k2_enumset1(A_185,B_188,C_186,D_187),C_189) ),
    inference(superposition,[status(thm),theory(equality)],[c_685,c_4])).

tff(c_15100,plain,(
    ! [A_185,E_111,F_109,A_34,B_35,C_36,G_114] : k2_xboole_0(k2_enumset1(A_185,A_34,B_35,C_36),k1_enumset1(E_111,F_109,G_114)) = k2_xboole_0(k1_tarski(A_185),k4_enumset1(A_34,B_35,C_36,E_111,F_109,G_114)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1760,c_14770])).

tff(c_15289,plain,(
    ! [A_185,E_111,F_109,A_34,B_35,C_36,G_114] : k2_xboole_0(k1_tarski(A_185),k4_enumset1(A_34,B_35,C_36,E_111,F_109,G_114)) = k5_enumset1(A_185,A_34,B_35,C_36,E_111,F_109,G_114) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_15100])).

tff(c_1762,plain,(
    ! [C_121,D_116,H_119,G_123,F_120,E_122,A_118,B_117] : k2_xboole_0(k5_enumset1(A_118,B_117,C_121,D_116,E_122,F_120,G_123),k1_tarski(H_119)) = k6_enumset1(A_118,B_117,C_121,D_116,E_122,F_120,G_123,H_119) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_22062,plain,(
    ! [B_293,E_297,D_295,A_299,H_296,F_294,C_298] : k6_enumset1(A_299,A_299,B_293,C_298,D_295,E_297,F_294,H_296) = k2_xboole_0(k4_enumset1(A_299,B_293,C_298,D_295,E_297,F_294),k1_tarski(H_296)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_1762])).

tff(c_22233,plain,(
    ! [B_293,E_297,D_295,A_299,H_296,F_294,C_298] : k6_enumset1(A_299,A_299,B_293,C_298,D_295,E_297,F_294,H_296) = k2_xboole_0(k1_tarski(H_296),k4_enumset1(A_299,B_293,C_298,D_295,E_297,F_294)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_22062])).

tff(c_58411,plain,(
    ! [B_293,E_297,D_295,A_299,H_296,F_294,C_298] : k6_enumset1(A_299,A_299,B_293,C_298,D_295,E_297,F_294,H_296) = k5_enumset1(H_296,A_299,B_293,C_298,D_295,E_297,F_294) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15289,c_22233])).

tff(c_24,plain,(
    k6_enumset1('#skF_1','#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7') != k5_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_32019,plain,(
    k6_enumset1('#skF_1','#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7') != k5_enumset1('#skF_4','#skF_5','#skF_6','#skF_7','#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20515,c_24])).

tff(c_58412,plain,(
    k5_enumset1('#skF_7','#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6') != k5_enumset1('#skF_4','#skF_5','#skF_6','#skF_7','#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58411,c_32019])).

tff(c_58416,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20515,c_58412])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:46:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 50.18/38.51  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 50.18/38.51  
% 50.18/38.51  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 50.18/38.52  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 50.18/38.52  
% 50.18/38.52  %Foreground sorts:
% 50.18/38.52  
% 50.18/38.52  
% 50.18/38.52  %Background operators:
% 50.18/38.52  
% 50.18/38.52  
% 50.18/38.52  %Foreground operators:
% 50.18/38.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 50.18/38.52  tff(k1_tarski, type, k1_tarski: $i > $i).
% 50.18/38.52  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 50.18/38.52  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 50.18/38.52  tff('#skF_7', type, '#skF_7': $i).
% 50.18/38.52  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 50.18/38.52  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 50.18/38.52  tff('#skF_5', type, '#skF_5': $i).
% 50.18/38.52  tff('#skF_6', type, '#skF_6': $i).
% 50.18/38.52  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 50.18/38.52  tff('#skF_2', type, '#skF_2': $i).
% 50.18/38.52  tff('#skF_3', type, '#skF_3': $i).
% 50.18/38.52  tff('#skF_1', type, '#skF_1': $i).
% 50.18/38.52  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 50.18/38.52  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 50.18/38.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 50.18/38.52  tff('#skF_4', type, '#skF_4': $i).
% 50.18/38.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 50.18/38.52  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 50.18/38.52  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 50.18/38.52  
% 50.18/38.53  tff(f_37, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k1_enumset1(A, B, C), k2_enumset1(D, E, F, G)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_enumset1)).
% 50.18/38.53  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 50.18/38.53  tff(f_33, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k2_enumset1(A, B, C, D), k1_enumset1(E, F, G)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l68_enumset1)).
% 50.18/38.53  tff(f_47, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 50.18/38.53  tff(f_41, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 50.18/38.53  tff(f_35, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_tarski(A), k1_enumset1(B, C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_enumset1)).
% 50.18/38.53  tff(f_29, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 50.18/38.53  tff(f_39, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k5_enumset1(A, B, C, D, E, F, G), k1_tarski(H)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t68_enumset1)).
% 50.18/38.53  tff(f_50, negated_conjecture, ~(![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 50.18/38.53  tff(c_12, plain, (![A_19, C_21, D_22, B_20, F_24, E_23, G_25]: (k2_xboole_0(k1_enumset1(A_19, B_20, C_21), k2_enumset1(D_22, E_23, F_24, G_25))=k5_enumset1(A_19, B_20, C_21, D_22, E_23, F_24, G_25))), inference(cnfTransformation, [status(thm)], [f_37])).
% 50.18/38.53  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 50.18/38.53  tff(c_1698, plain, (![E_111, A_110, D_115, F_109, G_114, C_113, B_112]: (k2_xboole_0(k2_enumset1(A_110, B_112, C_113, D_115), k1_enumset1(E_111, F_109, G_114))=k5_enumset1(A_110, B_112, C_113, D_115, E_111, F_109, G_114))), inference(cnfTransformation, [status(thm)], [f_33])).
% 50.18/38.53  tff(c_20344, plain, (![D_253, E_251, G_249, B_254, A_248, C_250, F_252]: (k2_xboole_0(k1_enumset1(E_251, F_252, G_249), k2_enumset1(A_248, B_254, C_250, D_253))=k5_enumset1(A_248, B_254, C_250, D_253, E_251, F_252, G_249))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1698])).
% 50.18/38.53  tff(c_20515, plain, (![A_19, C_21, D_22, B_20, F_24, E_23, G_25]: (k5_enumset1(D_22, E_23, F_24, G_25, A_19, B_20, C_21)=k5_enumset1(A_19, B_20, C_21, D_22, E_23, F_24, G_25))), inference(superposition, [status(thm), theory('equality')], [c_12, c_20344])).
% 50.18/38.53  tff(c_8, plain, (![E_12, D_11, A_8, C_10, B_9, F_13, G_14]: (k2_xboole_0(k2_enumset1(A_8, B_9, C_10, D_11), k1_enumset1(E_12, F_13, G_14))=k5_enumset1(A_8, B_9, C_10, D_11, E_12, F_13, G_14))), inference(cnfTransformation, [status(thm)], [f_33])).
% 50.18/38.53  tff(c_22, plain, (![A_46, E_50, B_47, C_48, D_49, F_51]: (k5_enumset1(A_46, A_46, B_47, C_48, D_49, E_50, F_51)=k4_enumset1(A_46, B_47, C_48, D_49, E_50, F_51))), inference(cnfTransformation, [status(thm)], [f_47])).
% 50.18/38.53  tff(c_16, plain, (![A_34, B_35, C_36]: (k2_enumset1(A_34, A_34, B_35, C_36)=k1_enumset1(A_34, B_35, C_36))), inference(cnfTransformation, [status(thm)], [f_41])).
% 50.18/38.53  tff(c_1749, plain, (![E_111, F_109, A_34, B_35, C_36, G_114]: (k5_enumset1(A_34, A_34, B_35, C_36, E_111, F_109, G_114)=k2_xboole_0(k1_enumset1(A_34, B_35, C_36), k1_enumset1(E_111, F_109, G_114)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_1698])).
% 50.18/38.53  tff(c_1760, plain, (![E_111, F_109, A_34, B_35, C_36, G_114]: (k2_xboole_0(k1_enumset1(A_34, B_35, C_36), k1_enumset1(E_111, F_109, G_114))=k4_enumset1(A_34, B_35, C_36, E_111, F_109, G_114))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_1749])).
% 50.18/38.53  tff(c_685, plain, (![A_78, B_79, C_80, D_81]: (k2_xboole_0(k1_tarski(A_78), k1_enumset1(B_79, C_80, D_81))=k2_enumset1(A_78, B_79, C_80, D_81))), inference(cnfTransformation, [status(thm)], [f_35])).
% 50.18/38.53  tff(c_4, plain, (![A_3, B_4, C_5]: (k2_xboole_0(k2_xboole_0(A_3, B_4), C_5)=k2_xboole_0(A_3, k2_xboole_0(B_4, C_5)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 50.18/38.53  tff(c_14770, plain, (![B_188, A_185, D_187, C_189, C_186]: (k2_xboole_0(k1_tarski(A_185), k2_xboole_0(k1_enumset1(B_188, C_186, D_187), C_189))=k2_xboole_0(k2_enumset1(A_185, B_188, C_186, D_187), C_189))), inference(superposition, [status(thm), theory('equality')], [c_685, c_4])).
% 50.18/38.53  tff(c_15100, plain, (![A_185, E_111, F_109, A_34, B_35, C_36, G_114]: (k2_xboole_0(k2_enumset1(A_185, A_34, B_35, C_36), k1_enumset1(E_111, F_109, G_114))=k2_xboole_0(k1_tarski(A_185), k4_enumset1(A_34, B_35, C_36, E_111, F_109, G_114)))), inference(superposition, [status(thm), theory('equality')], [c_1760, c_14770])).
% 50.18/38.53  tff(c_15289, plain, (![A_185, E_111, F_109, A_34, B_35, C_36, G_114]: (k2_xboole_0(k1_tarski(A_185), k4_enumset1(A_34, B_35, C_36, E_111, F_109, G_114))=k5_enumset1(A_185, A_34, B_35, C_36, E_111, F_109, G_114))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_15100])).
% 50.18/38.53  tff(c_1762, plain, (![C_121, D_116, H_119, G_123, F_120, E_122, A_118, B_117]: (k2_xboole_0(k5_enumset1(A_118, B_117, C_121, D_116, E_122, F_120, G_123), k1_tarski(H_119))=k6_enumset1(A_118, B_117, C_121, D_116, E_122, F_120, G_123, H_119))), inference(cnfTransformation, [status(thm)], [f_39])).
% 50.18/38.53  tff(c_22062, plain, (![B_293, E_297, D_295, A_299, H_296, F_294, C_298]: (k6_enumset1(A_299, A_299, B_293, C_298, D_295, E_297, F_294, H_296)=k2_xboole_0(k4_enumset1(A_299, B_293, C_298, D_295, E_297, F_294), k1_tarski(H_296)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_1762])).
% 50.18/38.53  tff(c_22233, plain, (![B_293, E_297, D_295, A_299, H_296, F_294, C_298]: (k6_enumset1(A_299, A_299, B_293, C_298, D_295, E_297, F_294, H_296)=k2_xboole_0(k1_tarski(H_296), k4_enumset1(A_299, B_293, C_298, D_295, E_297, F_294)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_22062])).
% 50.18/38.53  tff(c_58411, plain, (![B_293, E_297, D_295, A_299, H_296, F_294, C_298]: (k6_enumset1(A_299, A_299, B_293, C_298, D_295, E_297, F_294, H_296)=k5_enumset1(H_296, A_299, B_293, C_298, D_295, E_297, F_294))), inference(demodulation, [status(thm), theory('equality')], [c_15289, c_22233])).
% 50.18/38.53  tff(c_24, plain, (k6_enumset1('#skF_1', '#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')!=k5_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_50])).
% 50.18/38.53  tff(c_32019, plain, (k6_enumset1('#skF_1', '#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')!=k5_enumset1('#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_20515, c_24])).
% 50.18/38.53  tff(c_58412, plain, (k5_enumset1('#skF_7', '#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')!=k5_enumset1('#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58411, c_32019])).
% 50.18/38.53  tff(c_58416, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20515, c_58412])).
% 50.18/38.53  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 50.18/38.53  
% 50.18/38.53  Inference rules
% 50.18/38.53  ----------------------
% 50.18/38.53  #Ref     : 0
% 50.18/38.53  #Sup     : 14992
% 50.18/38.53  #Fact    : 0
% 50.18/38.53  #Define  : 0
% 50.18/38.53  #Split   : 0
% 50.18/38.53  #Chain   : 0
% 50.18/38.53  #Close   : 0
% 50.18/38.53  
% 50.18/38.53  Ordering : KBO
% 50.18/38.53  
% 50.18/38.53  Simplification rules
% 50.18/38.53  ----------------------
% 50.18/38.53  #Subsume      : 2350
% 50.18/38.53  #Demod        : 15478
% 50.18/38.53  #Tautology    : 2479
% 50.18/38.53  #SimpNegUnit  : 0
% 50.18/38.53  #BackRed      : 3
% 50.18/38.53  
% 50.18/38.53  #Partial instantiations: 0
% 50.18/38.53  #Strategies tried      : 1
% 50.18/38.53  
% 50.18/38.53  Timing (in seconds)
% 50.18/38.53  ----------------------
% 50.18/38.53  Preprocessing        : 0.30
% 50.18/38.53  Parsing              : 0.16
% 50.18/38.53  CNF conversion       : 0.02
% 50.18/38.53  Main loop            : 37.46
% 50.18/38.53  Inferencing          : 2.43
% 50.18/38.53  Reduction            : 32.45
% 50.18/38.53  Demodulation         : 31.86
% 50.18/38.53  BG Simplification    : 0.52
% 50.18/38.53  Subsumption          : 1.58
% 50.18/38.53  Abstraction          : 0.84
% 50.18/38.53  MUC search           : 0.00
% 50.18/38.53  Cooper               : 0.00
% 50.18/38.53  Total                : 37.79
% 50.18/38.53  Index Insertion      : 0.00
% 50.18/38.53  Index Deletion       : 0.00
% 50.18/38.53  Index Matching       : 0.00
% 50.18/38.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
