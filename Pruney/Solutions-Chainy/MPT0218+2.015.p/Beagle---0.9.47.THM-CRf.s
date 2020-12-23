%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:48 EST 2020

% Result     : Theorem 3.54s
% Output     : CNFRefutation 3.54s
% Verified   : 
% Statistics : Number of formulae       :   62 (  65 expanded)
%              Number of leaves         :   32 (  34 expanded)
%              Depth                    :   13
%              Number of atoms          :   44 (  47 expanded)
%              Number of equality atoms :   30 (  33 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_43,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_47,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_49,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_41,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_51,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_53,axiom,(
    ! [A,B,C,D,E,F,G] : k6_enumset1(A,A,B,C,D,E,F,G) = k5_enumset1(A,B,C,D,E,F,G) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k1_enumset1(A,B,C),k3_enumset1(D,E,F,G,H)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_enumset1)).

tff(f_31,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),k5_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_xboole_1)).

tff(f_56,negated_conjecture,(
    ~ ! [A,B] : r1_tarski(k1_tarski(A),k2_tarski(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_zfmisc_1)).

tff(c_18,plain,(
    ! [A_24,B_25] : k1_enumset1(A_24,A_24,B_25) = k2_tarski(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_20,plain,(
    ! [A_26,B_27,C_28] : k2_enumset1(A_26,A_26,B_27,C_28) = k1_enumset1(A_26,B_27,C_28) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_22,plain,(
    ! [A_29,B_30,C_31,D_32] : k3_enumset1(A_29,A_29,B_30,C_31,D_32) = k2_enumset1(A_29,B_30,C_31,D_32) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_24,plain,(
    ! [D_36,E_37,A_33,B_34,C_35] : k4_enumset1(A_33,A_33,B_34,C_35,D_36,E_37) = k3_enumset1(A_33,B_34,C_35,D_36,E_37) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_16,plain,(
    ! [A_23] : k2_tarski(A_23,A_23) = k1_tarski(A_23) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_26,plain,(
    ! [D_41,B_39,A_38,F_43,E_42,C_40] : k5_enumset1(A_38,A_38,B_39,C_40,D_41,E_42,F_43) = k4_enumset1(A_38,B_39,C_40,D_41,E_42,F_43) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_28,plain,(
    ! [C_46,E_48,F_49,G_50,A_44,B_45,D_47] : k6_enumset1(A_44,A_44,B_45,C_46,D_47,E_48,F_49,G_50) = k5_enumset1(A_44,B_45,C_46,D_47,E_48,F_49,G_50) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_471,plain,(
    ! [D_122,A_127,G_123,E_126,H_121,B_124,C_120,F_125] : k2_xboole_0(k1_enumset1(A_127,B_124,C_120),k3_enumset1(D_122,E_126,F_125,G_123,H_121)) = k6_enumset1(A_127,B_124,C_120,D_122,E_126,F_125,G_123,H_121) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_486,plain,(
    ! [A_24,D_122,G_123,B_25,E_126,H_121,F_125] : k6_enumset1(A_24,A_24,B_25,D_122,E_126,F_125,G_123,H_121) = k2_xboole_0(k2_tarski(A_24,B_25),k3_enumset1(D_122,E_126,F_125,G_123,H_121)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_471])).

tff(c_1930,plain,(
    ! [E_191,F_187,D_190,B_186,A_189,G_185,H_188] : k2_xboole_0(k2_tarski(A_189,B_186),k3_enumset1(D_190,E_191,F_187,G_185,H_188)) = k5_enumset1(A_189,B_186,D_190,E_191,F_187,G_185,H_188) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_486])).

tff(c_6,plain,(
    ! [A_6,B_7] : k2_xboole_0(A_6,k3_xboole_0(A_6,B_7)) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_128,plain,(
    ! [A_74,B_75,C_76] : k4_xboole_0(k3_xboole_0(A_74,B_75),C_76) = k3_xboole_0(A_74,k4_xboole_0(B_75,C_76)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_12,plain,(
    ! [A_13,B_14] : k5_xboole_0(A_13,k4_xboole_0(B_14,A_13)) = k2_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_235,plain,(
    ! [C_94,A_95,B_96] : k5_xboole_0(C_94,k3_xboole_0(A_95,k4_xboole_0(B_96,C_94))) = k2_xboole_0(C_94,k3_xboole_0(A_95,B_96)) ),
    inference(superposition,[status(thm),theory(equality)],[c_128,c_12])).

tff(c_2,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(A_1,B_2)) = k4_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_246,plain,(
    ! [A_95,B_96] : k4_xboole_0(A_95,k4_xboole_0(B_96,A_95)) = k2_xboole_0(A_95,k3_xboole_0(A_95,B_96)) ),
    inference(superposition,[status(thm),theory(equality)],[c_235,c_2])).

tff(c_265,plain,(
    ! [A_95,B_96] : k4_xboole_0(A_95,k4_xboole_0(B_96,A_95)) = A_95 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_246])).

tff(c_59,plain,(
    ! [A_58,B_59] : k5_xboole_0(A_58,k4_xboole_0(B_59,A_58)) = k2_xboole_0(A_58,B_59) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_10,plain,(
    ! [A_11,B_12] : r1_tarski(k4_xboole_0(A_11,B_12),k5_xboole_0(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_65,plain,(
    ! [A_58,B_59] : r1_tarski(k4_xboole_0(A_58,k4_xboole_0(B_59,A_58)),k2_xboole_0(A_58,B_59)) ),
    inference(superposition,[status(thm),theory(equality)],[c_59,c_10])).

tff(c_278,plain,(
    ! [A_58,B_59] : r1_tarski(A_58,k2_xboole_0(A_58,B_59)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_265,c_65])).

tff(c_1949,plain,(
    ! [B_194,E_193,D_195,A_197,F_198,G_196,H_192] : r1_tarski(k2_tarski(A_197,B_194),k5_enumset1(A_197,B_194,D_195,E_193,F_198,G_196,H_192)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1930,c_278])).

tff(c_1952,plain,(
    ! [D_41,B_39,A_38,F_43,E_42,C_40] : r1_tarski(k2_tarski(A_38,A_38),k4_enumset1(A_38,B_39,C_40,D_41,E_42,F_43)) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_1949])).

tff(c_1958,plain,(
    ! [B_200,C_203,E_201,D_204,F_202,A_199] : r1_tarski(k1_tarski(A_199),k4_enumset1(A_199,B_200,C_203,D_204,E_201,F_202)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_1952])).

tff(c_1962,plain,(
    ! [E_206,B_209,D_208,A_205,C_207] : r1_tarski(k1_tarski(A_205),k3_enumset1(A_205,B_209,C_207,D_208,E_206)) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_1958])).

tff(c_1966,plain,(
    ! [A_210,B_211,C_212,D_213] : r1_tarski(k1_tarski(A_210),k2_enumset1(A_210,B_211,C_212,D_213)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_1962])).

tff(c_1970,plain,(
    ! [A_214,B_215,C_216] : r1_tarski(k1_tarski(A_214),k1_enumset1(A_214,B_215,C_216)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_1966])).

tff(c_1973,plain,(
    ! [A_24,B_25] : r1_tarski(k1_tarski(A_24),k2_tarski(A_24,B_25)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_1970])).

tff(c_30,plain,(
    ~ r1_tarski(k1_tarski('#skF_1'),k2_tarski('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1976,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1973,c_30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 11:03:19 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.54/1.53  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.54/1.53  
% 3.54/1.53  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.54/1.54  %$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1
% 3.54/1.54  
% 3.54/1.54  %Foreground sorts:
% 3.54/1.54  
% 3.54/1.54  
% 3.54/1.54  %Background operators:
% 3.54/1.54  
% 3.54/1.54  
% 3.54/1.54  %Foreground operators:
% 3.54/1.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.54/1.54  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.54/1.54  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.54/1.54  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.54/1.54  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.54/1.54  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.54/1.54  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.54/1.54  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.54/1.54  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.54/1.54  tff('#skF_2', type, '#skF_2': $i).
% 3.54/1.54  tff('#skF_1', type, '#skF_1': $i).
% 3.54/1.54  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.54/1.54  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.54/1.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.54/1.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.54/1.54  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.54/1.54  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.54/1.54  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.54/1.54  
% 3.54/1.55  tff(f_43, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 3.54/1.55  tff(f_45, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 3.54/1.55  tff(f_47, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 3.54/1.55  tff(f_49, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 3.54/1.55  tff(f_41, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.54/1.55  tff(f_51, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 3.54/1.55  tff(f_53, axiom, (![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 3.54/1.55  tff(f_39, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k1_enumset1(A, B, C), k3_enumset1(D, E, F, G, H)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_enumset1)).
% 3.54/1.55  tff(f_31, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_xboole_1)).
% 3.54/1.55  tff(f_33, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 3.54/1.55  tff(f_37, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 3.54/1.55  tff(f_27, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.54/1.55  tff(f_35, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), k5_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t96_xboole_1)).
% 3.54/1.55  tff(f_56, negated_conjecture, ~(![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 3.54/1.55  tff(c_18, plain, (![A_24, B_25]: (k1_enumset1(A_24, A_24, B_25)=k2_tarski(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.54/1.55  tff(c_20, plain, (![A_26, B_27, C_28]: (k2_enumset1(A_26, A_26, B_27, C_28)=k1_enumset1(A_26, B_27, C_28))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.54/1.55  tff(c_22, plain, (![A_29, B_30, C_31, D_32]: (k3_enumset1(A_29, A_29, B_30, C_31, D_32)=k2_enumset1(A_29, B_30, C_31, D_32))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.54/1.55  tff(c_24, plain, (![D_36, E_37, A_33, B_34, C_35]: (k4_enumset1(A_33, A_33, B_34, C_35, D_36, E_37)=k3_enumset1(A_33, B_34, C_35, D_36, E_37))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.54/1.55  tff(c_16, plain, (![A_23]: (k2_tarski(A_23, A_23)=k1_tarski(A_23))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.54/1.55  tff(c_26, plain, (![D_41, B_39, A_38, F_43, E_42, C_40]: (k5_enumset1(A_38, A_38, B_39, C_40, D_41, E_42, F_43)=k4_enumset1(A_38, B_39, C_40, D_41, E_42, F_43))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.54/1.55  tff(c_28, plain, (![C_46, E_48, F_49, G_50, A_44, B_45, D_47]: (k6_enumset1(A_44, A_44, B_45, C_46, D_47, E_48, F_49, G_50)=k5_enumset1(A_44, B_45, C_46, D_47, E_48, F_49, G_50))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.54/1.55  tff(c_471, plain, (![D_122, A_127, G_123, E_126, H_121, B_124, C_120, F_125]: (k2_xboole_0(k1_enumset1(A_127, B_124, C_120), k3_enumset1(D_122, E_126, F_125, G_123, H_121))=k6_enumset1(A_127, B_124, C_120, D_122, E_126, F_125, G_123, H_121))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.54/1.55  tff(c_486, plain, (![A_24, D_122, G_123, B_25, E_126, H_121, F_125]: (k6_enumset1(A_24, A_24, B_25, D_122, E_126, F_125, G_123, H_121)=k2_xboole_0(k2_tarski(A_24, B_25), k3_enumset1(D_122, E_126, F_125, G_123, H_121)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_471])).
% 3.54/1.55  tff(c_1930, plain, (![E_191, F_187, D_190, B_186, A_189, G_185, H_188]: (k2_xboole_0(k2_tarski(A_189, B_186), k3_enumset1(D_190, E_191, F_187, G_185, H_188))=k5_enumset1(A_189, B_186, D_190, E_191, F_187, G_185, H_188))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_486])).
% 3.54/1.55  tff(c_6, plain, (![A_6, B_7]: (k2_xboole_0(A_6, k3_xboole_0(A_6, B_7))=A_6)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.54/1.55  tff(c_128, plain, (![A_74, B_75, C_76]: (k4_xboole_0(k3_xboole_0(A_74, B_75), C_76)=k3_xboole_0(A_74, k4_xboole_0(B_75, C_76)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.54/1.55  tff(c_12, plain, (![A_13, B_14]: (k5_xboole_0(A_13, k4_xboole_0(B_14, A_13))=k2_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.54/1.55  tff(c_235, plain, (![C_94, A_95, B_96]: (k5_xboole_0(C_94, k3_xboole_0(A_95, k4_xboole_0(B_96, C_94)))=k2_xboole_0(C_94, k3_xboole_0(A_95, B_96)))), inference(superposition, [status(thm), theory('equality')], [c_128, c_12])).
% 3.54/1.55  tff(c_2, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(A_1, B_2))=k4_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.54/1.55  tff(c_246, plain, (![A_95, B_96]: (k4_xboole_0(A_95, k4_xboole_0(B_96, A_95))=k2_xboole_0(A_95, k3_xboole_0(A_95, B_96)))), inference(superposition, [status(thm), theory('equality')], [c_235, c_2])).
% 3.54/1.55  tff(c_265, plain, (![A_95, B_96]: (k4_xboole_0(A_95, k4_xboole_0(B_96, A_95))=A_95)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_246])).
% 3.54/1.55  tff(c_59, plain, (![A_58, B_59]: (k5_xboole_0(A_58, k4_xboole_0(B_59, A_58))=k2_xboole_0(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.54/1.55  tff(c_10, plain, (![A_11, B_12]: (r1_tarski(k4_xboole_0(A_11, B_12), k5_xboole_0(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.54/1.55  tff(c_65, plain, (![A_58, B_59]: (r1_tarski(k4_xboole_0(A_58, k4_xboole_0(B_59, A_58)), k2_xboole_0(A_58, B_59)))), inference(superposition, [status(thm), theory('equality')], [c_59, c_10])).
% 3.54/1.55  tff(c_278, plain, (![A_58, B_59]: (r1_tarski(A_58, k2_xboole_0(A_58, B_59)))), inference(demodulation, [status(thm), theory('equality')], [c_265, c_65])).
% 3.54/1.55  tff(c_1949, plain, (![B_194, E_193, D_195, A_197, F_198, G_196, H_192]: (r1_tarski(k2_tarski(A_197, B_194), k5_enumset1(A_197, B_194, D_195, E_193, F_198, G_196, H_192)))), inference(superposition, [status(thm), theory('equality')], [c_1930, c_278])).
% 3.54/1.55  tff(c_1952, plain, (![D_41, B_39, A_38, F_43, E_42, C_40]: (r1_tarski(k2_tarski(A_38, A_38), k4_enumset1(A_38, B_39, C_40, D_41, E_42, F_43)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_1949])).
% 3.54/1.55  tff(c_1958, plain, (![B_200, C_203, E_201, D_204, F_202, A_199]: (r1_tarski(k1_tarski(A_199), k4_enumset1(A_199, B_200, C_203, D_204, E_201, F_202)))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_1952])).
% 3.54/1.55  tff(c_1962, plain, (![E_206, B_209, D_208, A_205, C_207]: (r1_tarski(k1_tarski(A_205), k3_enumset1(A_205, B_209, C_207, D_208, E_206)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_1958])).
% 3.54/1.55  tff(c_1966, plain, (![A_210, B_211, C_212, D_213]: (r1_tarski(k1_tarski(A_210), k2_enumset1(A_210, B_211, C_212, D_213)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_1962])).
% 3.54/1.55  tff(c_1970, plain, (![A_214, B_215, C_216]: (r1_tarski(k1_tarski(A_214), k1_enumset1(A_214, B_215, C_216)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_1966])).
% 3.54/1.55  tff(c_1973, plain, (![A_24, B_25]: (r1_tarski(k1_tarski(A_24), k2_tarski(A_24, B_25)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_1970])).
% 3.54/1.55  tff(c_30, plain, (~r1_tarski(k1_tarski('#skF_1'), k2_tarski('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.54/1.55  tff(c_1976, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1973, c_30])).
% 3.54/1.55  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.54/1.55  
% 3.54/1.55  Inference rules
% 3.54/1.55  ----------------------
% 3.54/1.55  #Ref     : 0
% 3.54/1.55  #Sup     : 504
% 3.54/1.55  #Fact    : 0
% 3.54/1.55  #Define  : 0
% 3.54/1.55  #Split   : 0
% 3.54/1.55  #Chain   : 0
% 3.54/1.55  #Close   : 0
% 3.54/1.55  
% 3.54/1.55  Ordering : KBO
% 3.54/1.55  
% 3.54/1.55  Simplification rules
% 3.54/1.55  ----------------------
% 3.54/1.55  #Subsume      : 0
% 3.54/1.55  #Demod        : 335
% 3.54/1.55  #Tautology    : 207
% 3.54/1.55  #SimpNegUnit  : 0
% 3.54/1.55  #BackRed      : 6
% 3.54/1.55  
% 3.54/1.55  #Partial instantiations: 0
% 3.54/1.55  #Strategies tried      : 1
% 3.54/1.55  
% 3.54/1.55  Timing (in seconds)
% 3.54/1.55  ----------------------
% 3.54/1.55  Preprocessing        : 0.29
% 3.54/1.55  Parsing              : 0.16
% 3.54/1.55  CNF conversion       : 0.02
% 3.54/1.55  Main loop            : 0.52
% 3.54/1.55  Inferencing          : 0.19
% 3.54/1.55  Reduction            : 0.19
% 3.54/1.55  Demodulation         : 0.15
% 3.54/1.55  BG Simplification    : 0.03
% 3.54/1.55  Subsumption          : 0.07
% 3.54/1.55  Abstraction          : 0.04
% 3.54/1.55  MUC search           : 0.00
% 3.54/1.55  Cooper               : 0.00
% 3.54/1.55  Total                : 0.84
% 3.54/1.55  Index Insertion      : 0.00
% 3.54/1.55  Index Deletion       : 0.00
% 3.54/1.55  Index Matching       : 0.00
% 3.54/1.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
