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
% DateTime   : Thu Dec  3 09:47:18 EST 2020

% Result     : Theorem 7.31s
% Output     : CNFRefutation 7.31s
% Verified   : 
% Statistics : Number of formulae       :   56 (  87 expanded)
%              Number of leaves         :   28 (  42 expanded)
%              Depth                    :   11
%              Number of atoms          :   38 (  69 expanded)
%              Number of equality atoms :   37 (  68 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k7_enumset1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k7_enumset1,type,(
    k7_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_37,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(D,C,B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,D,C,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_47,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_43,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_49,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_51,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_53,axiom,(
    ! [A,B,C,D,E,F,G] : k6_enumset1(A,A,B,C,D,E,F,G) = k5_enumset1(A,B,C,D,E,F,G) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k4_enumset1(A,B,C,D,E,F),k2_tarski(G,H)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_enumset1)).

tff(f_56,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(B,A),k2_tarski(C,A)) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_enumset1)).

tff(c_12,plain,(
    ! [D_18,C_17,B_16,A_15] : k2_enumset1(D_18,C_17,B_16,A_15) = k2_enumset1(A_15,B_16,C_17,D_18) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_252,plain,(
    ! [B_85,D_86,C_87,A_88] : k2_enumset1(B_85,D_86,C_87,A_88) = k2_enumset1(A_88,B_85,C_87,D_86) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_20,plain,(
    ! [A_38,B_39,C_40] : k2_enumset1(A_38,A_38,B_39,C_40) = k1_enumset1(A_38,B_39,C_40) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_333,plain,(
    ! [B_89,D_90,C_91] : k2_enumset1(B_89,D_90,C_91,B_89) = k1_enumset1(B_89,C_91,D_90) ),
    inference(superposition,[status(thm),theory(equality)],[c_252,c_20])).

tff(c_616,plain,(
    ! [A_101,B_102,C_103] : k2_enumset1(A_101,B_102,C_103,A_101) = k1_enumset1(A_101,B_102,C_103) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_333])).

tff(c_288,plain,(
    ! [B_85,D_86,C_87] : k2_enumset1(B_85,D_86,C_87,B_85) = k1_enumset1(B_85,C_87,D_86) ),
    inference(superposition,[status(thm),theory(equality)],[c_252,c_20])).

tff(c_632,plain,(
    ! [A_101,C_103,B_102] : k1_enumset1(A_101,C_103,B_102) = k1_enumset1(A_101,B_102,C_103) ),
    inference(superposition,[status(thm),theory(equality)],[c_616,c_288])).

tff(c_134,plain,(
    ! [D_76,C_77,B_78,A_79] : k2_enumset1(D_76,C_77,B_78,A_79) = k2_enumset1(A_79,B_78,C_77,D_76) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_150,plain,(
    ! [D_76,C_77,B_78] : k2_enumset1(D_76,C_77,B_78,B_78) = k1_enumset1(B_78,C_77,D_76) ),
    inference(superposition,[status(thm),theory(equality)],[c_134,c_20])).

tff(c_307,plain,(
    ! [B_78,D_76,C_77] : k2_enumset1(B_78,D_76,B_78,C_77) = k1_enumset1(B_78,C_77,D_76) ),
    inference(superposition,[status(thm),theory(equality)],[c_150,c_252])).

tff(c_22,plain,(
    ! [A_41,B_42,C_43,D_44] : k3_enumset1(A_41,A_41,B_42,C_43,D_44) = k2_enumset1(A_41,B_42,C_43,D_44) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_18,plain,(
    ! [A_36,B_37] : k1_enumset1(A_36,A_36,B_37) = k2_tarski(A_36,B_37) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_24,plain,(
    ! [D_48,C_47,A_45,B_46,E_49] : k4_enumset1(A_45,A_45,B_46,C_47,D_48,E_49) = k3_enumset1(A_45,B_46,C_47,D_48,E_49) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_26,plain,(
    ! [A_50,B_51,E_54,C_52,D_53,F_55] : k5_enumset1(A_50,A_50,B_51,C_52,D_53,E_54,F_55) = k4_enumset1(A_50,B_51,C_52,D_53,E_54,F_55) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_28,plain,(
    ! [D_59,A_56,B_57,G_62,F_61,C_58,E_60] : k6_enumset1(A_56,A_56,B_57,C_58,D_59,E_60,F_61,G_62) = k5_enumset1(A_56,B_57,C_58,D_59,E_60,F_61,G_62) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1295,plain,(
    ! [E_143,F_142,A_144,D_147,H_148,C_145,B_146,G_141] : k2_xboole_0(k4_enumset1(A_144,B_146,C_145,D_147,E_143,F_142),k2_tarski(G_141,H_148)) = k6_enumset1(A_144,B_146,C_145,D_147,E_143,F_142,G_141,H_148) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1304,plain,(
    ! [D_48,C_47,A_45,B_46,H_148,E_49,G_141] : k6_enumset1(A_45,A_45,B_46,C_47,D_48,E_49,G_141,H_148) = k2_xboole_0(k3_enumset1(A_45,B_46,C_47,D_48,E_49),k2_tarski(G_141,H_148)) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_1295])).

tff(c_4846,plain,(
    ! [E_205,B_200,C_203,G_204,H_199,D_202,A_201] : k2_xboole_0(k3_enumset1(A_201,B_200,C_203,D_202,E_205),k2_tarski(G_204,H_199)) = k5_enumset1(A_201,B_200,C_203,D_202,E_205,G_204,H_199) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_1304])).

tff(c_4855,plain,(
    ! [D_44,G_204,C_43,A_41,B_42,H_199] : k5_enumset1(A_41,A_41,B_42,C_43,D_44,G_204,H_199) = k2_xboole_0(k2_enumset1(A_41,B_42,C_43,D_44),k2_tarski(G_204,H_199)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_4846])).

tff(c_7661,plain,(
    ! [A_234,H_238,D_237,C_236,G_235,B_239] : k2_xboole_0(k2_enumset1(A_234,B_239,C_236,D_237),k2_tarski(G_235,H_238)) = k4_enumset1(A_234,B_239,C_236,D_237,G_235,H_238) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_4855])).

tff(c_7799,plain,(
    ! [B_39,H_238,G_235,A_38,C_40] : k4_enumset1(A_38,A_38,B_39,C_40,G_235,H_238) = k2_xboole_0(k1_enumset1(A_38,B_39,C_40),k2_tarski(G_235,H_238)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_7661])).

tff(c_7954,plain,(
    ! [C_249,A_246,H_248,G_250,B_247] : k2_xboole_0(k1_enumset1(A_246,B_247,C_249),k2_tarski(G_250,H_248)) = k3_enumset1(A_246,B_247,C_249,G_250,H_248) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_7799])).

tff(c_7978,plain,(
    ! [A_36,B_37,G_250,H_248] : k3_enumset1(A_36,A_36,B_37,G_250,H_248) = k2_xboole_0(k2_tarski(A_36,B_37),k2_tarski(G_250,H_248)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_7954])).

tff(c_7981,plain,(
    ! [A_36,B_37,G_250,H_248] : k2_xboole_0(k2_tarski(A_36,B_37),k2_tarski(G_250,H_248)) = k2_enumset1(A_36,B_37,G_250,H_248) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_7978])).

tff(c_30,plain,(
    k2_xboole_0(k2_tarski('#skF_2','#skF_1'),k2_tarski('#skF_3','#skF_1')) != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_707,plain,(
    k2_xboole_0(k2_tarski('#skF_2','#skF_1'),k2_tarski('#skF_3','#skF_1')) != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_632,c_30])).

tff(c_8006,plain,(
    k2_enumset1('#skF_2','#skF_1','#skF_3','#skF_1') != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7981,c_707])).

tff(c_8009,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_632,c_307,c_12,c_8006])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n004.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 17:00:23 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.31/2.82  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.31/2.82  
% 7.31/2.82  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.31/2.83  %$ k7_enumset1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > #skF_2 > #skF_3 > #skF_1
% 7.31/2.83  
% 7.31/2.83  %Foreground sorts:
% 7.31/2.83  
% 7.31/2.83  
% 7.31/2.83  %Background operators:
% 7.31/2.83  
% 7.31/2.83  
% 7.31/2.83  %Foreground operators:
% 7.31/2.83  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.31/2.83  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.31/2.83  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 7.31/2.83  tff(k7_enumset1, type, k7_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 7.31/2.83  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 7.31/2.83  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 7.31/2.83  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.31/2.83  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.31/2.83  tff('#skF_2', type, '#skF_2': $i).
% 7.31/2.83  tff('#skF_3', type, '#skF_3': $i).
% 7.31/2.83  tff('#skF_1', type, '#skF_1': $i).
% 7.31/2.83  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.31/2.83  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 7.31/2.83  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.31/2.83  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.31/2.83  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.31/2.83  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.31/2.83  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 7.31/2.83  
% 7.31/2.84  tff(f_37, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(D, C, B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_enumset1)).
% 7.31/2.84  tff(f_35, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, D, C, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_enumset1)).
% 7.31/2.84  tff(f_45, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 7.31/2.84  tff(f_47, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 7.31/2.84  tff(f_43, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 7.31/2.84  tff(f_49, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 7.31/2.84  tff(f_51, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 7.31/2.84  tff(f_53, axiom, (![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 7.31/2.84  tff(f_41, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k4_enumset1(A, B, C, D, E, F), k2_tarski(G, H)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_enumset1)).
% 7.31/2.84  tff(f_56, negated_conjecture, ~(![A, B, C]: (k2_xboole_0(k2_tarski(B, A), k2_tarski(C, A)) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t137_enumset1)).
% 7.31/2.84  tff(c_12, plain, (![D_18, C_17, B_16, A_15]: (k2_enumset1(D_18, C_17, B_16, A_15)=k2_enumset1(A_15, B_16, C_17, D_18))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.31/2.84  tff(c_252, plain, (![B_85, D_86, C_87, A_88]: (k2_enumset1(B_85, D_86, C_87, A_88)=k2_enumset1(A_88, B_85, C_87, D_86))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.31/2.84  tff(c_20, plain, (![A_38, B_39, C_40]: (k2_enumset1(A_38, A_38, B_39, C_40)=k1_enumset1(A_38, B_39, C_40))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.31/2.84  tff(c_333, plain, (![B_89, D_90, C_91]: (k2_enumset1(B_89, D_90, C_91, B_89)=k1_enumset1(B_89, C_91, D_90))), inference(superposition, [status(thm), theory('equality')], [c_252, c_20])).
% 7.31/2.84  tff(c_616, plain, (![A_101, B_102, C_103]: (k2_enumset1(A_101, B_102, C_103, A_101)=k1_enumset1(A_101, B_102, C_103))), inference(superposition, [status(thm), theory('equality')], [c_12, c_333])).
% 7.31/2.84  tff(c_288, plain, (![B_85, D_86, C_87]: (k2_enumset1(B_85, D_86, C_87, B_85)=k1_enumset1(B_85, C_87, D_86))), inference(superposition, [status(thm), theory('equality')], [c_252, c_20])).
% 7.31/2.84  tff(c_632, plain, (![A_101, C_103, B_102]: (k1_enumset1(A_101, C_103, B_102)=k1_enumset1(A_101, B_102, C_103))), inference(superposition, [status(thm), theory('equality')], [c_616, c_288])).
% 7.31/2.84  tff(c_134, plain, (![D_76, C_77, B_78, A_79]: (k2_enumset1(D_76, C_77, B_78, A_79)=k2_enumset1(A_79, B_78, C_77, D_76))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.31/2.84  tff(c_150, plain, (![D_76, C_77, B_78]: (k2_enumset1(D_76, C_77, B_78, B_78)=k1_enumset1(B_78, C_77, D_76))), inference(superposition, [status(thm), theory('equality')], [c_134, c_20])).
% 7.31/2.84  tff(c_307, plain, (![B_78, D_76, C_77]: (k2_enumset1(B_78, D_76, B_78, C_77)=k1_enumset1(B_78, C_77, D_76))), inference(superposition, [status(thm), theory('equality')], [c_150, c_252])).
% 7.31/2.84  tff(c_22, plain, (![A_41, B_42, C_43, D_44]: (k3_enumset1(A_41, A_41, B_42, C_43, D_44)=k2_enumset1(A_41, B_42, C_43, D_44))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.31/2.84  tff(c_18, plain, (![A_36, B_37]: (k1_enumset1(A_36, A_36, B_37)=k2_tarski(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.31/2.84  tff(c_24, plain, (![D_48, C_47, A_45, B_46, E_49]: (k4_enumset1(A_45, A_45, B_46, C_47, D_48, E_49)=k3_enumset1(A_45, B_46, C_47, D_48, E_49))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.31/2.84  tff(c_26, plain, (![A_50, B_51, E_54, C_52, D_53, F_55]: (k5_enumset1(A_50, A_50, B_51, C_52, D_53, E_54, F_55)=k4_enumset1(A_50, B_51, C_52, D_53, E_54, F_55))), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.31/2.84  tff(c_28, plain, (![D_59, A_56, B_57, G_62, F_61, C_58, E_60]: (k6_enumset1(A_56, A_56, B_57, C_58, D_59, E_60, F_61, G_62)=k5_enumset1(A_56, B_57, C_58, D_59, E_60, F_61, G_62))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.31/2.84  tff(c_1295, plain, (![E_143, F_142, A_144, D_147, H_148, C_145, B_146, G_141]: (k2_xboole_0(k4_enumset1(A_144, B_146, C_145, D_147, E_143, F_142), k2_tarski(G_141, H_148))=k6_enumset1(A_144, B_146, C_145, D_147, E_143, F_142, G_141, H_148))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.31/2.84  tff(c_1304, plain, (![D_48, C_47, A_45, B_46, H_148, E_49, G_141]: (k6_enumset1(A_45, A_45, B_46, C_47, D_48, E_49, G_141, H_148)=k2_xboole_0(k3_enumset1(A_45, B_46, C_47, D_48, E_49), k2_tarski(G_141, H_148)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_1295])).
% 7.31/2.84  tff(c_4846, plain, (![E_205, B_200, C_203, G_204, H_199, D_202, A_201]: (k2_xboole_0(k3_enumset1(A_201, B_200, C_203, D_202, E_205), k2_tarski(G_204, H_199))=k5_enumset1(A_201, B_200, C_203, D_202, E_205, G_204, H_199))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_1304])).
% 7.31/2.84  tff(c_4855, plain, (![D_44, G_204, C_43, A_41, B_42, H_199]: (k5_enumset1(A_41, A_41, B_42, C_43, D_44, G_204, H_199)=k2_xboole_0(k2_enumset1(A_41, B_42, C_43, D_44), k2_tarski(G_204, H_199)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_4846])).
% 7.31/2.84  tff(c_7661, plain, (![A_234, H_238, D_237, C_236, G_235, B_239]: (k2_xboole_0(k2_enumset1(A_234, B_239, C_236, D_237), k2_tarski(G_235, H_238))=k4_enumset1(A_234, B_239, C_236, D_237, G_235, H_238))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_4855])).
% 7.31/2.84  tff(c_7799, plain, (![B_39, H_238, G_235, A_38, C_40]: (k4_enumset1(A_38, A_38, B_39, C_40, G_235, H_238)=k2_xboole_0(k1_enumset1(A_38, B_39, C_40), k2_tarski(G_235, H_238)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_7661])).
% 7.31/2.84  tff(c_7954, plain, (![C_249, A_246, H_248, G_250, B_247]: (k2_xboole_0(k1_enumset1(A_246, B_247, C_249), k2_tarski(G_250, H_248))=k3_enumset1(A_246, B_247, C_249, G_250, H_248))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_7799])).
% 7.31/2.84  tff(c_7978, plain, (![A_36, B_37, G_250, H_248]: (k3_enumset1(A_36, A_36, B_37, G_250, H_248)=k2_xboole_0(k2_tarski(A_36, B_37), k2_tarski(G_250, H_248)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_7954])).
% 7.31/2.84  tff(c_7981, plain, (![A_36, B_37, G_250, H_248]: (k2_xboole_0(k2_tarski(A_36, B_37), k2_tarski(G_250, H_248))=k2_enumset1(A_36, B_37, G_250, H_248))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_7978])).
% 7.31/2.84  tff(c_30, plain, (k2_xboole_0(k2_tarski('#skF_2', '#skF_1'), k2_tarski('#skF_3', '#skF_1'))!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_56])).
% 7.31/2.84  tff(c_707, plain, (k2_xboole_0(k2_tarski('#skF_2', '#skF_1'), k2_tarski('#skF_3', '#skF_1'))!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_632, c_30])).
% 7.31/2.84  tff(c_8006, plain, (k2_enumset1('#skF_2', '#skF_1', '#skF_3', '#skF_1')!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_7981, c_707])).
% 7.31/2.84  tff(c_8009, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_632, c_307, c_12, c_8006])).
% 7.31/2.84  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.31/2.84  
% 7.31/2.84  Inference rules
% 7.31/2.84  ----------------------
% 7.31/2.84  #Ref     : 0
% 7.31/2.84  #Sup     : 2140
% 7.31/2.84  #Fact    : 0
% 7.31/2.84  #Define  : 0
% 7.31/2.84  #Split   : 0
% 7.31/2.84  #Chain   : 0
% 7.31/2.84  #Close   : 0
% 7.31/2.84  
% 7.31/2.84  Ordering : KBO
% 7.31/2.84  
% 7.31/2.84  Simplification rules
% 7.31/2.84  ----------------------
% 7.31/2.84  #Subsume      : 1009
% 7.31/2.84  #Demod        : 923
% 7.31/2.84  #Tautology    : 1004
% 7.31/2.84  #SimpNegUnit  : 0
% 7.31/2.84  #BackRed      : 2
% 7.31/2.84  
% 7.31/2.84  #Partial instantiations: 0
% 7.31/2.84  #Strategies tried      : 1
% 7.31/2.84  
% 7.31/2.84  Timing (in seconds)
% 7.31/2.84  ----------------------
% 7.31/2.84  Preprocessing        : 0.33
% 7.31/2.84  Parsing              : 0.17
% 7.31/2.84  CNF conversion       : 0.02
% 7.31/2.84  Main loop            : 1.70
% 7.31/2.84  Inferencing          : 0.40
% 7.31/2.84  Reduction            : 1.04
% 7.31/2.84  Demodulation         : 0.97
% 7.31/2.84  BG Simplification    : 0.04
% 7.31/2.84  Subsumption          : 0.17
% 7.31/2.84  Abstraction          : 0.07
% 7.31/2.84  MUC search           : 0.00
% 7.31/2.84  Cooper               : 0.00
% 7.31/2.84  Total                : 2.06
% 7.31/2.84  Index Insertion      : 0.00
% 7.31/2.84  Index Deletion       : 0.00
% 7.31/2.84  Index Matching       : 0.00
% 7.31/2.84  BG Taut test         : 0.00
%------------------------------------------------------------------------------
