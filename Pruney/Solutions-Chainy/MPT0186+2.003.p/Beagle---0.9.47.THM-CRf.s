%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:47 EST 2020

% Result     : Theorem 6.34s
% Output     : CNFRefutation 6.34s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 105 expanded)
%              Number of leaves         :   27 (  46 expanded)
%              Depth                    :   12
%              Number of atoms          :   41 (  89 expanded)
%              Number of equality atoms :   40 (  88 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_27,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_37,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_35,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k2_enumset1(A,B,C,D),k1_tarski(E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_enumset1)).

tff(f_33,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C,D,E,F,G] : k6_enumset1(A,A,B,C,D,E,F,G) = k5_enumset1(A,B,C,D,E,F,G) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k1_enumset1(F,G,H)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_enumset1)).

tff(f_48,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,C,B,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_enumset1)).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_tarski(B_2,A_1) = k2_tarski(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_12,plain,(
    ! [A_19,B_20,C_21] : k2_enumset1(A_19,A_19,B_20,C_21) = k1_enumset1(A_19,B_20,C_21) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_10,plain,(
    ! [A_17,B_18] : k1_enumset1(A_17,A_17,B_18) = k2_tarski(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_14,plain,(
    ! [A_22,B_23,C_24,D_25] : k3_enumset1(A_22,A_22,B_23,C_24,D_25) = k2_enumset1(A_22,B_23,C_24,D_25) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_101,plain,(
    ! [E_61,D_62,A_63,C_64,B_65] : k2_xboole_0(k2_enumset1(A_63,B_65,C_64,D_62),k1_tarski(E_61)) = k3_enumset1(A_63,B_65,C_64,D_62,E_61) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_110,plain,(
    ! [A_19,B_20,C_21,E_61] : k3_enumset1(A_19,A_19,B_20,C_21,E_61) = k2_xboole_0(k1_enumset1(A_19,B_20,C_21),k1_tarski(E_61)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_101])).

tff(c_114,plain,(
    ! [A_66,B_67,C_68,E_69] : k2_xboole_0(k1_enumset1(A_66,B_67,C_68),k1_tarski(E_69)) = k2_enumset1(A_66,B_67,C_68,E_69) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_110])).

tff(c_123,plain,(
    ! [A_17,B_18,E_69] : k2_xboole_0(k2_tarski(A_17,B_18),k1_tarski(E_69)) = k2_enumset1(A_17,A_17,B_18,E_69) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_114])).

tff(c_136,plain,(
    ! [A_76,B_77,E_78] : k2_xboole_0(k2_tarski(A_76,B_77),k1_tarski(E_78)) = k1_enumset1(A_76,B_77,E_78) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_123])).

tff(c_164,plain,(
    ! [A_81,B_82,E_83] : k2_xboole_0(k2_tarski(A_81,B_82),k1_tarski(E_83)) = k1_enumset1(B_82,A_81,E_83) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_136])).

tff(c_126,plain,(
    ! [A_17,B_18,E_69] : k2_xboole_0(k2_tarski(A_17,B_18),k1_tarski(E_69)) = k1_enumset1(A_17,B_18,E_69) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_123])).

tff(c_170,plain,(
    ! [B_82,A_81,E_83] : k1_enumset1(B_82,A_81,E_83) = k1_enumset1(A_81,B_82,E_83) ),
    inference(superposition,[status(thm),theory(equality)],[c_164,c_126])).

tff(c_8,plain,(
    ! [A_16] : k2_tarski(A_16,A_16) = k1_tarski(A_16) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_16,plain,(
    ! [B_27,D_29,A_26,E_30,C_28] : k4_enumset1(A_26,A_26,B_27,C_28,D_29,E_30) = k3_enumset1(A_26,B_27,C_28,D_29,E_30) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_18,plain,(
    ! [A_31,C_33,B_32,F_36,E_35,D_34] : k5_enumset1(A_31,A_31,B_32,C_33,D_34,E_35,F_36) = k4_enumset1(A_31,B_32,C_33,D_34,E_35,F_36) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_20,plain,(
    ! [C_39,B_38,A_37,D_40,F_42,G_43,E_41] : k6_enumset1(A_37,A_37,B_38,C_39,D_40,E_41,F_42,G_43) = k5_enumset1(A_37,B_38,C_39,D_40,E_41,F_42,G_43) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_306,plain,(
    ! [G_107,D_109,E_104,F_102,H_108,C_106,B_105,A_103] : k2_xboole_0(k3_enumset1(A_103,B_105,C_106,D_109,E_104),k1_enumset1(F_102,G_107,H_108)) = k6_enumset1(A_103,B_105,C_106,D_109,E_104,F_102,G_107,H_108) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_321,plain,(
    ! [G_107,F_102,H_108,A_22,B_23,D_25,C_24] : k6_enumset1(A_22,A_22,B_23,C_24,D_25,F_102,G_107,H_108) = k2_xboole_0(k2_enumset1(A_22,B_23,C_24,D_25),k1_enumset1(F_102,G_107,H_108)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_306])).

tff(c_395,plain,(
    ! [B_126,G_123,H_125,C_122,A_120,F_121,D_124] : k2_xboole_0(k2_enumset1(A_120,B_126,C_122,D_124),k1_enumset1(F_121,G_123,H_125)) = k5_enumset1(A_120,B_126,C_122,D_124,F_121,G_123,H_125) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_321])).

tff(c_416,plain,(
    ! [A_19,G_123,H_125,F_121,C_21,B_20] : k5_enumset1(A_19,A_19,B_20,C_21,F_121,G_123,H_125) = k2_xboole_0(k1_enumset1(A_19,B_20,C_21),k1_enumset1(F_121,G_123,H_125)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_395])).

tff(c_424,plain,(
    ! [B_129,A_130,H_131,F_132,C_127,G_128] : k2_xboole_0(k1_enumset1(A_130,B_129,C_127),k1_enumset1(F_132,G_128,H_131)) = k4_enumset1(A_130,B_129,C_127,F_132,G_128,H_131) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_416])).

tff(c_445,plain,(
    ! [H_131,B_18,A_17,F_132,G_128] : k4_enumset1(A_17,A_17,B_18,F_132,G_128,H_131) = k2_xboole_0(k2_tarski(A_17,B_18),k1_enumset1(F_132,G_128,H_131)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_424])).

tff(c_452,plain,(
    ! [A_134,G_137,H_133,B_135,F_136] : k2_xboole_0(k2_tarski(A_134,B_135),k1_enumset1(F_136,G_137,H_133)) = k3_enumset1(A_134,B_135,F_136,G_137,H_133) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_445])).

tff(c_476,plain,(
    ! [A_16,F_136,G_137,H_133] : k3_enumset1(A_16,A_16,F_136,G_137,H_133) = k2_xboole_0(k1_tarski(A_16),k1_enumset1(F_136,G_137,H_133)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_452])).

tff(c_6152,plain,(
    ! [A_301,F_302,G_303,H_304] : k2_xboole_0(k1_tarski(A_301),k1_enumset1(F_302,G_303,H_304)) = k2_enumset1(A_301,F_302,G_303,H_304) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_476])).

tff(c_6510,plain,(
    ! [A_313,A_314,B_315,E_316] : k2_xboole_0(k1_tarski(A_313),k1_enumset1(A_314,B_315,E_316)) = k2_enumset1(A_313,B_315,A_314,E_316) ),
    inference(superposition,[status(thm),theory(equality)],[c_170,c_6152])).

tff(c_479,plain,(
    ! [A_16,F_136,G_137,H_133] : k2_xboole_0(k1_tarski(A_16),k1_enumset1(F_136,G_137,H_133)) = k2_enumset1(A_16,F_136,G_137,H_133) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_476])).

tff(c_6516,plain,(
    ! [A_313,B_315,A_314,E_316] : k2_enumset1(A_313,B_315,A_314,E_316) = k2_enumset1(A_313,A_314,B_315,E_316) ),
    inference(superposition,[status(thm),theory(equality)],[c_6510,c_479])).

tff(c_22,plain,(
    k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_enumset1('#skF_1','#skF_3','#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_6560,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6516,c_22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:58:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.34/2.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.34/2.27  
% 6.34/2.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.34/2.27  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 6.34/2.27  
% 6.34/2.27  %Foreground sorts:
% 6.34/2.27  
% 6.34/2.27  
% 6.34/2.27  %Background operators:
% 6.34/2.27  
% 6.34/2.27  
% 6.34/2.27  %Foreground operators:
% 6.34/2.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.34/2.27  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.34/2.27  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.34/2.27  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.34/2.27  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.34/2.27  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.34/2.27  tff('#skF_2', type, '#skF_2': $i).
% 6.34/2.27  tff('#skF_3', type, '#skF_3': $i).
% 6.34/2.27  tff('#skF_1', type, '#skF_1': $i).
% 6.34/2.27  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.34/2.27  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 6.34/2.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.34/2.27  tff('#skF_4', type, '#skF_4': $i).
% 6.34/2.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.34/2.27  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.34/2.27  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 6.34/2.27  
% 6.34/2.29  tff(f_27, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 6.34/2.29  tff(f_37, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 6.34/2.29  tff(f_35, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 6.34/2.29  tff(f_39, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 6.34/2.29  tff(f_29, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k2_enumset1(A, B, C, D), k1_tarski(E)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_enumset1)).
% 6.34/2.29  tff(f_33, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 6.34/2.29  tff(f_41, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 6.34/2.29  tff(f_43, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 6.34/2.29  tff(f_45, axiom, (![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 6.34/2.29  tff(f_31, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k1_enumset1(F, G, H)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_enumset1)).
% 6.34/2.29  tff(f_48, negated_conjecture, ~(![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, C, B, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t104_enumset1)).
% 6.34/2.29  tff(c_2, plain, (![B_2, A_1]: (k2_tarski(B_2, A_1)=k2_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.34/2.29  tff(c_12, plain, (![A_19, B_20, C_21]: (k2_enumset1(A_19, A_19, B_20, C_21)=k1_enumset1(A_19, B_20, C_21))), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.34/2.29  tff(c_10, plain, (![A_17, B_18]: (k1_enumset1(A_17, A_17, B_18)=k2_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.34/2.29  tff(c_14, plain, (![A_22, B_23, C_24, D_25]: (k3_enumset1(A_22, A_22, B_23, C_24, D_25)=k2_enumset1(A_22, B_23, C_24, D_25))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.34/2.29  tff(c_101, plain, (![E_61, D_62, A_63, C_64, B_65]: (k2_xboole_0(k2_enumset1(A_63, B_65, C_64, D_62), k1_tarski(E_61))=k3_enumset1(A_63, B_65, C_64, D_62, E_61))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.34/2.29  tff(c_110, plain, (![A_19, B_20, C_21, E_61]: (k3_enumset1(A_19, A_19, B_20, C_21, E_61)=k2_xboole_0(k1_enumset1(A_19, B_20, C_21), k1_tarski(E_61)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_101])).
% 6.34/2.29  tff(c_114, plain, (![A_66, B_67, C_68, E_69]: (k2_xboole_0(k1_enumset1(A_66, B_67, C_68), k1_tarski(E_69))=k2_enumset1(A_66, B_67, C_68, E_69))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_110])).
% 6.34/2.29  tff(c_123, plain, (![A_17, B_18, E_69]: (k2_xboole_0(k2_tarski(A_17, B_18), k1_tarski(E_69))=k2_enumset1(A_17, A_17, B_18, E_69))), inference(superposition, [status(thm), theory('equality')], [c_10, c_114])).
% 6.34/2.29  tff(c_136, plain, (![A_76, B_77, E_78]: (k2_xboole_0(k2_tarski(A_76, B_77), k1_tarski(E_78))=k1_enumset1(A_76, B_77, E_78))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_123])).
% 6.34/2.29  tff(c_164, plain, (![A_81, B_82, E_83]: (k2_xboole_0(k2_tarski(A_81, B_82), k1_tarski(E_83))=k1_enumset1(B_82, A_81, E_83))), inference(superposition, [status(thm), theory('equality')], [c_2, c_136])).
% 6.34/2.29  tff(c_126, plain, (![A_17, B_18, E_69]: (k2_xboole_0(k2_tarski(A_17, B_18), k1_tarski(E_69))=k1_enumset1(A_17, B_18, E_69))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_123])).
% 6.34/2.29  tff(c_170, plain, (![B_82, A_81, E_83]: (k1_enumset1(B_82, A_81, E_83)=k1_enumset1(A_81, B_82, E_83))), inference(superposition, [status(thm), theory('equality')], [c_164, c_126])).
% 6.34/2.29  tff(c_8, plain, (![A_16]: (k2_tarski(A_16, A_16)=k1_tarski(A_16))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.34/2.29  tff(c_16, plain, (![B_27, D_29, A_26, E_30, C_28]: (k4_enumset1(A_26, A_26, B_27, C_28, D_29, E_30)=k3_enumset1(A_26, B_27, C_28, D_29, E_30))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.34/2.29  tff(c_18, plain, (![A_31, C_33, B_32, F_36, E_35, D_34]: (k5_enumset1(A_31, A_31, B_32, C_33, D_34, E_35, F_36)=k4_enumset1(A_31, B_32, C_33, D_34, E_35, F_36))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.34/2.29  tff(c_20, plain, (![C_39, B_38, A_37, D_40, F_42, G_43, E_41]: (k6_enumset1(A_37, A_37, B_38, C_39, D_40, E_41, F_42, G_43)=k5_enumset1(A_37, B_38, C_39, D_40, E_41, F_42, G_43))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.34/2.29  tff(c_306, plain, (![G_107, D_109, E_104, F_102, H_108, C_106, B_105, A_103]: (k2_xboole_0(k3_enumset1(A_103, B_105, C_106, D_109, E_104), k1_enumset1(F_102, G_107, H_108))=k6_enumset1(A_103, B_105, C_106, D_109, E_104, F_102, G_107, H_108))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.34/2.29  tff(c_321, plain, (![G_107, F_102, H_108, A_22, B_23, D_25, C_24]: (k6_enumset1(A_22, A_22, B_23, C_24, D_25, F_102, G_107, H_108)=k2_xboole_0(k2_enumset1(A_22, B_23, C_24, D_25), k1_enumset1(F_102, G_107, H_108)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_306])).
% 6.34/2.29  tff(c_395, plain, (![B_126, G_123, H_125, C_122, A_120, F_121, D_124]: (k2_xboole_0(k2_enumset1(A_120, B_126, C_122, D_124), k1_enumset1(F_121, G_123, H_125))=k5_enumset1(A_120, B_126, C_122, D_124, F_121, G_123, H_125))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_321])).
% 6.34/2.29  tff(c_416, plain, (![A_19, G_123, H_125, F_121, C_21, B_20]: (k5_enumset1(A_19, A_19, B_20, C_21, F_121, G_123, H_125)=k2_xboole_0(k1_enumset1(A_19, B_20, C_21), k1_enumset1(F_121, G_123, H_125)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_395])).
% 6.34/2.29  tff(c_424, plain, (![B_129, A_130, H_131, F_132, C_127, G_128]: (k2_xboole_0(k1_enumset1(A_130, B_129, C_127), k1_enumset1(F_132, G_128, H_131))=k4_enumset1(A_130, B_129, C_127, F_132, G_128, H_131))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_416])).
% 6.34/2.29  tff(c_445, plain, (![H_131, B_18, A_17, F_132, G_128]: (k4_enumset1(A_17, A_17, B_18, F_132, G_128, H_131)=k2_xboole_0(k2_tarski(A_17, B_18), k1_enumset1(F_132, G_128, H_131)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_424])).
% 6.34/2.29  tff(c_452, plain, (![A_134, G_137, H_133, B_135, F_136]: (k2_xboole_0(k2_tarski(A_134, B_135), k1_enumset1(F_136, G_137, H_133))=k3_enumset1(A_134, B_135, F_136, G_137, H_133))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_445])).
% 6.34/2.29  tff(c_476, plain, (![A_16, F_136, G_137, H_133]: (k3_enumset1(A_16, A_16, F_136, G_137, H_133)=k2_xboole_0(k1_tarski(A_16), k1_enumset1(F_136, G_137, H_133)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_452])).
% 6.34/2.29  tff(c_6152, plain, (![A_301, F_302, G_303, H_304]: (k2_xboole_0(k1_tarski(A_301), k1_enumset1(F_302, G_303, H_304))=k2_enumset1(A_301, F_302, G_303, H_304))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_476])).
% 6.34/2.29  tff(c_6510, plain, (![A_313, A_314, B_315, E_316]: (k2_xboole_0(k1_tarski(A_313), k1_enumset1(A_314, B_315, E_316))=k2_enumset1(A_313, B_315, A_314, E_316))), inference(superposition, [status(thm), theory('equality')], [c_170, c_6152])).
% 6.34/2.29  tff(c_479, plain, (![A_16, F_136, G_137, H_133]: (k2_xboole_0(k1_tarski(A_16), k1_enumset1(F_136, G_137, H_133))=k2_enumset1(A_16, F_136, G_137, H_133))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_476])).
% 6.34/2.29  tff(c_6516, plain, (![A_313, B_315, A_314, E_316]: (k2_enumset1(A_313, B_315, A_314, E_316)=k2_enumset1(A_313, A_314, B_315, E_316))), inference(superposition, [status(thm), theory('equality')], [c_6510, c_479])).
% 6.34/2.29  tff(c_22, plain, (k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_enumset1('#skF_1', '#skF_3', '#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_48])).
% 6.34/2.29  tff(c_6560, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6516, c_22])).
% 6.34/2.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.34/2.29  
% 6.34/2.29  Inference rules
% 6.34/2.29  ----------------------
% 6.34/2.29  #Ref     : 0
% 6.34/2.29  #Sup     : 1591
% 6.34/2.29  #Fact    : 0
% 6.34/2.29  #Define  : 0
% 6.34/2.29  #Split   : 0
% 6.34/2.29  #Chain   : 0
% 6.34/2.29  #Close   : 0
% 6.34/2.29  
% 6.34/2.29  Ordering : KBO
% 6.34/2.29  
% 6.34/2.29  Simplification rules
% 6.34/2.29  ----------------------
% 6.34/2.29  #Subsume      : 247
% 6.34/2.29  #Demod        : 1385
% 6.34/2.29  #Tautology    : 958
% 6.34/2.29  #SimpNegUnit  : 0
% 6.34/2.29  #BackRed      : 1
% 6.34/2.29  
% 6.34/2.29  #Partial instantiations: 0
% 6.34/2.29  #Strategies tried      : 1
% 6.34/2.29  
% 6.34/2.29  Timing (in seconds)
% 6.34/2.29  ----------------------
% 6.34/2.30  Preprocessing        : 0.30
% 6.34/2.30  Parsing              : 0.16
% 6.34/2.30  CNF conversion       : 0.02
% 6.34/2.30  Main loop            : 1.19
% 6.34/2.30  Inferencing          : 0.41
% 6.34/2.30  Reduction            : 0.55
% 6.34/2.30  Demodulation         : 0.48
% 6.34/2.30  BG Simplification    : 0.06
% 6.34/2.30  Subsumption          : 0.13
% 6.34/2.30  Abstraction          : 0.07
% 6.34/2.30  MUC search           : 0.00
% 6.34/2.30  Cooper               : 0.00
% 6.34/2.30  Total                : 1.52
% 6.34/2.30  Index Insertion      : 0.00
% 6.34/2.30  Index Deletion       : 0.00
% 6.34/2.30  Index Matching       : 0.00
% 6.34/2.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
