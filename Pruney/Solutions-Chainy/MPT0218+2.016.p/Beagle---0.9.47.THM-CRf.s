%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:48 EST 2020

% Result     : Theorem 6.24s
% Output     : CNFRefutation 6.33s
% Verified   : 
% Statistics : Number of formulae       :   66 (  77 expanded)
%              Number of leaves         :   32 (  38 expanded)
%              Depth                    :   15
%              Number of atoms          :   48 (  59 expanded)
%              Number of equality atoms :   32 (  43 expanded)
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

tff(f_41,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

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

tff(f_51,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_53,axiom,(
    ! [A,B,C,D,E,F,G] : k6_enumset1(A,A,B,C,D,E,F,G) = k5_enumset1(A,B,C,D,E,F,G) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k5_enumset1(A,B,C,D,E,F,G),k1_tarski(H)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_enumset1)).

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

tff(c_16,plain,(
    ! [A_23] : k2_tarski(A_23,A_23) = k1_tarski(A_23) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

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

tff(c_26,plain,(
    ! [D_41,B_39,A_38,F_43,E_42,C_40] : k5_enumset1(A_38,A_38,B_39,C_40,D_41,E_42,F_43) = k4_enumset1(A_38,B_39,C_40,D_41,E_42,F_43) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_28,plain,(
    ! [C_46,E_48,F_49,G_50,A_44,B_45,D_47] : k6_enumset1(A_44,A_44,B_45,C_46,D_47,E_48,F_49,G_50) = k5_enumset1(A_44,B_45,C_46,D_47,E_48,F_49,G_50) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_471,plain,(
    ! [D_122,A_127,G_123,E_126,H_121,B_124,C_120,F_125] : k2_xboole_0(k5_enumset1(A_127,B_124,C_120,D_122,E_126,F_125,G_123),k1_tarski(H_121)) = k6_enumset1(A_127,B_124,C_120,D_122,E_126,F_125,G_123,H_121) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_483,plain,(
    ! [D_41,B_39,H_121,A_38,F_43,E_42,C_40] : k6_enumset1(A_38,A_38,B_39,C_40,D_41,E_42,F_43,H_121) = k2_xboole_0(k4_enumset1(A_38,B_39,C_40,D_41,E_42,F_43),k1_tarski(H_121)) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_471])).

tff(c_1768,plain,(
    ! [A_181,B_183,F_185,H_182,E_184,D_187,C_186] : k2_xboole_0(k4_enumset1(A_181,B_183,C_186,D_187,E_184,F_185),k1_tarski(H_182)) = k5_enumset1(A_181,B_183,C_186,D_187,E_184,F_185,H_182) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_483])).

tff(c_1780,plain,(
    ! [D_36,H_182,E_37,A_33,B_34,C_35] : k5_enumset1(A_33,A_33,B_34,C_35,D_36,E_37,H_182) = k2_xboole_0(k3_enumset1(A_33,B_34,C_35,D_36,E_37),k1_tarski(H_182)) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_1768])).

tff(c_6008,plain,(
    ! [E_290,A_289,H_293,C_291,B_294,D_292] : k2_xboole_0(k3_enumset1(A_289,B_294,C_291,D_292,E_290),k1_tarski(H_293)) = k4_enumset1(A_289,B_294,C_291,D_292,E_290,H_293) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1780])).

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

tff(c_6024,plain,(
    ! [B_296,H_299,E_297,D_300,A_298,C_295] : r1_tarski(k3_enumset1(A_298,B_296,C_295,D_300,E_297),k4_enumset1(A_298,B_296,C_295,D_300,E_297,H_299)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6008,c_278])).

tff(c_6027,plain,(
    ! [D_36,E_37,A_33,B_34,C_35] : r1_tarski(k3_enumset1(A_33,A_33,B_34,C_35,D_36),k3_enumset1(A_33,B_34,C_35,D_36,E_37)) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_6024])).

tff(c_6033,plain,(
    ! [E_302,D_304,B_305,C_303,A_301] : r1_tarski(k2_enumset1(A_301,B_305,C_303,D_304),k3_enumset1(A_301,B_305,C_303,D_304,E_302)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_6027])).

tff(c_6036,plain,(
    ! [A_29,B_30,C_31,D_32] : r1_tarski(k2_enumset1(A_29,A_29,B_30,C_31),k2_enumset1(A_29,B_30,C_31,D_32)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_6033])).

tff(c_6042,plain,(
    ! [A_306,B_307,C_308,D_309] : r1_tarski(k1_enumset1(A_306,B_307,C_308),k2_enumset1(A_306,B_307,C_308,D_309)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_6036])).

tff(c_6045,plain,(
    ! [A_26,B_27,C_28] : r1_tarski(k1_enumset1(A_26,A_26,B_27),k1_enumset1(A_26,B_27,C_28)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_6042])).

tff(c_6052,plain,(
    ! [A_310,B_311,C_312] : r1_tarski(k2_tarski(A_310,B_311),k1_enumset1(A_310,B_311,C_312)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_6045])).

tff(c_6055,plain,(
    ! [A_24,B_25] : r1_tarski(k2_tarski(A_24,A_24),k2_tarski(A_24,B_25)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_6052])).

tff(c_6059,plain,(
    ! [A_24,B_25] : r1_tarski(k1_tarski(A_24),k2_tarski(A_24,B_25)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_6055])).

tff(c_30,plain,(
    ~ r1_tarski(k1_tarski('#skF_1'),k2_tarski('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_6063,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6059,c_30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:10:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.24/2.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.24/2.33  
% 6.24/2.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.24/2.33  %$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1
% 6.24/2.33  
% 6.24/2.33  %Foreground sorts:
% 6.24/2.33  
% 6.24/2.33  
% 6.24/2.33  %Background operators:
% 6.24/2.33  
% 6.24/2.33  
% 6.24/2.33  %Foreground operators:
% 6.24/2.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.24/2.33  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.24/2.33  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.24/2.33  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.24/2.33  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 6.24/2.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.24/2.33  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.24/2.33  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.24/2.33  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.24/2.33  tff('#skF_2', type, '#skF_2': $i).
% 6.24/2.33  tff('#skF_1', type, '#skF_1': $i).
% 6.24/2.33  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.24/2.33  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 6.24/2.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.24/2.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.24/2.33  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.24/2.33  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.24/2.33  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 6.24/2.33  
% 6.33/2.35  tff(f_41, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 6.33/2.35  tff(f_43, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 6.33/2.35  tff(f_45, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 6.33/2.35  tff(f_47, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 6.33/2.35  tff(f_49, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 6.33/2.35  tff(f_51, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 6.33/2.35  tff(f_53, axiom, (![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 6.33/2.35  tff(f_39, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k5_enumset1(A, B, C, D, E, F, G), k1_tarski(H)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t68_enumset1)).
% 6.33/2.35  tff(f_31, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_xboole_1)).
% 6.33/2.35  tff(f_33, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 6.33/2.35  tff(f_37, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 6.33/2.35  tff(f_27, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 6.33/2.35  tff(f_35, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), k5_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t96_xboole_1)).
% 6.33/2.35  tff(f_56, negated_conjecture, ~(![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 6.33/2.35  tff(c_16, plain, (![A_23]: (k2_tarski(A_23, A_23)=k1_tarski(A_23))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.33/2.35  tff(c_18, plain, (![A_24, B_25]: (k1_enumset1(A_24, A_24, B_25)=k2_tarski(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.33/2.35  tff(c_20, plain, (![A_26, B_27, C_28]: (k2_enumset1(A_26, A_26, B_27, C_28)=k1_enumset1(A_26, B_27, C_28))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.33/2.35  tff(c_22, plain, (![A_29, B_30, C_31, D_32]: (k3_enumset1(A_29, A_29, B_30, C_31, D_32)=k2_enumset1(A_29, B_30, C_31, D_32))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.33/2.35  tff(c_24, plain, (![D_36, E_37, A_33, B_34, C_35]: (k4_enumset1(A_33, A_33, B_34, C_35, D_36, E_37)=k3_enumset1(A_33, B_34, C_35, D_36, E_37))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.33/2.35  tff(c_26, plain, (![D_41, B_39, A_38, F_43, E_42, C_40]: (k5_enumset1(A_38, A_38, B_39, C_40, D_41, E_42, F_43)=k4_enumset1(A_38, B_39, C_40, D_41, E_42, F_43))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.33/2.35  tff(c_28, plain, (![C_46, E_48, F_49, G_50, A_44, B_45, D_47]: (k6_enumset1(A_44, A_44, B_45, C_46, D_47, E_48, F_49, G_50)=k5_enumset1(A_44, B_45, C_46, D_47, E_48, F_49, G_50))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.33/2.35  tff(c_471, plain, (![D_122, A_127, G_123, E_126, H_121, B_124, C_120, F_125]: (k2_xboole_0(k5_enumset1(A_127, B_124, C_120, D_122, E_126, F_125, G_123), k1_tarski(H_121))=k6_enumset1(A_127, B_124, C_120, D_122, E_126, F_125, G_123, H_121))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.33/2.35  tff(c_483, plain, (![D_41, B_39, H_121, A_38, F_43, E_42, C_40]: (k6_enumset1(A_38, A_38, B_39, C_40, D_41, E_42, F_43, H_121)=k2_xboole_0(k4_enumset1(A_38, B_39, C_40, D_41, E_42, F_43), k1_tarski(H_121)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_471])).
% 6.33/2.35  tff(c_1768, plain, (![A_181, B_183, F_185, H_182, E_184, D_187, C_186]: (k2_xboole_0(k4_enumset1(A_181, B_183, C_186, D_187, E_184, F_185), k1_tarski(H_182))=k5_enumset1(A_181, B_183, C_186, D_187, E_184, F_185, H_182))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_483])).
% 6.33/2.35  tff(c_1780, plain, (![D_36, H_182, E_37, A_33, B_34, C_35]: (k5_enumset1(A_33, A_33, B_34, C_35, D_36, E_37, H_182)=k2_xboole_0(k3_enumset1(A_33, B_34, C_35, D_36, E_37), k1_tarski(H_182)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_1768])).
% 6.33/2.35  tff(c_6008, plain, (![E_290, A_289, H_293, C_291, B_294, D_292]: (k2_xboole_0(k3_enumset1(A_289, B_294, C_291, D_292, E_290), k1_tarski(H_293))=k4_enumset1(A_289, B_294, C_291, D_292, E_290, H_293))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_1780])).
% 6.33/2.35  tff(c_6, plain, (![A_6, B_7]: (k2_xboole_0(A_6, k3_xboole_0(A_6, B_7))=A_6)), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.33/2.35  tff(c_128, plain, (![A_74, B_75, C_76]: (k4_xboole_0(k3_xboole_0(A_74, B_75), C_76)=k3_xboole_0(A_74, k4_xboole_0(B_75, C_76)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.33/2.35  tff(c_12, plain, (![A_13, B_14]: (k5_xboole_0(A_13, k4_xboole_0(B_14, A_13))=k2_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.33/2.35  tff(c_235, plain, (![C_94, A_95, B_96]: (k5_xboole_0(C_94, k3_xboole_0(A_95, k4_xboole_0(B_96, C_94)))=k2_xboole_0(C_94, k3_xboole_0(A_95, B_96)))), inference(superposition, [status(thm), theory('equality')], [c_128, c_12])).
% 6.33/2.35  tff(c_2, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(A_1, B_2))=k4_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.33/2.35  tff(c_246, plain, (![A_95, B_96]: (k4_xboole_0(A_95, k4_xboole_0(B_96, A_95))=k2_xboole_0(A_95, k3_xboole_0(A_95, B_96)))), inference(superposition, [status(thm), theory('equality')], [c_235, c_2])).
% 6.33/2.35  tff(c_265, plain, (![A_95, B_96]: (k4_xboole_0(A_95, k4_xboole_0(B_96, A_95))=A_95)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_246])).
% 6.33/2.35  tff(c_59, plain, (![A_58, B_59]: (k5_xboole_0(A_58, k4_xboole_0(B_59, A_58))=k2_xboole_0(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.33/2.35  tff(c_10, plain, (![A_11, B_12]: (r1_tarski(k4_xboole_0(A_11, B_12), k5_xboole_0(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.33/2.35  tff(c_65, plain, (![A_58, B_59]: (r1_tarski(k4_xboole_0(A_58, k4_xboole_0(B_59, A_58)), k2_xboole_0(A_58, B_59)))), inference(superposition, [status(thm), theory('equality')], [c_59, c_10])).
% 6.33/2.35  tff(c_278, plain, (![A_58, B_59]: (r1_tarski(A_58, k2_xboole_0(A_58, B_59)))), inference(demodulation, [status(thm), theory('equality')], [c_265, c_65])).
% 6.33/2.35  tff(c_6024, plain, (![B_296, H_299, E_297, D_300, A_298, C_295]: (r1_tarski(k3_enumset1(A_298, B_296, C_295, D_300, E_297), k4_enumset1(A_298, B_296, C_295, D_300, E_297, H_299)))), inference(superposition, [status(thm), theory('equality')], [c_6008, c_278])).
% 6.33/2.35  tff(c_6027, plain, (![D_36, E_37, A_33, B_34, C_35]: (r1_tarski(k3_enumset1(A_33, A_33, B_34, C_35, D_36), k3_enumset1(A_33, B_34, C_35, D_36, E_37)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_6024])).
% 6.33/2.35  tff(c_6033, plain, (![E_302, D_304, B_305, C_303, A_301]: (r1_tarski(k2_enumset1(A_301, B_305, C_303, D_304), k3_enumset1(A_301, B_305, C_303, D_304, E_302)))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_6027])).
% 6.33/2.35  tff(c_6036, plain, (![A_29, B_30, C_31, D_32]: (r1_tarski(k2_enumset1(A_29, A_29, B_30, C_31), k2_enumset1(A_29, B_30, C_31, D_32)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_6033])).
% 6.33/2.35  tff(c_6042, plain, (![A_306, B_307, C_308, D_309]: (r1_tarski(k1_enumset1(A_306, B_307, C_308), k2_enumset1(A_306, B_307, C_308, D_309)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_6036])).
% 6.33/2.35  tff(c_6045, plain, (![A_26, B_27, C_28]: (r1_tarski(k1_enumset1(A_26, A_26, B_27), k1_enumset1(A_26, B_27, C_28)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_6042])).
% 6.33/2.35  tff(c_6052, plain, (![A_310, B_311, C_312]: (r1_tarski(k2_tarski(A_310, B_311), k1_enumset1(A_310, B_311, C_312)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_6045])).
% 6.33/2.35  tff(c_6055, plain, (![A_24, B_25]: (r1_tarski(k2_tarski(A_24, A_24), k2_tarski(A_24, B_25)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_6052])).
% 6.33/2.35  tff(c_6059, plain, (![A_24, B_25]: (r1_tarski(k1_tarski(A_24), k2_tarski(A_24, B_25)))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_6055])).
% 6.33/2.35  tff(c_30, plain, (~r1_tarski(k1_tarski('#skF_1'), k2_tarski('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_56])).
% 6.33/2.35  tff(c_6063, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6059, c_30])).
% 6.33/2.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.33/2.35  
% 6.33/2.35  Inference rules
% 6.33/2.35  ----------------------
% 6.33/2.35  #Ref     : 0
% 6.33/2.35  #Sup     : 1553
% 6.33/2.35  #Fact    : 0
% 6.33/2.35  #Define  : 0
% 6.33/2.35  #Split   : 0
% 6.33/2.35  #Chain   : 0
% 6.33/2.35  #Close   : 0
% 6.33/2.35  
% 6.33/2.35  Ordering : KBO
% 6.33/2.35  
% 6.33/2.35  Simplification rules
% 6.33/2.35  ----------------------
% 6.33/2.35  #Subsume      : 0
% 6.33/2.35  #Demod        : 1762
% 6.33/2.35  #Tautology    : 574
% 6.33/2.35  #SimpNegUnit  : 0
% 6.33/2.35  #BackRed      : 10
% 6.33/2.35  
% 6.33/2.35  #Partial instantiations: 0
% 6.33/2.35  #Strategies tried      : 1
% 6.33/2.35  
% 6.33/2.35  Timing (in seconds)
% 6.33/2.35  ----------------------
% 6.33/2.35  Preprocessing        : 0.30
% 6.33/2.35  Parsing              : 0.16
% 6.33/2.35  CNF conversion       : 0.02
% 6.33/2.35  Main loop            : 1.28
% 6.33/2.35  Inferencing          : 0.38
% 6.33/2.35  Reduction            : 0.61
% 6.33/2.35  Demodulation         : 0.51
% 6.33/2.35  BG Simplification    : 0.07
% 6.33/2.35  Subsumption          : 0.16
% 6.33/2.35  Abstraction          : 0.10
% 6.33/2.35  MUC search           : 0.00
% 6.33/2.35  Cooper               : 0.00
% 6.33/2.35  Total                : 1.61
% 6.33/2.35  Index Insertion      : 0.00
% 6.33/2.35  Index Deletion       : 0.00
% 6.33/2.35  Index Matching       : 0.00
% 6.33/2.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
