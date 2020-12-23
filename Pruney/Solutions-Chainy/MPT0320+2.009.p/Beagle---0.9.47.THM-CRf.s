%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:13 EST 2020

% Result     : Theorem 19.47s
% Output     : CNFRefutation 19.47s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 116 expanded)
%              Number of leaves         :   30 (  52 expanded)
%              Depth                    :   14
%              Number of atoms          :   57 ( 108 expanded)
%              Number of equality atoms :   55 ( 106 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_31,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_29,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C,D,E,F,G] : k6_enumset1(A,A,B,C,D,E,F,G) = k5_enumset1(A,B,C,D,E,F,G) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k5_enumset1(A,B,C,D,E,F,G),k1_tarski(H)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k2_xboole_0(A,B),C) = k2_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
      & k2_zfmisc_1(C,k2_xboole_0(A,B)) = k2_xboole_0(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t120_zfmisc_1)).

tff(f_52,negated_conjecture,(
    ~ ! [A,B,C] :
        ( k2_zfmisc_1(k2_tarski(A,B),C) = k2_xboole_0(k2_zfmisc_1(k1_tarski(A),C),k2_zfmisc_1(k1_tarski(B),C))
        & k2_zfmisc_1(C,k2_tarski(A,B)) = k2_xboole_0(k2_zfmisc_1(C,k1_tarski(A)),k2_zfmisc_1(C,k1_tarski(B))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_zfmisc_1)).

tff(c_6,plain,(
    ! [A_10,B_11] : k1_enumset1(A_10,A_10,B_11) = k2_tarski(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4,plain,(
    ! [A_9] : k2_tarski(A_9,A_9) = k1_tarski(A_9) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_8,plain,(
    ! [A_12,B_13,C_14] : k2_enumset1(A_12,A_12,B_13,C_14) = k1_enumset1(A_12,B_13,C_14) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [A_15,B_16,C_17,D_18] : k3_enumset1(A_15,A_15,B_16,C_17,D_18) = k2_enumset1(A_15,B_16,C_17,D_18) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [A_19,C_21,D_22,B_20,E_23] : k4_enumset1(A_19,A_19,B_20,C_21,D_22,E_23) = k3_enumset1(A_19,B_20,C_21,D_22,E_23) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_14,plain,(
    ! [A_24,B_25,F_29,D_27,C_26,E_28] : k5_enumset1(A_24,A_24,B_25,C_26,D_27,E_28,F_29) = k4_enumset1(A_24,B_25,C_26,D_27,E_28,F_29) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_16,plain,(
    ! [D_33,A_30,C_32,B_31,E_34,G_36,F_35] : k6_enumset1(A_30,A_30,B_31,C_32,D_33,E_34,F_35,G_36) = k5_enumset1(A_30,B_31,C_32,D_33,E_34,F_35,G_36) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_18563,plain,(
    ! [H_266,C_264,A_265,D_262,F_259,E_261,G_260,B_263] : k2_xboole_0(k5_enumset1(A_265,B_263,C_264,D_262,E_261,F_259,G_260),k1_tarski(H_266)) = k6_enumset1(A_265,B_263,C_264,D_262,E_261,F_259,G_260,H_266) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_18572,plain,(
    ! [A_24,B_25,F_29,H_266,D_27,C_26,E_28] : k6_enumset1(A_24,A_24,B_25,C_26,D_27,E_28,F_29,H_266) = k2_xboole_0(k4_enumset1(A_24,B_25,C_26,D_27,E_28,F_29),k1_tarski(H_266)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_18563])).

tff(c_21514,plain,(
    ! [F_286,H_287,E_285,D_289,A_288,C_283,B_284] : k2_xboole_0(k4_enumset1(A_288,B_284,C_283,D_289,E_285,F_286),k1_tarski(H_287)) = k5_enumset1(A_288,B_284,C_283,D_289,E_285,F_286,H_287) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_18572])).

tff(c_21523,plain,(
    ! [A_19,H_287,C_21,D_22,B_20,E_23] : k5_enumset1(A_19,A_19,B_20,C_21,D_22,E_23,H_287) = k2_xboole_0(k3_enumset1(A_19,B_20,C_21,D_22,E_23),k1_tarski(H_287)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_21514])).

tff(c_32397,plain,(
    ! [E_329,H_330,D_333,C_328,A_332,B_331] : k2_xboole_0(k3_enumset1(A_332,B_331,C_328,D_333,E_329),k1_tarski(H_330)) = k4_enumset1(A_332,B_331,C_328,D_333,E_329,H_330) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_21523])).

tff(c_32406,plain,(
    ! [B_16,A_15,D_18,H_330,C_17] : k4_enumset1(A_15,A_15,B_16,C_17,D_18,H_330) = k2_xboole_0(k2_enumset1(A_15,B_16,C_17,D_18),k1_tarski(H_330)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_32397])).

tff(c_32410,plain,(
    ! [C_334,H_335,D_336,A_338,B_337] : k2_xboole_0(k2_enumset1(A_338,B_337,C_334,D_336),k1_tarski(H_335)) = k3_enumset1(A_338,B_337,C_334,D_336,H_335) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_32406])).

tff(c_32419,plain,(
    ! [A_12,B_13,C_14,H_335] : k3_enumset1(A_12,A_12,B_13,C_14,H_335) = k2_xboole_0(k1_enumset1(A_12,B_13,C_14),k1_tarski(H_335)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_32410])).

tff(c_32423,plain,(
    ! [A_339,B_340,C_341,H_342] : k2_xboole_0(k1_enumset1(A_339,B_340,C_341),k1_tarski(H_342)) = k2_enumset1(A_339,B_340,C_341,H_342) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_32419])).

tff(c_32432,plain,(
    ! [A_10,B_11,H_342] : k2_xboole_0(k2_tarski(A_10,B_11),k1_tarski(H_342)) = k2_enumset1(A_10,A_10,B_11,H_342) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_32423])).

tff(c_32437,plain,(
    ! [A_343,B_344,H_345] : k2_xboole_0(k2_tarski(A_343,B_344),k1_tarski(H_345)) = k1_enumset1(A_343,B_344,H_345) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_32432])).

tff(c_32446,plain,(
    ! [A_9,H_345] : k2_xboole_0(k1_tarski(A_9),k1_tarski(H_345)) = k1_enumset1(A_9,A_9,H_345) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_32437])).

tff(c_32449,plain,(
    ! [A_9,H_345] : k2_xboole_0(k1_tarski(A_9),k1_tarski(H_345)) = k2_tarski(A_9,H_345) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_32446])).

tff(c_1185,plain,(
    ! [F_97,E_99,C_102,D_100,H_104,B_101,A_103,G_98] : k2_xboole_0(k5_enumset1(A_103,B_101,C_102,D_100,E_99,F_97,G_98),k1_tarski(H_104)) = k6_enumset1(A_103,B_101,C_102,D_100,E_99,F_97,G_98,H_104) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_1194,plain,(
    ! [A_24,B_25,F_29,D_27,C_26,H_104,E_28] : k6_enumset1(A_24,A_24,B_25,C_26,D_27,E_28,F_29,H_104) = k2_xboole_0(k4_enumset1(A_24,B_25,C_26,D_27,E_28,F_29),k1_tarski(H_104)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_1185])).

tff(c_4346,plain,(
    ! [A_133,E_131,F_132,B_130,D_135,H_134,C_129] : k2_xboole_0(k4_enumset1(A_133,B_130,C_129,D_135,E_131,F_132),k1_tarski(H_134)) = k5_enumset1(A_133,B_130,C_129,D_135,E_131,F_132,H_134) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_1194])).

tff(c_4355,plain,(
    ! [A_19,C_21,D_22,B_20,H_134,E_23] : k5_enumset1(A_19,A_19,B_20,C_21,D_22,E_23,H_134) = k2_xboole_0(k3_enumset1(A_19,B_20,C_21,D_22,E_23),k1_tarski(H_134)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_4346])).

tff(c_14072,plain,(
    ! [B_180,A_181,H_182,D_183,C_178,E_179] : k2_xboole_0(k3_enumset1(A_181,B_180,C_178,D_183,E_179),k1_tarski(H_182)) = k4_enumset1(A_181,B_180,C_178,D_183,E_179,H_182) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_4355])).

tff(c_14081,plain,(
    ! [B_16,A_15,D_18,H_182,C_17] : k4_enumset1(A_15,A_15,B_16,C_17,D_18,H_182) = k2_xboole_0(k2_enumset1(A_15,B_16,C_17,D_18),k1_tarski(H_182)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_14072])).

tff(c_14085,plain,(
    ! [H_187,C_184,A_188,B_186,D_185] : k2_xboole_0(k2_enumset1(A_188,B_186,C_184,D_185),k1_tarski(H_187)) = k3_enumset1(A_188,B_186,C_184,D_185,H_187) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_14081])).

tff(c_14094,plain,(
    ! [A_12,B_13,C_14,H_187] : k3_enumset1(A_12,A_12,B_13,C_14,H_187) = k2_xboole_0(k1_enumset1(A_12,B_13,C_14),k1_tarski(H_187)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_14085])).

tff(c_14098,plain,(
    ! [A_189,B_190,C_191,H_192] : k2_xboole_0(k1_enumset1(A_189,B_190,C_191),k1_tarski(H_192)) = k2_enumset1(A_189,B_190,C_191,H_192) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_14094])).

tff(c_14107,plain,(
    ! [A_10,B_11,H_192] : k2_xboole_0(k2_tarski(A_10,B_11),k1_tarski(H_192)) = k2_enumset1(A_10,A_10,B_11,H_192) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_14098])).

tff(c_14111,plain,(
    ! [A_193,B_194,H_195] : k2_xboole_0(k2_tarski(A_193,B_194),k1_tarski(H_195)) = k1_enumset1(A_193,B_194,H_195) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_14107])).

tff(c_14120,plain,(
    ! [A_9,H_195] : k2_xboole_0(k1_tarski(A_9),k1_tarski(H_195)) = k1_enumset1(A_9,A_9,H_195) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_14111])).

tff(c_14123,plain,(
    ! [A_9,H_195] : k2_xboole_0(k1_tarski(A_9),k1_tarski(H_195)) = k2_tarski(A_9,H_195) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_14120])).

tff(c_18,plain,(
    ! [A_37,C_39,B_38] : k2_xboole_0(k2_zfmisc_1(A_37,C_39),k2_zfmisc_1(B_38,C_39)) = k2_zfmisc_1(k2_xboole_0(A_37,B_38),C_39) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_20,plain,(
    ! [C_39,A_37,B_38] : k2_xboole_0(k2_zfmisc_1(C_39,A_37),k2_zfmisc_1(C_39,B_38)) = k2_zfmisc_1(C_39,k2_xboole_0(A_37,B_38)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_24,plain,
    ( k2_xboole_0(k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_6'),k2_zfmisc_1(k1_tarski('#skF_5'),'#skF_6')) != k2_zfmisc_1(k2_tarski('#skF_4','#skF_5'),'#skF_6')
    | k2_xboole_0(k2_zfmisc_1('#skF_3',k1_tarski('#skF_1')),k2_zfmisc_1('#skF_3',k1_tarski('#skF_2'))) != k2_zfmisc_1('#skF_3',k2_tarski('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_25,plain,
    ( k2_xboole_0(k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_6'),k2_zfmisc_1(k1_tarski('#skF_5'),'#skF_6')) != k2_zfmisc_1(k2_tarski('#skF_4','#skF_5'),'#skF_6')
    | k2_zfmisc_1('#skF_3',k2_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2'))) != k2_zfmisc_1('#skF_3',k2_tarski('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_24])).

tff(c_26,plain,
    ( k2_zfmisc_1(k2_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_5')),'#skF_6') != k2_zfmisc_1(k2_tarski('#skF_4','#skF_5'),'#skF_6')
    | k2_zfmisc_1('#skF_3',k2_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2'))) != k2_zfmisc_1('#skF_3',k2_tarski('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_25])).

tff(c_139,plain,(
    k2_zfmisc_1('#skF_3',k2_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2'))) != k2_zfmisc_1('#skF_3',k2_tarski('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_14126,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14123,c_139])).

tff(c_14127,plain,(
    k2_zfmisc_1(k2_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_5')),'#skF_6') != k2_zfmisc_1(k2_tarski('#skF_4','#skF_5'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_32460,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32449,c_14127])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:35:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 19.47/10.17  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 19.47/10.17  
% 19.47/10.17  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 19.47/10.18  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 19.47/10.18  
% 19.47/10.18  %Foreground sorts:
% 19.47/10.18  
% 19.47/10.18  
% 19.47/10.18  %Background operators:
% 19.47/10.18  
% 19.47/10.18  
% 19.47/10.18  %Foreground operators:
% 19.47/10.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 19.47/10.18  tff(k1_tarski, type, k1_tarski: $i > $i).
% 19.47/10.18  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 19.47/10.18  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 19.47/10.18  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 19.47/10.18  tff('#skF_5', type, '#skF_5': $i).
% 19.47/10.18  tff('#skF_6', type, '#skF_6': $i).
% 19.47/10.18  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 19.47/10.18  tff('#skF_2', type, '#skF_2': $i).
% 19.47/10.18  tff('#skF_3', type, '#skF_3': $i).
% 19.47/10.18  tff('#skF_1', type, '#skF_1': $i).
% 19.47/10.18  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 19.47/10.18  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 19.47/10.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 19.47/10.18  tff(k3_tarski, type, k3_tarski: $i > $i).
% 19.47/10.18  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 19.47/10.18  tff('#skF_4', type, '#skF_4': $i).
% 19.47/10.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 19.47/10.18  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 19.47/10.18  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 19.47/10.18  
% 19.47/10.19  tff(f_31, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 19.47/10.19  tff(f_29, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 19.47/10.19  tff(f_33, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 19.47/10.19  tff(f_35, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 19.47/10.19  tff(f_37, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 19.47/10.19  tff(f_39, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 19.47/10.19  tff(f_41, axiom, (![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 19.47/10.19  tff(f_27, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k5_enumset1(A, B, C, D, E, F, G), k1_tarski(H)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t68_enumset1)).
% 19.47/10.19  tff(f_45, axiom, (![A, B, C]: ((k2_zfmisc_1(k2_xboole_0(A, B), C) = k2_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, C))) & (k2_zfmisc_1(C, k2_xboole_0(A, B)) = k2_xboole_0(k2_zfmisc_1(C, A), k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t120_zfmisc_1)).
% 19.47/10.19  tff(f_52, negated_conjecture, ~(![A, B, C]: ((k2_zfmisc_1(k2_tarski(A, B), C) = k2_xboole_0(k2_zfmisc_1(k1_tarski(A), C), k2_zfmisc_1(k1_tarski(B), C))) & (k2_zfmisc_1(C, k2_tarski(A, B)) = k2_xboole_0(k2_zfmisc_1(C, k1_tarski(A)), k2_zfmisc_1(C, k1_tarski(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t132_zfmisc_1)).
% 19.47/10.19  tff(c_6, plain, (![A_10, B_11]: (k1_enumset1(A_10, A_10, B_11)=k2_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_31])).
% 19.47/10.19  tff(c_4, plain, (![A_9]: (k2_tarski(A_9, A_9)=k1_tarski(A_9))), inference(cnfTransformation, [status(thm)], [f_29])).
% 19.47/10.19  tff(c_8, plain, (![A_12, B_13, C_14]: (k2_enumset1(A_12, A_12, B_13, C_14)=k1_enumset1(A_12, B_13, C_14))), inference(cnfTransformation, [status(thm)], [f_33])).
% 19.47/10.19  tff(c_10, plain, (![A_15, B_16, C_17, D_18]: (k3_enumset1(A_15, A_15, B_16, C_17, D_18)=k2_enumset1(A_15, B_16, C_17, D_18))), inference(cnfTransformation, [status(thm)], [f_35])).
% 19.47/10.19  tff(c_12, plain, (![A_19, C_21, D_22, B_20, E_23]: (k4_enumset1(A_19, A_19, B_20, C_21, D_22, E_23)=k3_enumset1(A_19, B_20, C_21, D_22, E_23))), inference(cnfTransformation, [status(thm)], [f_37])).
% 19.47/10.19  tff(c_14, plain, (![A_24, B_25, F_29, D_27, C_26, E_28]: (k5_enumset1(A_24, A_24, B_25, C_26, D_27, E_28, F_29)=k4_enumset1(A_24, B_25, C_26, D_27, E_28, F_29))), inference(cnfTransformation, [status(thm)], [f_39])).
% 19.47/10.19  tff(c_16, plain, (![D_33, A_30, C_32, B_31, E_34, G_36, F_35]: (k6_enumset1(A_30, A_30, B_31, C_32, D_33, E_34, F_35, G_36)=k5_enumset1(A_30, B_31, C_32, D_33, E_34, F_35, G_36))), inference(cnfTransformation, [status(thm)], [f_41])).
% 19.47/10.19  tff(c_18563, plain, (![H_266, C_264, A_265, D_262, F_259, E_261, G_260, B_263]: (k2_xboole_0(k5_enumset1(A_265, B_263, C_264, D_262, E_261, F_259, G_260), k1_tarski(H_266))=k6_enumset1(A_265, B_263, C_264, D_262, E_261, F_259, G_260, H_266))), inference(cnfTransformation, [status(thm)], [f_27])).
% 19.47/10.19  tff(c_18572, plain, (![A_24, B_25, F_29, H_266, D_27, C_26, E_28]: (k6_enumset1(A_24, A_24, B_25, C_26, D_27, E_28, F_29, H_266)=k2_xboole_0(k4_enumset1(A_24, B_25, C_26, D_27, E_28, F_29), k1_tarski(H_266)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_18563])).
% 19.47/10.19  tff(c_21514, plain, (![F_286, H_287, E_285, D_289, A_288, C_283, B_284]: (k2_xboole_0(k4_enumset1(A_288, B_284, C_283, D_289, E_285, F_286), k1_tarski(H_287))=k5_enumset1(A_288, B_284, C_283, D_289, E_285, F_286, H_287))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_18572])).
% 19.47/10.19  tff(c_21523, plain, (![A_19, H_287, C_21, D_22, B_20, E_23]: (k5_enumset1(A_19, A_19, B_20, C_21, D_22, E_23, H_287)=k2_xboole_0(k3_enumset1(A_19, B_20, C_21, D_22, E_23), k1_tarski(H_287)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_21514])).
% 19.47/10.19  tff(c_32397, plain, (![E_329, H_330, D_333, C_328, A_332, B_331]: (k2_xboole_0(k3_enumset1(A_332, B_331, C_328, D_333, E_329), k1_tarski(H_330))=k4_enumset1(A_332, B_331, C_328, D_333, E_329, H_330))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_21523])).
% 19.47/10.19  tff(c_32406, plain, (![B_16, A_15, D_18, H_330, C_17]: (k4_enumset1(A_15, A_15, B_16, C_17, D_18, H_330)=k2_xboole_0(k2_enumset1(A_15, B_16, C_17, D_18), k1_tarski(H_330)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_32397])).
% 19.47/10.19  tff(c_32410, plain, (![C_334, H_335, D_336, A_338, B_337]: (k2_xboole_0(k2_enumset1(A_338, B_337, C_334, D_336), k1_tarski(H_335))=k3_enumset1(A_338, B_337, C_334, D_336, H_335))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_32406])).
% 19.47/10.19  tff(c_32419, plain, (![A_12, B_13, C_14, H_335]: (k3_enumset1(A_12, A_12, B_13, C_14, H_335)=k2_xboole_0(k1_enumset1(A_12, B_13, C_14), k1_tarski(H_335)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_32410])).
% 19.47/10.19  tff(c_32423, plain, (![A_339, B_340, C_341, H_342]: (k2_xboole_0(k1_enumset1(A_339, B_340, C_341), k1_tarski(H_342))=k2_enumset1(A_339, B_340, C_341, H_342))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_32419])).
% 19.47/10.19  tff(c_32432, plain, (![A_10, B_11, H_342]: (k2_xboole_0(k2_tarski(A_10, B_11), k1_tarski(H_342))=k2_enumset1(A_10, A_10, B_11, H_342))), inference(superposition, [status(thm), theory('equality')], [c_6, c_32423])).
% 19.47/10.19  tff(c_32437, plain, (![A_343, B_344, H_345]: (k2_xboole_0(k2_tarski(A_343, B_344), k1_tarski(H_345))=k1_enumset1(A_343, B_344, H_345))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_32432])).
% 19.47/10.19  tff(c_32446, plain, (![A_9, H_345]: (k2_xboole_0(k1_tarski(A_9), k1_tarski(H_345))=k1_enumset1(A_9, A_9, H_345))), inference(superposition, [status(thm), theory('equality')], [c_4, c_32437])).
% 19.47/10.19  tff(c_32449, plain, (![A_9, H_345]: (k2_xboole_0(k1_tarski(A_9), k1_tarski(H_345))=k2_tarski(A_9, H_345))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_32446])).
% 19.47/10.19  tff(c_1185, plain, (![F_97, E_99, C_102, D_100, H_104, B_101, A_103, G_98]: (k2_xboole_0(k5_enumset1(A_103, B_101, C_102, D_100, E_99, F_97, G_98), k1_tarski(H_104))=k6_enumset1(A_103, B_101, C_102, D_100, E_99, F_97, G_98, H_104))), inference(cnfTransformation, [status(thm)], [f_27])).
% 19.47/10.19  tff(c_1194, plain, (![A_24, B_25, F_29, D_27, C_26, H_104, E_28]: (k6_enumset1(A_24, A_24, B_25, C_26, D_27, E_28, F_29, H_104)=k2_xboole_0(k4_enumset1(A_24, B_25, C_26, D_27, E_28, F_29), k1_tarski(H_104)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_1185])).
% 19.47/10.19  tff(c_4346, plain, (![A_133, E_131, F_132, B_130, D_135, H_134, C_129]: (k2_xboole_0(k4_enumset1(A_133, B_130, C_129, D_135, E_131, F_132), k1_tarski(H_134))=k5_enumset1(A_133, B_130, C_129, D_135, E_131, F_132, H_134))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_1194])).
% 19.47/10.19  tff(c_4355, plain, (![A_19, C_21, D_22, B_20, H_134, E_23]: (k5_enumset1(A_19, A_19, B_20, C_21, D_22, E_23, H_134)=k2_xboole_0(k3_enumset1(A_19, B_20, C_21, D_22, E_23), k1_tarski(H_134)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_4346])).
% 19.47/10.19  tff(c_14072, plain, (![B_180, A_181, H_182, D_183, C_178, E_179]: (k2_xboole_0(k3_enumset1(A_181, B_180, C_178, D_183, E_179), k1_tarski(H_182))=k4_enumset1(A_181, B_180, C_178, D_183, E_179, H_182))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_4355])).
% 19.47/10.19  tff(c_14081, plain, (![B_16, A_15, D_18, H_182, C_17]: (k4_enumset1(A_15, A_15, B_16, C_17, D_18, H_182)=k2_xboole_0(k2_enumset1(A_15, B_16, C_17, D_18), k1_tarski(H_182)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_14072])).
% 19.47/10.19  tff(c_14085, plain, (![H_187, C_184, A_188, B_186, D_185]: (k2_xboole_0(k2_enumset1(A_188, B_186, C_184, D_185), k1_tarski(H_187))=k3_enumset1(A_188, B_186, C_184, D_185, H_187))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_14081])).
% 19.47/10.19  tff(c_14094, plain, (![A_12, B_13, C_14, H_187]: (k3_enumset1(A_12, A_12, B_13, C_14, H_187)=k2_xboole_0(k1_enumset1(A_12, B_13, C_14), k1_tarski(H_187)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_14085])).
% 19.47/10.19  tff(c_14098, plain, (![A_189, B_190, C_191, H_192]: (k2_xboole_0(k1_enumset1(A_189, B_190, C_191), k1_tarski(H_192))=k2_enumset1(A_189, B_190, C_191, H_192))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_14094])).
% 19.47/10.19  tff(c_14107, plain, (![A_10, B_11, H_192]: (k2_xboole_0(k2_tarski(A_10, B_11), k1_tarski(H_192))=k2_enumset1(A_10, A_10, B_11, H_192))), inference(superposition, [status(thm), theory('equality')], [c_6, c_14098])).
% 19.47/10.19  tff(c_14111, plain, (![A_193, B_194, H_195]: (k2_xboole_0(k2_tarski(A_193, B_194), k1_tarski(H_195))=k1_enumset1(A_193, B_194, H_195))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_14107])).
% 19.47/10.19  tff(c_14120, plain, (![A_9, H_195]: (k2_xboole_0(k1_tarski(A_9), k1_tarski(H_195))=k1_enumset1(A_9, A_9, H_195))), inference(superposition, [status(thm), theory('equality')], [c_4, c_14111])).
% 19.47/10.19  tff(c_14123, plain, (![A_9, H_195]: (k2_xboole_0(k1_tarski(A_9), k1_tarski(H_195))=k2_tarski(A_9, H_195))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_14120])).
% 19.47/10.19  tff(c_18, plain, (![A_37, C_39, B_38]: (k2_xboole_0(k2_zfmisc_1(A_37, C_39), k2_zfmisc_1(B_38, C_39))=k2_zfmisc_1(k2_xboole_0(A_37, B_38), C_39))), inference(cnfTransformation, [status(thm)], [f_45])).
% 19.47/10.19  tff(c_20, plain, (![C_39, A_37, B_38]: (k2_xboole_0(k2_zfmisc_1(C_39, A_37), k2_zfmisc_1(C_39, B_38))=k2_zfmisc_1(C_39, k2_xboole_0(A_37, B_38)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 19.47/10.19  tff(c_24, plain, (k2_xboole_0(k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_6'), k2_zfmisc_1(k1_tarski('#skF_5'), '#skF_6'))!=k2_zfmisc_1(k2_tarski('#skF_4', '#skF_5'), '#skF_6') | k2_xboole_0(k2_zfmisc_1('#skF_3', k1_tarski('#skF_1')), k2_zfmisc_1('#skF_3', k1_tarski('#skF_2')))!=k2_zfmisc_1('#skF_3', k2_tarski('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_52])).
% 19.47/10.19  tff(c_25, plain, (k2_xboole_0(k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_6'), k2_zfmisc_1(k1_tarski('#skF_5'), '#skF_6'))!=k2_zfmisc_1(k2_tarski('#skF_4', '#skF_5'), '#skF_6') | k2_zfmisc_1('#skF_3', k2_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2')))!=k2_zfmisc_1('#skF_3', k2_tarski('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_24])).
% 19.47/10.19  tff(c_26, plain, (k2_zfmisc_1(k2_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_5')), '#skF_6')!=k2_zfmisc_1(k2_tarski('#skF_4', '#skF_5'), '#skF_6') | k2_zfmisc_1('#skF_3', k2_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2')))!=k2_zfmisc_1('#skF_3', k2_tarski('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_25])).
% 19.47/10.19  tff(c_139, plain, (k2_zfmisc_1('#skF_3', k2_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2')))!=k2_zfmisc_1('#skF_3', k2_tarski('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_26])).
% 19.47/10.19  tff(c_14126, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14123, c_139])).
% 19.47/10.19  tff(c_14127, plain, (k2_zfmisc_1(k2_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_5')), '#skF_6')!=k2_zfmisc_1(k2_tarski('#skF_4', '#skF_5'), '#skF_6')), inference(splitRight, [status(thm)], [c_26])).
% 19.47/10.19  tff(c_32460, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32449, c_14127])).
% 19.47/10.19  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 19.47/10.19  
% 19.47/10.19  Inference rules
% 19.47/10.19  ----------------------
% 19.47/10.19  #Ref     : 0
% 19.47/10.19  #Sup     : 7709
% 19.47/10.19  #Fact    : 0
% 19.47/10.19  #Define  : 0
% 19.47/10.19  #Split   : 1
% 19.47/10.19  #Chain   : 0
% 19.47/10.19  #Close   : 0
% 19.47/10.19  
% 19.47/10.19  Ordering : KBO
% 19.47/10.19  
% 19.47/10.19  Simplification rules
% 19.47/10.19  ----------------------
% 19.47/10.19  #Subsume      : 474
% 19.47/10.19  #Demod        : 12074
% 19.47/10.19  #Tautology    : 636
% 19.47/10.19  #SimpNegUnit  : 0
% 19.47/10.19  #BackRed      : 5
% 19.47/10.19  
% 19.47/10.19  #Partial instantiations: 0
% 19.47/10.19  #Strategies tried      : 1
% 19.47/10.19  
% 19.47/10.19  Timing (in seconds)
% 19.47/10.19  ----------------------
% 19.47/10.19  Preprocessing        : 0.33
% 19.47/10.19  Parsing              : 0.18
% 19.47/10.19  CNF conversion       : 0.02
% 19.47/10.19  Main loop            : 9.05
% 19.47/10.19  Inferencing          : 1.33
% 19.47/10.20  Reduction            : 6.60
% 19.47/10.20  Demodulation         : 6.21
% 19.47/10.20  BG Simplification    : 0.29
% 19.47/10.20  Subsumption          : 0.65
% 19.47/10.20  Abstraction          : 0.50
% 19.47/10.20  MUC search           : 0.00
% 19.47/10.20  Cooper               : 0.00
% 19.47/10.20  Total                : 9.40
% 19.47/10.20  Index Insertion      : 0.00
% 19.47/10.20  Index Deletion       : 0.00
% 19.47/10.20  Index Matching       : 0.00
% 19.47/10.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
