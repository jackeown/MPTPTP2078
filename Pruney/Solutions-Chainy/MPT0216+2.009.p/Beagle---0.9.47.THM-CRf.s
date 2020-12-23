%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:44 EST 2020

% Result     : Theorem 6.96s
% Output     : CNFRefutation 6.96s
% Verified   : 
% Statistics : Number of formulae       :   87 (1111 expanded)
%              Number of leaves         :   33 ( 384 expanded)
%              Depth                    :   23
%              Number of atoms          :   96 (1343 expanded)
%              Number of equality atoms :   87 (1305 expanded)
%              Maximal formula depth    :   24 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k7_enumset1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_5 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_85,negated_conjecture,(
    ~ ! [A,B,C] :
        ( k1_tarski(A) = k2_tarski(B,C)
       => B = C ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_zfmisc_1)).

tff(f_70,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_72,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_74,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_76,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_78,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_66,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k1_tarski(A),k5_enumset1(B,C,D,E,F,G,H)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_enumset1)).

tff(f_68,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_80,axiom,(
    ! [A,B,C,D,E,F,G] : k6_enumset1(A,A,B,C,D,E,F,G) = k5_enumset1(A,B,C,D,E,F,G) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

tff(f_64,axiom,(
    ! [A,B,C,D,E,F,G,H,I] : k7_enumset1(A,B,C,D,E,F,G,H,I) = k2_xboole_0(k1_tarski(A),k6_enumset1(B,C,D,E,F,G,H,I)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_enumset1)).

tff(f_62,axiom,(
    ! [A,B,C,D,E,F,G,H,I,J] :
      ( J = k7_enumset1(A,B,C,D,E,F,G,H,I)
    <=> ! [K] :
          ( r2_hidden(K,J)
        <=> ~ ( K != A
              & K != B
              & K != C
              & K != D
              & K != E
              & K != F
              & K != G
              & K != H
              & K != I ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_enumset1)).

tff(c_86,plain,(
    k2_tarski('#skF_4','#skF_5') = k1_tarski('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_72,plain,(
    ! [A_36,B_37] : k1_enumset1(A_36,A_36,B_37) = k2_tarski(A_36,B_37) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_74,plain,(
    ! [A_38,B_39,C_40] : k2_enumset1(A_38,A_38,B_39,C_40) = k1_enumset1(A_38,B_39,C_40) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_76,plain,(
    ! [A_41,B_42,C_43,D_44] : k3_enumset1(A_41,A_41,B_42,C_43,D_44) = k2_enumset1(A_41,B_42,C_43,D_44) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_78,plain,(
    ! [D_48,C_47,A_45,B_46,E_49] : k4_enumset1(A_45,A_45,B_46,C_47,D_48,E_49) = k3_enumset1(A_45,B_46,C_47,D_48,E_49) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_80,plain,(
    ! [A_50,B_51,E_54,C_52,D_53,F_55] : k5_enumset1(A_50,A_50,B_51,C_52,D_53,E_54,F_55) = k4_enumset1(A_50,B_51,C_52,D_53,E_54,F_55) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_181,plain,(
    ! [D_179,C_177,G_182,F_176,E_180,H_178,A_183,B_181] : k2_xboole_0(k1_tarski(A_183),k5_enumset1(B_181,C_177,D_179,E_180,F_176,G_182,H_178)) = k6_enumset1(A_183,B_181,C_177,D_179,E_180,F_176,G_182,H_178) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_193,plain,(
    ! [C_187,B_188,A_185,E_184,F_189,A_186,D_190] : k6_enumset1(A_186,A_185,A_185,B_188,C_187,D_190,E_184,F_189) = k2_xboole_0(k1_tarski(A_186),k4_enumset1(A_185,B_188,C_187,D_190,E_184,F_189)) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_181])).

tff(c_360,plain,(
    ! [A_228,C_230,B_227,A_232,D_229,E_231] : k6_enumset1(A_232,A_228,A_228,A_228,B_227,C_230,D_229,E_231) = k2_xboole_0(k1_tarski(A_232),k3_enumset1(A_228,B_227,C_230,D_229,E_231)) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_193])).

tff(c_535,plain,(
    ! [A_263,B_267,A_266,D_265,C_264] : k6_enumset1(A_266,A_263,A_263,A_263,A_263,B_267,C_264,D_265) = k2_xboole_0(k1_tarski(A_266),k2_enumset1(A_263,B_267,C_264,D_265)) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_360])).

tff(c_734,plain,(
    ! [A_290,A_291,B_292,C_293] : k6_enumset1(A_290,A_291,A_291,A_291,A_291,A_291,B_292,C_293) = k2_xboole_0(k1_tarski(A_290),k1_enumset1(A_291,B_292,C_293)) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_535])).

tff(c_1014,plain,(
    ! [A_336,A_337,B_338] : k6_enumset1(A_336,A_337,A_337,A_337,A_337,A_337,A_337,B_338) = k2_xboole_0(k1_tarski(A_336),k2_tarski(A_337,B_338)) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_734])).

tff(c_1110,plain,(
    ! [A_336] : k2_xboole_0(k1_tarski(A_336),k1_tarski('#skF_3')) = k6_enumset1(A_336,'#skF_4','#skF_4','#skF_4','#skF_4','#skF_4','#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_1014])).

tff(c_70,plain,(
    ! [A_35] : k2_tarski(A_35,A_35) = k1_tarski(A_35) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_82,plain,(
    ! [D_59,A_56,B_57,G_62,F_61,C_58,E_60] : k6_enumset1(A_56,A_56,B_57,C_58,D_59,E_60,F_61,G_62) = k5_enumset1(A_56,B_57,C_58,D_59,E_60,F_61,G_62) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_203,plain,(
    ! [C_187,B_188,A_185,E_184,F_189,D_190] : k2_xboole_0(k1_tarski(A_185),k4_enumset1(A_185,B_188,C_187,D_190,E_184,F_189)) = k5_enumset1(A_185,A_185,B_188,C_187,D_190,E_184,F_189) ),
    inference(superposition,[status(thm),theory(equality)],[c_193,c_82])).

tff(c_223,plain,(
    ! [A_191,B_192,C_195,D_194,E_196,F_193] : k2_xboole_0(k1_tarski(A_191),k4_enumset1(A_191,B_192,C_195,D_194,E_196,F_193)) = k4_enumset1(A_191,B_192,C_195,D_194,E_196,F_193) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_203])).

tff(c_239,plain,(
    ! [D_48,C_47,A_45,B_46,E_49] : k2_xboole_0(k1_tarski(A_45),k3_enumset1(A_45,B_46,C_47,D_48,E_49)) = k4_enumset1(A_45,A_45,B_46,C_47,D_48,E_49) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_223])).

tff(c_243,plain,(
    ! [C_200,E_201,D_199,A_198,B_197] : k2_xboole_0(k1_tarski(A_198),k3_enumset1(A_198,B_197,C_200,D_199,E_201)) = k3_enumset1(A_198,B_197,C_200,D_199,E_201) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_239])).

tff(c_252,plain,(
    ! [A_41,B_42,C_43,D_44] : k2_xboole_0(k1_tarski(A_41),k2_enumset1(A_41,B_42,C_43,D_44)) = k3_enumset1(A_41,A_41,B_42,C_43,D_44) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_243])).

tff(c_256,plain,(
    ! [A_202,B_203,C_204,D_205] : k2_xboole_0(k1_tarski(A_202),k2_enumset1(A_202,B_203,C_204,D_205)) = k2_enumset1(A_202,B_203,C_204,D_205) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_252])).

tff(c_265,plain,(
    ! [A_38,B_39,C_40] : k2_xboole_0(k1_tarski(A_38),k1_enumset1(A_38,B_39,C_40)) = k2_enumset1(A_38,A_38,B_39,C_40) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_256])).

tff(c_285,plain,(
    ! [A_215,B_216,C_217] : k2_xboole_0(k1_tarski(A_215),k1_enumset1(A_215,B_216,C_217)) = k1_enumset1(A_215,B_216,C_217) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_265])).

tff(c_294,plain,(
    ! [A_36,B_37] : k2_xboole_0(k1_tarski(A_36),k2_tarski(A_36,B_37)) = k1_enumset1(A_36,A_36,B_37) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_285])).

tff(c_298,plain,(
    ! [A_218,B_219] : k2_xboole_0(k1_tarski(A_218),k2_tarski(A_218,B_219)) = k2_tarski(A_218,B_219) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_294])).

tff(c_307,plain,(
    ! [A_35] : k2_xboole_0(k1_tarski(A_35),k1_tarski(A_35)) = k2_tarski(A_35,A_35) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_298])).

tff(c_313,plain,(
    ! [A_35] : k2_xboole_0(k1_tarski(A_35),k1_tarski(A_35)) = k1_tarski(A_35) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_307])).

tff(c_1333,plain,(
    ! [A_357] : k2_xboole_0(k1_tarski(A_357),k1_tarski('#skF_3')) = k6_enumset1(A_357,'#skF_4','#skF_4','#skF_4','#skF_4','#skF_4','#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_1014])).

tff(c_1353,plain,(
    k6_enumset1('#skF_3','#skF_4','#skF_4','#skF_4','#skF_4','#skF_4','#skF_4','#skF_5') = k1_tarski('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_313,c_1333])).

tff(c_66,plain,(
    ! [H_25,E_22,G_24,D_21,F_23,A_18,C_20,B_19,I_26] : k2_xboole_0(k1_tarski(A_18),k6_enumset1(B_19,C_20,D_21,E_22,F_23,G_24,H_25,I_26)) = k7_enumset1(A_18,B_19,C_20,D_21,E_22,F_23,G_24,H_25,I_26) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1541,plain,(
    ! [A_18] : k2_xboole_0(k1_tarski(A_18),k1_tarski('#skF_3')) = k7_enumset1(A_18,'#skF_3','#skF_4','#skF_4','#skF_4','#skF_4','#skF_4','#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1353,c_66])).

tff(c_1645,plain,(
    ! [A_380] : k7_enumset1(A_380,'#skF_3','#skF_4','#skF_4','#skF_4','#skF_4','#skF_4','#skF_4','#skF_5') = k6_enumset1(A_380,'#skF_4','#skF_4','#skF_4','#skF_4','#skF_4','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1110,c_1541])).

tff(c_8,plain,(
    ! [B_6,H_12,C_7,E_9,D_8,A_5,G_11,K_17,F_10] : r2_hidden(K_17,k7_enumset1(A_5,B_6,C_7,D_8,E_9,F_10,G_11,H_12,K_17)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1678,plain,(
    ! [A_380] : r2_hidden('#skF_5',k6_enumset1(A_380,'#skF_4','#skF_4','#skF_4','#skF_4','#skF_4','#skF_4','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1645,c_8])).

tff(c_1904,plain,(
    ! [A_416,A_417] : k6_enumset1(A_416,A_417,A_417,A_417,A_417,A_417,A_417,A_417) = k2_xboole_0(k1_tarski(A_416),k1_tarski(A_417)) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_1014])).

tff(c_2057,plain,(
    ! [A_418] : k6_enumset1(A_418,A_418,A_418,A_418,A_418,A_418,A_418,A_418) = k1_tarski(A_418) ),
    inference(superposition,[status(thm),theory(equality)],[c_1904,c_313])).

tff(c_2479,plain,(
    ! [A_445,A_446] : k7_enumset1(A_445,A_446,A_446,A_446,A_446,A_446,A_446,A_446,A_446) = k2_xboole_0(k1_tarski(A_445),k1_tarski(A_446)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2057,c_66])).

tff(c_2578,plain,(
    ! [A_460] : k7_enumset1(A_460,'#skF_3','#skF_3','#skF_3','#skF_3','#skF_3','#skF_3','#skF_3','#skF_3') = k6_enumset1(A_460,'#skF_4','#skF_4','#skF_4','#skF_4','#skF_4','#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1110,c_2479])).

tff(c_6,plain,(
    ! [B_6,H_12,C_7,I_13,E_9,D_8,A_5,G_11,K_17,F_10] :
      ( K_17 = I_13
      | K_17 = H_12
      | K_17 = G_11
      | K_17 = F_10
      | K_17 = E_9
      | K_17 = D_8
      | K_17 = C_7
      | K_17 = B_6
      | K_17 = A_5
      | ~ r2_hidden(K_17,k7_enumset1(A_5,B_6,C_7,D_8,E_9,F_10,G_11,H_12,I_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_3032,plain,(
    ! [K_496,A_497] :
      ( K_496 = '#skF_3'
      | K_496 = '#skF_3'
      | K_496 = '#skF_3'
      | K_496 = '#skF_3'
      | K_496 = '#skF_3'
      | K_496 = '#skF_3'
      | K_496 = '#skF_3'
      | K_496 = '#skF_3'
      | K_496 = A_497
      | ~ r2_hidden(K_496,k6_enumset1(A_497,'#skF_4','#skF_4','#skF_4','#skF_4','#skF_4','#skF_4','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2578,c_6])).

tff(c_3084,plain,(
    ! [A_380] :
      ( '#skF_5' = '#skF_3'
      | A_380 = '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_1678,c_3032])).

tff(c_3092,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_3084])).

tff(c_84,plain,(
    '#skF_5' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_3112,plain,(
    '#skF_3' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3092,c_84])).

tff(c_18,plain,(
    ! [B_6,H_12,C_7,I_13,E_9,A_5,G_11,K_17,F_10] : r2_hidden(K_17,k7_enumset1(A_5,B_6,C_7,K_17,E_9,F_10,G_11,H_12,I_13)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1654,plain,(
    ! [A_380] : r2_hidden('#skF_4',k6_enumset1(A_380,'#skF_4','#skF_4','#skF_4','#skF_4','#skF_4','#skF_4','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1645,c_18])).

tff(c_3085,plain,(
    ! [A_380] :
      ( '#skF_3' = '#skF_4'
      | A_380 = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_1654,c_3032])).

tff(c_3119,plain,(
    ! [A_498] : A_498 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_3112,c_3085])).

tff(c_3427,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_3119,c_3112])).

tff(c_3434,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_3084])).

tff(c_3428,plain,(
    ! [A_380] : A_380 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_3084])).

tff(c_3878,plain,(
    ! [A_14902] : A_14902 = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_3434,c_3428])).

tff(c_3429,plain,(
    '#skF_5' != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_3084])).

tff(c_4356,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_3878,c_3429])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:05:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.96/2.45  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.96/2.46  
% 6.96/2.46  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.96/2.46  %$ r2_hidden > k7_enumset1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_5 > #skF_3 > #skF_1 > #skF_4
% 6.96/2.46  
% 6.96/2.46  %Foreground sorts:
% 6.96/2.46  
% 6.96/2.46  
% 6.96/2.46  %Background operators:
% 6.96/2.46  
% 6.96/2.46  
% 6.96/2.46  %Foreground operators:
% 6.96/2.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.96/2.46  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.96/2.46  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.96/2.46  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.96/2.46  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 6.96/2.46  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.96/2.46  tff(k7_enumset1, type, k7_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 6.96/2.46  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 6.96/2.46  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.96/2.46  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.96/2.46  tff('#skF_5', type, '#skF_5': $i).
% 6.96/2.46  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.96/2.46  tff('#skF_3', type, '#skF_3': $i).
% 6.96/2.46  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.96/2.46  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 6.96/2.46  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 6.96/2.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.96/2.46  tff('#skF_4', type, '#skF_4': $i).
% 6.96/2.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.96/2.46  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.96/2.46  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.96/2.46  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 6.96/2.46  
% 6.96/2.48  tff(f_85, negated_conjecture, ~(![A, B, C]: ((k1_tarski(A) = k2_tarski(B, C)) => (B = C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_zfmisc_1)).
% 6.96/2.48  tff(f_70, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 6.96/2.48  tff(f_72, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 6.96/2.48  tff(f_74, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 6.96/2.48  tff(f_76, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 6.96/2.48  tff(f_78, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 6.96/2.48  tff(f_66, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k1_tarski(A), k5_enumset1(B, C, D, E, F, G, H)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_enumset1)).
% 6.96/2.48  tff(f_68, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 6.96/2.48  tff(f_80, axiom, (![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 6.96/2.48  tff(f_64, axiom, (![A, B, C, D, E, F, G, H, I]: (k7_enumset1(A, B, C, D, E, F, G, H, I) = k2_xboole_0(k1_tarski(A), k6_enumset1(B, C, D, E, F, G, H, I)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t127_enumset1)).
% 6.96/2.48  tff(f_62, axiom, (![A, B, C, D, E, F, G, H, I, J]: ((J = k7_enumset1(A, B, C, D, E, F, G, H, I)) <=> (![K]: (r2_hidden(K, J) <=> ~((((((((~(K = A) & ~(K = B)) & ~(K = C)) & ~(K = D)) & ~(K = E)) & ~(K = F)) & ~(K = G)) & ~(K = H)) & ~(K = I)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_enumset1)).
% 6.96/2.48  tff(c_86, plain, (k2_tarski('#skF_4', '#skF_5')=k1_tarski('#skF_3')), inference(cnfTransformation, [status(thm)], [f_85])).
% 6.96/2.48  tff(c_72, plain, (![A_36, B_37]: (k1_enumset1(A_36, A_36, B_37)=k2_tarski(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.96/2.48  tff(c_74, plain, (![A_38, B_39, C_40]: (k2_enumset1(A_38, A_38, B_39, C_40)=k1_enumset1(A_38, B_39, C_40))), inference(cnfTransformation, [status(thm)], [f_72])).
% 6.96/2.48  tff(c_76, plain, (![A_41, B_42, C_43, D_44]: (k3_enumset1(A_41, A_41, B_42, C_43, D_44)=k2_enumset1(A_41, B_42, C_43, D_44))), inference(cnfTransformation, [status(thm)], [f_74])).
% 6.96/2.48  tff(c_78, plain, (![D_48, C_47, A_45, B_46, E_49]: (k4_enumset1(A_45, A_45, B_46, C_47, D_48, E_49)=k3_enumset1(A_45, B_46, C_47, D_48, E_49))), inference(cnfTransformation, [status(thm)], [f_76])).
% 6.96/2.48  tff(c_80, plain, (![A_50, B_51, E_54, C_52, D_53, F_55]: (k5_enumset1(A_50, A_50, B_51, C_52, D_53, E_54, F_55)=k4_enumset1(A_50, B_51, C_52, D_53, E_54, F_55))), inference(cnfTransformation, [status(thm)], [f_78])).
% 6.96/2.48  tff(c_181, plain, (![D_179, C_177, G_182, F_176, E_180, H_178, A_183, B_181]: (k2_xboole_0(k1_tarski(A_183), k5_enumset1(B_181, C_177, D_179, E_180, F_176, G_182, H_178))=k6_enumset1(A_183, B_181, C_177, D_179, E_180, F_176, G_182, H_178))), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.96/2.48  tff(c_193, plain, (![C_187, B_188, A_185, E_184, F_189, A_186, D_190]: (k6_enumset1(A_186, A_185, A_185, B_188, C_187, D_190, E_184, F_189)=k2_xboole_0(k1_tarski(A_186), k4_enumset1(A_185, B_188, C_187, D_190, E_184, F_189)))), inference(superposition, [status(thm), theory('equality')], [c_80, c_181])).
% 6.96/2.48  tff(c_360, plain, (![A_228, C_230, B_227, A_232, D_229, E_231]: (k6_enumset1(A_232, A_228, A_228, A_228, B_227, C_230, D_229, E_231)=k2_xboole_0(k1_tarski(A_232), k3_enumset1(A_228, B_227, C_230, D_229, E_231)))), inference(superposition, [status(thm), theory('equality')], [c_78, c_193])).
% 6.96/2.48  tff(c_535, plain, (![A_263, B_267, A_266, D_265, C_264]: (k6_enumset1(A_266, A_263, A_263, A_263, A_263, B_267, C_264, D_265)=k2_xboole_0(k1_tarski(A_266), k2_enumset1(A_263, B_267, C_264, D_265)))), inference(superposition, [status(thm), theory('equality')], [c_76, c_360])).
% 6.96/2.48  tff(c_734, plain, (![A_290, A_291, B_292, C_293]: (k6_enumset1(A_290, A_291, A_291, A_291, A_291, A_291, B_292, C_293)=k2_xboole_0(k1_tarski(A_290), k1_enumset1(A_291, B_292, C_293)))), inference(superposition, [status(thm), theory('equality')], [c_74, c_535])).
% 6.96/2.48  tff(c_1014, plain, (![A_336, A_337, B_338]: (k6_enumset1(A_336, A_337, A_337, A_337, A_337, A_337, A_337, B_338)=k2_xboole_0(k1_tarski(A_336), k2_tarski(A_337, B_338)))), inference(superposition, [status(thm), theory('equality')], [c_72, c_734])).
% 6.96/2.48  tff(c_1110, plain, (![A_336]: (k2_xboole_0(k1_tarski(A_336), k1_tarski('#skF_3'))=k6_enumset1(A_336, '#skF_4', '#skF_4', '#skF_4', '#skF_4', '#skF_4', '#skF_4', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_86, c_1014])).
% 6.96/2.48  tff(c_70, plain, (![A_35]: (k2_tarski(A_35, A_35)=k1_tarski(A_35))), inference(cnfTransformation, [status(thm)], [f_68])).
% 6.96/2.48  tff(c_82, plain, (![D_59, A_56, B_57, G_62, F_61, C_58, E_60]: (k6_enumset1(A_56, A_56, B_57, C_58, D_59, E_60, F_61, G_62)=k5_enumset1(A_56, B_57, C_58, D_59, E_60, F_61, G_62))), inference(cnfTransformation, [status(thm)], [f_80])).
% 6.96/2.48  tff(c_203, plain, (![C_187, B_188, A_185, E_184, F_189, D_190]: (k2_xboole_0(k1_tarski(A_185), k4_enumset1(A_185, B_188, C_187, D_190, E_184, F_189))=k5_enumset1(A_185, A_185, B_188, C_187, D_190, E_184, F_189))), inference(superposition, [status(thm), theory('equality')], [c_193, c_82])).
% 6.96/2.48  tff(c_223, plain, (![A_191, B_192, C_195, D_194, E_196, F_193]: (k2_xboole_0(k1_tarski(A_191), k4_enumset1(A_191, B_192, C_195, D_194, E_196, F_193))=k4_enumset1(A_191, B_192, C_195, D_194, E_196, F_193))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_203])).
% 6.96/2.48  tff(c_239, plain, (![D_48, C_47, A_45, B_46, E_49]: (k2_xboole_0(k1_tarski(A_45), k3_enumset1(A_45, B_46, C_47, D_48, E_49))=k4_enumset1(A_45, A_45, B_46, C_47, D_48, E_49))), inference(superposition, [status(thm), theory('equality')], [c_78, c_223])).
% 6.96/2.48  tff(c_243, plain, (![C_200, E_201, D_199, A_198, B_197]: (k2_xboole_0(k1_tarski(A_198), k3_enumset1(A_198, B_197, C_200, D_199, E_201))=k3_enumset1(A_198, B_197, C_200, D_199, E_201))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_239])).
% 6.96/2.48  tff(c_252, plain, (![A_41, B_42, C_43, D_44]: (k2_xboole_0(k1_tarski(A_41), k2_enumset1(A_41, B_42, C_43, D_44))=k3_enumset1(A_41, A_41, B_42, C_43, D_44))), inference(superposition, [status(thm), theory('equality')], [c_76, c_243])).
% 6.96/2.48  tff(c_256, plain, (![A_202, B_203, C_204, D_205]: (k2_xboole_0(k1_tarski(A_202), k2_enumset1(A_202, B_203, C_204, D_205))=k2_enumset1(A_202, B_203, C_204, D_205))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_252])).
% 6.96/2.48  tff(c_265, plain, (![A_38, B_39, C_40]: (k2_xboole_0(k1_tarski(A_38), k1_enumset1(A_38, B_39, C_40))=k2_enumset1(A_38, A_38, B_39, C_40))), inference(superposition, [status(thm), theory('equality')], [c_74, c_256])).
% 6.96/2.48  tff(c_285, plain, (![A_215, B_216, C_217]: (k2_xboole_0(k1_tarski(A_215), k1_enumset1(A_215, B_216, C_217))=k1_enumset1(A_215, B_216, C_217))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_265])).
% 6.96/2.48  tff(c_294, plain, (![A_36, B_37]: (k2_xboole_0(k1_tarski(A_36), k2_tarski(A_36, B_37))=k1_enumset1(A_36, A_36, B_37))), inference(superposition, [status(thm), theory('equality')], [c_72, c_285])).
% 6.96/2.48  tff(c_298, plain, (![A_218, B_219]: (k2_xboole_0(k1_tarski(A_218), k2_tarski(A_218, B_219))=k2_tarski(A_218, B_219))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_294])).
% 6.96/2.48  tff(c_307, plain, (![A_35]: (k2_xboole_0(k1_tarski(A_35), k1_tarski(A_35))=k2_tarski(A_35, A_35))), inference(superposition, [status(thm), theory('equality')], [c_70, c_298])).
% 6.96/2.48  tff(c_313, plain, (![A_35]: (k2_xboole_0(k1_tarski(A_35), k1_tarski(A_35))=k1_tarski(A_35))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_307])).
% 6.96/2.48  tff(c_1333, plain, (![A_357]: (k2_xboole_0(k1_tarski(A_357), k1_tarski('#skF_3'))=k6_enumset1(A_357, '#skF_4', '#skF_4', '#skF_4', '#skF_4', '#skF_4', '#skF_4', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_86, c_1014])).
% 6.96/2.48  tff(c_1353, plain, (k6_enumset1('#skF_3', '#skF_4', '#skF_4', '#skF_4', '#skF_4', '#skF_4', '#skF_4', '#skF_5')=k1_tarski('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_313, c_1333])).
% 6.96/2.48  tff(c_66, plain, (![H_25, E_22, G_24, D_21, F_23, A_18, C_20, B_19, I_26]: (k2_xboole_0(k1_tarski(A_18), k6_enumset1(B_19, C_20, D_21, E_22, F_23, G_24, H_25, I_26))=k7_enumset1(A_18, B_19, C_20, D_21, E_22, F_23, G_24, H_25, I_26))), inference(cnfTransformation, [status(thm)], [f_64])).
% 6.96/2.48  tff(c_1541, plain, (![A_18]: (k2_xboole_0(k1_tarski(A_18), k1_tarski('#skF_3'))=k7_enumset1(A_18, '#skF_3', '#skF_4', '#skF_4', '#skF_4', '#skF_4', '#skF_4', '#skF_4', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1353, c_66])).
% 6.96/2.48  tff(c_1645, plain, (![A_380]: (k7_enumset1(A_380, '#skF_3', '#skF_4', '#skF_4', '#skF_4', '#skF_4', '#skF_4', '#skF_4', '#skF_5')=k6_enumset1(A_380, '#skF_4', '#skF_4', '#skF_4', '#skF_4', '#skF_4', '#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_1110, c_1541])).
% 6.96/2.48  tff(c_8, plain, (![B_6, H_12, C_7, E_9, D_8, A_5, G_11, K_17, F_10]: (r2_hidden(K_17, k7_enumset1(A_5, B_6, C_7, D_8, E_9, F_10, G_11, H_12, K_17)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 6.96/2.48  tff(c_1678, plain, (![A_380]: (r2_hidden('#skF_5', k6_enumset1(A_380, '#skF_4', '#skF_4', '#skF_4', '#skF_4', '#skF_4', '#skF_4', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_1645, c_8])).
% 6.96/2.48  tff(c_1904, plain, (![A_416, A_417]: (k6_enumset1(A_416, A_417, A_417, A_417, A_417, A_417, A_417, A_417)=k2_xboole_0(k1_tarski(A_416), k1_tarski(A_417)))), inference(superposition, [status(thm), theory('equality')], [c_70, c_1014])).
% 6.96/2.48  tff(c_2057, plain, (![A_418]: (k6_enumset1(A_418, A_418, A_418, A_418, A_418, A_418, A_418, A_418)=k1_tarski(A_418))), inference(superposition, [status(thm), theory('equality')], [c_1904, c_313])).
% 6.96/2.48  tff(c_2479, plain, (![A_445, A_446]: (k7_enumset1(A_445, A_446, A_446, A_446, A_446, A_446, A_446, A_446, A_446)=k2_xboole_0(k1_tarski(A_445), k1_tarski(A_446)))), inference(superposition, [status(thm), theory('equality')], [c_2057, c_66])).
% 6.96/2.48  tff(c_2578, plain, (![A_460]: (k7_enumset1(A_460, '#skF_3', '#skF_3', '#skF_3', '#skF_3', '#skF_3', '#skF_3', '#skF_3', '#skF_3')=k6_enumset1(A_460, '#skF_4', '#skF_4', '#skF_4', '#skF_4', '#skF_4', '#skF_4', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1110, c_2479])).
% 6.96/2.48  tff(c_6, plain, (![B_6, H_12, C_7, I_13, E_9, D_8, A_5, G_11, K_17, F_10]: (K_17=I_13 | K_17=H_12 | K_17=G_11 | K_17=F_10 | K_17=E_9 | K_17=D_8 | K_17=C_7 | K_17=B_6 | K_17=A_5 | ~r2_hidden(K_17, k7_enumset1(A_5, B_6, C_7, D_8, E_9, F_10, G_11, H_12, I_13)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 6.96/2.48  tff(c_3032, plain, (![K_496, A_497]: (K_496='#skF_3' | K_496='#skF_3' | K_496='#skF_3' | K_496='#skF_3' | K_496='#skF_3' | K_496='#skF_3' | K_496='#skF_3' | K_496='#skF_3' | K_496=A_497 | ~r2_hidden(K_496, k6_enumset1(A_497, '#skF_4', '#skF_4', '#skF_4', '#skF_4', '#skF_4', '#skF_4', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_2578, c_6])).
% 6.96/2.48  tff(c_3084, plain, (![A_380]: ('#skF_5'='#skF_3' | A_380='#skF_5')), inference(resolution, [status(thm)], [c_1678, c_3032])).
% 6.96/2.48  tff(c_3092, plain, ('#skF_5'='#skF_3'), inference(splitLeft, [status(thm)], [c_3084])).
% 6.96/2.48  tff(c_84, plain, ('#skF_5'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_85])).
% 6.96/2.48  tff(c_3112, plain, ('#skF_3'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3092, c_84])).
% 6.96/2.48  tff(c_18, plain, (![B_6, H_12, C_7, I_13, E_9, A_5, G_11, K_17, F_10]: (r2_hidden(K_17, k7_enumset1(A_5, B_6, C_7, K_17, E_9, F_10, G_11, H_12, I_13)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 6.96/2.48  tff(c_1654, plain, (![A_380]: (r2_hidden('#skF_4', k6_enumset1(A_380, '#skF_4', '#skF_4', '#skF_4', '#skF_4', '#skF_4', '#skF_4', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_1645, c_18])).
% 6.96/2.48  tff(c_3085, plain, (![A_380]: ('#skF_3'='#skF_4' | A_380='#skF_4')), inference(resolution, [status(thm)], [c_1654, c_3032])).
% 6.96/2.48  tff(c_3119, plain, (![A_498]: (A_498='#skF_4')), inference(negUnitSimplification, [status(thm)], [c_3112, c_3085])).
% 6.96/2.48  tff(c_3427, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_3119, c_3112])).
% 6.96/2.48  tff(c_3434, plain, ('#skF_5'='#skF_3'), inference(splitRight, [status(thm)], [c_3084])).
% 6.96/2.48  tff(c_3428, plain, (![A_380]: (A_380='#skF_5')), inference(splitRight, [status(thm)], [c_3084])).
% 6.96/2.48  tff(c_3878, plain, (![A_14902]: (A_14902='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3434, c_3428])).
% 6.96/2.48  tff(c_3429, plain, ('#skF_5'!='#skF_3'), inference(splitRight, [status(thm)], [c_3084])).
% 6.96/2.48  tff(c_4356, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_3878, c_3429])).
% 6.96/2.48  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.96/2.48  
% 6.96/2.48  Inference rules
% 6.96/2.48  ----------------------
% 6.96/2.48  #Ref     : 0
% 6.96/2.48  #Sup     : 1269
% 6.96/2.48  #Fact    : 0
% 6.96/2.48  #Define  : 0
% 6.96/2.48  #Split   : 1
% 6.96/2.48  #Chain   : 0
% 6.96/2.48  #Close   : 0
% 6.96/2.48  
% 6.96/2.48  Ordering : KBO
% 6.96/2.48  
% 6.96/2.48  Simplification rules
% 6.96/2.48  ----------------------
% 6.96/2.48  #Subsume      : 88
% 6.96/2.48  #Demod        : 916
% 6.96/2.48  #Tautology    : 591
% 6.96/2.48  #SimpNegUnit  : 1
% 6.96/2.48  #BackRed      : 20
% 6.96/2.48  
% 6.96/2.48  #Partial instantiations: 326
% 6.96/2.48  #Strategies tried      : 1
% 6.96/2.48  
% 6.96/2.48  Timing (in seconds)
% 6.96/2.48  ----------------------
% 6.96/2.48  Preprocessing        : 0.43
% 6.96/2.48  Parsing              : 0.19
% 6.96/2.49  CNF conversion       : 0.03
% 6.96/2.49  Main loop            : 1.20
% 6.96/2.49  Inferencing          : 0.51
% 6.96/2.49  Reduction            : 0.39
% 6.96/2.49  Demodulation         : 0.32
% 6.96/2.49  BG Simplification    : 0.05
% 6.96/2.49  Subsumption          : 0.20
% 6.96/2.49  Abstraction          : 0.08
% 6.96/2.49  MUC search           : 0.00
% 6.96/2.49  Cooper               : 0.00
% 6.96/2.49  Total                : 1.68
% 6.96/2.49  Index Insertion      : 0.00
% 6.96/2.49  Index Deletion       : 0.00
% 6.96/2.49  Index Matching       : 0.00
% 6.96/2.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
