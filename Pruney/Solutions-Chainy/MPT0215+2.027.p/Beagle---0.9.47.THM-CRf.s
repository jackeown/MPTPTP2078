%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:42 EST 2020

% Result     : Theorem 6.93s
% Output     : CNFRefutation 6.93s
% Verified   : 
% Statistics : Number of formulae       :  139 (7930 expanded)
%              Number of leaves         :   33 (2640 expanded)
%              Depth                    :   37
%              Number of atoms          :  228 (9630 expanded)
%              Number of equality atoms :  206 (9448 expanded)
%              Maximal formula depth    :   24 (   6 average)
%              Maximal term depth       :    3 (   1 average)

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
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_zfmisc_1)).

tff(f_66,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k5_enumset1(A,B,C,D,E,F,G),k1_tarski(H)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_enumset1)).

tff(f_80,axiom,(
    ! [A,B,C,D,E,F,G] : k6_enumset1(A,A,B,C,D,E,F,G) = k5_enumset1(A,B,C,D,E,F,G) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

tff(f_78,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_76,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_74,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_72,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_70,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_68,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_64,axiom,(
    ! [A,B,C,D,E,F,G,H,I] : k7_enumset1(A,B,C,D,E,F,G,H,I) = k2_xboole_0(k6_enumset1(A,B,C,D,E,F,G,H),k1_tarski(I)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_enumset1)).

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

tff(c_84,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_68,plain,(
    ! [C_29,D_30,B_28,G_33,F_32,A_27,E_31,H_34] : k2_xboole_0(k5_enumset1(A_27,B_28,C_29,D_30,E_31,F_32,G_33),k1_tarski(H_34)) = k6_enumset1(A_27,B_28,C_29,D_30,E_31,F_32,G_33,H_34) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_82,plain,(
    ! [D_59,A_56,B_57,G_62,F_61,C_58,E_60] : k6_enumset1(A_56,A_56,B_57,C_58,D_59,E_60,F_61,G_62) = k5_enumset1(A_56,B_57,C_58,D_59,E_60,F_61,G_62) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_80,plain,(
    ! [A_50,B_51,E_54,C_52,D_53,F_55] : k5_enumset1(A_50,A_50,B_51,C_52,D_53,E_54,F_55) = k4_enumset1(A_50,B_51,C_52,D_53,E_54,F_55) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_181,plain,(
    ! [D_179,C_177,G_182,F_176,E_180,H_178,A_183,B_181] : k2_xboole_0(k5_enumset1(A_183,B_181,C_177,D_179,E_180,F_176,G_182),k1_tarski(H_178)) = k6_enumset1(A_183,B_181,C_177,D_179,E_180,F_176,G_182,H_178) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_190,plain,(
    ! [A_50,B_51,E_54,C_52,D_53,F_55,H_178] : k6_enumset1(A_50,A_50,B_51,C_52,D_53,E_54,F_55,H_178) = k2_xboole_0(k4_enumset1(A_50,B_51,C_52,D_53,E_54,F_55),k1_tarski(H_178)) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_181])).

tff(c_193,plain,(
    ! [A_50,B_51,E_54,C_52,D_53,F_55,H_178] : k2_xboole_0(k4_enumset1(A_50,B_51,C_52,D_53,E_54,F_55),k1_tarski(H_178)) = k5_enumset1(A_50,B_51,C_52,D_53,E_54,F_55,H_178) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_190])).

tff(c_78,plain,(
    ! [D_48,C_47,A_45,B_46,E_49] : k4_enumset1(A_45,A_45,B_46,C_47,D_48,E_49) = k3_enumset1(A_45,B_46,C_47,D_48,E_49) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_194,plain,(
    ! [C_187,H_186,B_188,A_185,E_184,F_189,D_190] : k2_xboole_0(k4_enumset1(A_185,B_188,C_187,D_190,E_184,F_189),k1_tarski(H_186)) = k5_enumset1(A_185,B_188,C_187,D_190,E_184,F_189,H_186) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_190])).

tff(c_203,plain,(
    ! [H_186,D_48,C_47,A_45,B_46,E_49] : k5_enumset1(A_45,A_45,B_46,C_47,D_48,E_49,H_186) = k2_xboole_0(k3_enumset1(A_45,B_46,C_47,D_48,E_49),k1_tarski(H_186)) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_194])).

tff(c_206,plain,(
    ! [H_186,D_48,C_47,A_45,B_46,E_49] : k2_xboole_0(k3_enumset1(A_45,B_46,C_47,D_48,E_49),k1_tarski(H_186)) = k4_enumset1(A_45,B_46,C_47,D_48,E_49,H_186) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_203])).

tff(c_76,plain,(
    ! [A_41,B_42,C_43,D_44] : k3_enumset1(A_41,A_41,B_42,C_43,D_44) = k2_enumset1(A_41,B_42,C_43,D_44) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_207,plain,(
    ! [B_192,C_195,A_193,D_194,H_191,E_196] : k2_xboole_0(k3_enumset1(A_193,B_192,C_195,D_194,E_196),k1_tarski(H_191)) = k4_enumset1(A_193,B_192,C_195,D_194,E_196,H_191) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_203])).

tff(c_216,plain,(
    ! [D_44,C_43,A_41,H_191,B_42] : k4_enumset1(A_41,A_41,B_42,C_43,D_44,H_191) = k2_xboole_0(k2_enumset1(A_41,B_42,C_43,D_44),k1_tarski(H_191)) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_207])).

tff(c_219,plain,(
    ! [D_44,C_43,A_41,H_191,B_42] : k2_xboole_0(k2_enumset1(A_41,B_42,C_43,D_44),k1_tarski(H_191)) = k3_enumset1(A_41,B_42,C_43,D_44,H_191) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_216])).

tff(c_74,plain,(
    ! [A_38,B_39,C_40] : k2_enumset1(A_38,A_38,B_39,C_40) = k1_enumset1(A_38,B_39,C_40) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_220,plain,(
    ! [H_197,C_199,A_198,D_200,B_201] : k2_xboole_0(k2_enumset1(A_198,B_201,C_199,D_200),k1_tarski(H_197)) = k3_enumset1(A_198,B_201,C_199,D_200,H_197) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_216])).

tff(c_229,plain,(
    ! [A_38,B_39,C_40,H_197] : k3_enumset1(A_38,A_38,B_39,C_40,H_197) = k2_xboole_0(k1_enumset1(A_38,B_39,C_40),k1_tarski(H_197)) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_220])).

tff(c_232,plain,(
    ! [A_38,B_39,C_40,H_197] : k2_xboole_0(k1_enumset1(A_38,B_39,C_40),k1_tarski(H_197)) = k2_enumset1(A_38,B_39,C_40,H_197) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_229])).

tff(c_72,plain,(
    ! [A_36,B_37] : k1_enumset1(A_36,A_36,B_37) = k2_tarski(A_36,B_37) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_233,plain,(
    ! [A_202,B_203,C_204,H_205] : k2_xboole_0(k1_enumset1(A_202,B_203,C_204),k1_tarski(H_205)) = k2_enumset1(A_202,B_203,C_204,H_205) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_229])).

tff(c_242,plain,(
    ! [A_36,B_37,H_205] : k2_xboole_0(k2_tarski(A_36,B_37),k1_tarski(H_205)) = k2_enumset1(A_36,A_36,B_37,H_205) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_233])).

tff(c_245,plain,(
    ! [A_36,B_37,H_205] : k2_xboole_0(k2_tarski(A_36,B_37),k1_tarski(H_205)) = k1_enumset1(A_36,B_37,H_205) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_242])).

tff(c_70,plain,(
    ! [A_35] : k2_tarski(A_35,A_35) = k1_tarski(A_35) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_259,plain,(
    ! [A_215,B_216,H_217] : k2_xboole_0(k2_tarski(A_215,B_216),k1_tarski(H_217)) = k1_enumset1(A_215,B_216,H_217) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_242])).

tff(c_268,plain,(
    ! [A_35,H_217] : k2_xboole_0(k1_tarski(A_35),k1_tarski(H_217)) = k1_enumset1(A_35,A_35,H_217) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_259])).

tff(c_274,plain,(
    ! [A_35,H_217] : k2_xboole_0(k1_tarski(A_35),k1_tarski(H_217)) = k2_tarski(A_35,H_217) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_268])).

tff(c_86,plain,(
    k2_tarski('#skF_4','#skF_5') = k1_tarski('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_271,plain,(
    ! [H_217] : k2_xboole_0(k1_tarski('#skF_3'),k1_tarski(H_217)) = k1_enumset1('#skF_4','#skF_5',H_217) ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_259])).

tff(c_285,plain,(
    ! [H_220] : k1_enumset1('#skF_4','#skF_5',H_220) = k2_tarski('#skF_3',H_220) ),
    inference(demodulation,[status(thm),theory(equality)],[c_274,c_271])).

tff(c_291,plain,(
    ! [H_220,H_197] : k2_xboole_0(k2_tarski('#skF_3',H_220),k1_tarski(H_197)) = k2_enumset1('#skF_4','#skF_5',H_220,H_197) ),
    inference(superposition,[status(thm),theory(equality)],[c_285,c_232])).

tff(c_298,plain,(
    ! [H_221,H_222] : k2_enumset1('#skF_4','#skF_5',H_221,H_222) = k1_enumset1('#skF_3',H_221,H_222) ),
    inference(demodulation,[status(thm),theory(equality)],[c_245,c_291])).

tff(c_304,plain,(
    ! [H_221,H_222,H_191] : k2_xboole_0(k1_enumset1('#skF_3',H_221,H_222),k1_tarski(H_191)) = k3_enumset1('#skF_4','#skF_5',H_221,H_222,H_191) ),
    inference(superposition,[status(thm),theory(equality)],[c_298,c_219])).

tff(c_311,plain,(
    ! [H_223,H_224,H_225] : k3_enumset1('#skF_4','#skF_5',H_223,H_224,H_225) = k2_enumset1('#skF_3',H_223,H_224,H_225) ),
    inference(demodulation,[status(thm),theory(equality)],[c_232,c_304])).

tff(c_317,plain,(
    ! [H_223,H_224,H_225,H_186] : k2_xboole_0(k2_enumset1('#skF_3',H_223,H_224,H_225),k1_tarski(H_186)) = k4_enumset1('#skF_4','#skF_5',H_223,H_224,H_225,H_186) ),
    inference(superposition,[status(thm),theory(equality)],[c_311,c_206])).

tff(c_324,plain,(
    ! [H_226,H_227,H_228,H_229] : k4_enumset1('#skF_4','#skF_5',H_226,H_227,H_228,H_229) = k3_enumset1('#skF_3',H_226,H_227,H_228,H_229) ),
    inference(demodulation,[status(thm),theory(equality)],[c_219,c_317])).

tff(c_330,plain,(
    ! [H_228,H_226,H_227,H_178,H_229] : k2_xboole_0(k3_enumset1('#skF_3',H_226,H_227,H_228,H_229),k1_tarski(H_178)) = k5_enumset1('#skF_4','#skF_5',H_226,H_227,H_228,H_229,H_178) ),
    inference(superposition,[status(thm),theory(equality)],[c_324,c_193])).

tff(c_337,plain,(
    ! [H_230,H_233,H_231,H_234,H_232] : k5_enumset1('#skF_4','#skF_5',H_233,H_232,H_234,H_230,H_231) = k4_enumset1('#skF_3',H_233,H_232,H_234,H_230,H_231) ),
    inference(demodulation,[status(thm),theory(equality)],[c_206,c_330])).

tff(c_343,plain,(
    ! [H_230,H_233,H_231,H_234,H_232,H_34] : k2_xboole_0(k4_enumset1('#skF_3',H_233,H_232,H_234,H_230,H_231),k1_tarski(H_34)) = k6_enumset1('#skF_4','#skF_5',H_233,H_232,H_234,H_230,H_231,H_34) ),
    inference(superposition,[status(thm),theory(equality)],[c_337,c_68])).

tff(c_350,plain,(
    ! [H_236,H_239,H_237,H_240,H_238,H_235] : k6_enumset1('#skF_4','#skF_5',H_236,H_240,H_239,H_238,H_235,H_237) = k5_enumset1('#skF_3',H_236,H_240,H_239,H_238,H_235,H_237) ),
    inference(demodulation,[status(thm),theory(equality)],[c_193,c_343])).

tff(c_66,plain,(
    ! [H_25,E_22,G_24,D_21,F_23,A_18,C_20,B_19,I_26] : k2_xboole_0(k6_enumset1(A_18,B_19,C_20,D_21,E_22,F_23,G_24,H_25),k1_tarski(I_26)) = k7_enumset1(A_18,B_19,C_20,D_21,E_22,F_23,G_24,H_25,I_26) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_356,plain,(
    ! [H_236,H_239,H_237,H_240,H_238,H_235,I_26] : k2_xboole_0(k5_enumset1('#skF_3',H_236,H_240,H_239,H_238,H_235,H_237),k1_tarski(I_26)) = k7_enumset1('#skF_4','#skF_5',H_236,H_240,H_239,H_238,H_235,H_237,I_26) ),
    inference(superposition,[status(thm),theory(equality)],[c_350,c_66])).

tff(c_821,plain,(
    ! [H_594,H_595,H_593,H_598,H_596,I_597,H_592] : k7_enumset1('#skF_4','#skF_5',H_595,H_596,H_594,H_593,H_592,H_598,I_597) = k6_enumset1('#skF_3',H_595,H_596,H_594,H_593,H_592,H_598,I_597) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_356])).

tff(c_24,plain,(
    ! [B_6,H_12,C_7,I_13,E_9,D_8,G_11,K_17,F_10] : r2_hidden(K_17,k7_enumset1(K_17,B_6,C_7,D_8,E_9,F_10,G_11,H_12,I_13)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_851,plain,(
    ! [H_594,H_595,H_593,H_598,H_596,I_597,H_592] : r2_hidden('#skF_4',k6_enumset1('#skF_3',H_595,H_596,H_594,H_593,H_592,H_598,I_597)) ),
    inference(superposition,[status(thm),theory(equality)],[c_821,c_24])).

tff(c_246,plain,(
    ! [A_206,D_212,I_208,G_214,E_209,C_207,H_210,B_213,F_211] : k2_xboole_0(k6_enumset1(A_206,B_213,C_207,D_212,E_209,F_211,G_214,H_210),k1_tarski(I_208)) = k7_enumset1(A_206,B_213,C_207,D_212,E_209,F_211,G_214,H_210,I_208) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_255,plain,(
    ! [D_59,I_208,A_56,B_57,G_62,F_61,C_58,E_60] : k7_enumset1(A_56,A_56,B_57,C_58,D_59,E_60,F_61,G_62,I_208) = k2_xboole_0(k5_enumset1(A_56,B_57,C_58,D_59,E_60,F_61,G_62),k1_tarski(I_208)) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_246])).

tff(c_258,plain,(
    ! [D_59,I_208,A_56,B_57,G_62,F_61,C_58,E_60] : k7_enumset1(A_56,A_56,B_57,C_58,D_59,E_60,F_61,G_62,I_208) = k6_enumset1(A_56,B_57,C_58,D_59,E_60,F_61,G_62,I_208) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_255])).

tff(c_399,plain,(
    ! [I_250,G_252,D_249,A_255,K_256,F_251,E_258,B_253,H_257,C_254] :
      ( K_256 = I_250
      | K_256 = H_257
      | K_256 = G_252
      | K_256 = F_251
      | K_256 = E_258
      | K_256 = D_249
      | K_256 = C_254
      | K_256 = B_253
      | K_256 = A_255
      | ~ r2_hidden(K_256,k7_enumset1(A_255,B_253,C_254,D_249,E_258,F_251,G_252,H_257,I_250)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1560,plain,(
    ! [A_715,E_713,K_712,F_709,I_707,C_711,D_714,G_710,B_708] :
      ( K_712 = I_707
      | K_712 = G_710
      | K_712 = F_709
      | K_712 = E_713
      | K_712 = D_714
      | K_712 = C_711
      | K_712 = B_708
      | K_712 = A_715
      | K_712 = A_715
      | ~ r2_hidden(K_712,k6_enumset1(A_715,B_708,C_711,D_714,E_713,F_709,G_710,I_707)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_258,c_399])).

tff(c_1570,plain,(
    ! [H_594,H_595,H_593,H_598,H_596,I_597,H_592] :
      ( I_597 = '#skF_4'
      | H_598 = '#skF_4'
      | H_592 = '#skF_4'
      | H_593 = '#skF_4'
      | H_594 = '#skF_4'
      | H_596 = '#skF_4'
      | H_595 = '#skF_4'
      | '#skF_3' = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_851,c_1560])).

tff(c_1601,plain,(
    ! [H_594,H_595,H_593,H_598,H_596,I_597,H_592] :
      ( I_597 = '#skF_4'
      | H_598 = '#skF_4'
      | H_592 = '#skF_4'
      | H_593 = '#skF_4'
      | H_594 = '#skF_4'
      | H_596 = '#skF_4'
      | H_595 = '#skF_4' ) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_84,c_1570])).

tff(c_1619,plain,(
    ! [H_716] : H_716 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_1601])).

tff(c_363,plain,(
    ! [C_245,F_243,I_241,D_247,A_248,B_242,E_246,G_244] : k7_enumset1(A_248,A_248,B_242,C_245,D_247,E_246,F_243,G_244,I_241) = k6_enumset1(A_248,B_242,C_245,D_247,E_246,F_243,G_244,I_241) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_255])).

tff(c_390,plain,(
    ! [C_245,F_243,I_241,D_247,A_248,B_242,E_246,G_244] : r2_hidden(A_248,k6_enumset1(A_248,B_242,C_245,D_247,E_246,F_243,G_244,I_241)) ),
    inference(superposition,[status(thm),theory(equality)],[c_363,c_24])).

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

tff(c_879,plain,(
    ! [H_617,I_618,H_620,H_616,H_615,K_619,H_613,H_614] :
      ( K_619 = I_618
      | K_619 = H_614
      | K_619 = H_615
      | K_619 = H_616
      | K_619 = H_617
      | K_619 = H_613
      | K_619 = H_620
      | K_619 = '#skF_5'
      | K_619 = '#skF_4'
      | ~ r2_hidden(K_619,k6_enumset1('#skF_3',H_620,H_613,H_617,H_616,H_615,H_614,I_618)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_821,c_6])).

tff(c_913,plain,(
    ! [C_245,F_243,I_241,D_247,B_242,E_246,G_244] :
      ( I_241 = '#skF_3'
      | G_244 = '#skF_3'
      | F_243 = '#skF_3'
      | E_246 = '#skF_3'
      | D_247 = '#skF_3'
      | C_245 = '#skF_3'
      | B_242 = '#skF_3'
      | '#skF_5' = '#skF_3'
      | '#skF_3' = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_390,c_879])).

tff(c_940,plain,(
    ! [C_245,F_243,I_241,D_247,B_242,E_246,G_244] :
      ( I_241 = '#skF_3'
      | G_244 = '#skF_3'
      | F_243 = '#skF_3'
      | E_246 = '#skF_3'
      | D_247 = '#skF_3'
      | C_245 = '#skF_3'
      | B_242 = '#skF_3'
      | '#skF_5' = '#skF_3' ) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_913])).

tff(c_943,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_940])).

tff(c_1661,plain,(
    '#skF_3' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_1619,c_943])).

tff(c_1885,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_1661])).

tff(c_1886,plain,(
    ! [H_594,H_593,H_598,H_596,I_597,H_592] :
      ( H_594 = '#skF_4'
      | H_592 = '#skF_4'
      | I_597 = '#skF_4'
      | H_598 = '#skF_4'
      | H_593 = '#skF_4'
      | H_596 = '#skF_4' ) ),
    inference(splitRight,[status(thm)],[c_1601])).

tff(c_1888,plain,(
    ! [H_7809] : H_7809 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_1886])).

tff(c_1930,plain,(
    '#skF_3' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_1888,c_943])).

tff(c_2154,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_1930])).

tff(c_2155,plain,(
    ! [H_594,H_593,H_598,I_597,H_592] :
      ( H_598 = '#skF_4'
      | H_592 = '#skF_4'
      | H_594 = '#skF_4'
      | I_597 = '#skF_4'
      | H_593 = '#skF_4' ) ),
    inference(splitRight,[status(thm)],[c_1886])).

tff(c_2157,plain,(
    ! [H_14818] : H_14818 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_2155])).

tff(c_2199,plain,(
    '#skF_3' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_2157,c_943])).

tff(c_2423,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_2199])).

tff(c_2424,plain,(
    ! [H_594,H_598,H_592,I_597] :
      ( H_594 = '#skF_4'
      | H_598 = '#skF_4'
      | H_592 = '#skF_4'
      | I_597 = '#skF_4' ) ),
    inference(splitRight,[status(thm)],[c_2155])).

tff(c_2427,plain,(
    ! [I_21837] : I_21837 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_2424])).

tff(c_2471,plain,(
    '#skF_3' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_2427,c_943])).

tff(c_2695,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_2471])).

tff(c_2696,plain,(
    ! [H_598,H_594,H_592] :
      ( H_598 = '#skF_4'
      | H_594 = '#skF_4'
      | H_592 = '#skF_4' ) ),
    inference(splitRight,[status(thm)],[c_2424])).

tff(c_2698,plain,(
    ! [H_28919] : H_28919 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_2696])).

tff(c_2740,plain,(
    '#skF_3' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_2698,c_943])).

tff(c_2964,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_2740])).

tff(c_2965,plain,(
    ! [H_598,H_594] :
      ( H_598 = '#skF_4'
      | H_594 = '#skF_4' ) ),
    inference(splitRight,[status(thm)],[c_2696])).

tff(c_2967,plain,(
    ! [H_35928] : H_35928 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_2965])).

tff(c_3009,plain,(
    '#skF_3' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_2967,c_943])).

tff(c_3233,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_3009])).

tff(c_3235,plain,(
    ! [H_42937] : H_42937 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_2965])).

tff(c_3277,plain,(
    '#skF_3' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_3235,c_943])).

tff(c_3501,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_3277])).

tff(c_3502,plain,(
    ! [C_245,F_243,I_241,D_247,B_242,E_246,G_244] :
      ( B_242 = '#skF_3'
      | D_247 = '#skF_3'
      | F_243 = '#skF_3'
      | I_241 = '#skF_3'
      | G_244 = '#skF_3'
      | E_246 = '#skF_3'
      | C_245 = '#skF_3' ) ),
    inference(splitRight,[status(thm)],[c_940])).

tff(c_3505,plain,(
    ! [C_49946] : C_49946 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_3502])).

tff(c_3503,plain,(
    '#skF_5' != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_940])).

tff(c_3835,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_3505,c_3503])).

tff(c_3836,plain,(
    ! [F_243,I_241,D_247,B_242,E_246,G_244] :
      ( G_244 = '#skF_3'
      | F_243 = '#skF_3'
      | B_242 = '#skF_3'
      | D_247 = '#skF_3'
      | I_241 = '#skF_3'
      | E_246 = '#skF_3' ) ),
    inference(splitRight,[status(thm)],[c_3502])).

tff(c_3839,plain,(
    ! [E_57330] : E_57330 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_3836])).

tff(c_4171,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_3839,c_3503])).

tff(c_4172,plain,(
    ! [F_243,I_241,D_247,B_242,G_244] :
      ( D_247 = '#skF_3'
      | F_243 = '#skF_3'
      | G_244 = '#skF_3'
      | B_242 = '#skF_3'
      | I_241 = '#skF_3' ) ),
    inference(splitRight,[status(thm)],[c_3836])).

tff(c_4174,plain,(
    ! [I_64777] : I_64777 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_4172])).

tff(c_4506,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_4174,c_3503])).

tff(c_4507,plain,(
    ! [G_244,D_247,F_243,B_242] :
      ( G_244 = '#skF_3'
      | D_247 = '#skF_3'
      | F_243 = '#skF_3'
      | B_242 = '#skF_3' ) ),
    inference(splitRight,[status(thm)],[c_4172])).

tff(c_4509,plain,(
    ! [B_72224] : B_72224 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_4507])).

tff(c_4841,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_4509,c_3503])).

tff(c_4842,plain,(
    ! [D_247,G_244,F_243] :
      ( D_247 = '#skF_3'
      | G_244 = '#skF_3'
      | F_243 = '#skF_3' ) ),
    inference(splitRight,[status(thm)],[c_4507])).

tff(c_4844,plain,(
    ! [F_79671] : F_79671 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_4842])).

tff(c_5176,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_4844,c_3503])).

tff(c_5177,plain,(
    ! [D_247,G_244] :
      ( D_247 = '#skF_3'
      | G_244 = '#skF_3' ) ),
    inference(splitRight,[status(thm)],[c_4842])).

tff(c_5190,plain,(
    ! [G_87128] : G_87128 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_5177])).

tff(c_5524,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_5190,c_3503])).

tff(c_5526,plain,(
    ! [D_94648] : D_94648 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_5177])).

tff(c_5858,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_5526,c_3503])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:34:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.93/2.36  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.93/2.37  
% 6.93/2.37  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.93/2.37  %$ r2_hidden > k7_enumset1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_5 > #skF_3 > #skF_1 > #skF_4
% 6.93/2.37  
% 6.93/2.37  %Foreground sorts:
% 6.93/2.37  
% 6.93/2.37  
% 6.93/2.37  %Background operators:
% 6.93/2.37  
% 6.93/2.37  
% 6.93/2.37  %Foreground operators:
% 6.93/2.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.93/2.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.93/2.37  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.93/2.37  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.93/2.37  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 6.93/2.37  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.93/2.37  tff(k7_enumset1, type, k7_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 6.93/2.37  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 6.93/2.37  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.93/2.37  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.93/2.37  tff('#skF_5', type, '#skF_5': $i).
% 6.93/2.37  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.93/2.37  tff('#skF_3', type, '#skF_3': $i).
% 6.93/2.37  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.93/2.37  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 6.93/2.37  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 6.93/2.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.93/2.37  tff('#skF_4', type, '#skF_4': $i).
% 6.93/2.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.93/2.37  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.93/2.37  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.93/2.37  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 6.93/2.37  
% 6.93/2.39  tff(f_85, negated_conjecture, ~(![A, B, C]: ((k1_tarski(A) = k2_tarski(B, C)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_zfmisc_1)).
% 6.93/2.39  tff(f_66, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k5_enumset1(A, B, C, D, E, F, G), k1_tarski(H)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t68_enumset1)).
% 6.93/2.39  tff(f_80, axiom, (![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 6.93/2.39  tff(f_78, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 6.93/2.39  tff(f_76, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 6.93/2.39  tff(f_74, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 6.93/2.39  tff(f_72, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 6.93/2.39  tff(f_70, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 6.93/2.39  tff(f_68, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 6.93/2.39  tff(f_64, axiom, (![A, B, C, D, E, F, G, H, I]: (k7_enumset1(A, B, C, D, E, F, G, H, I) = k2_xboole_0(k6_enumset1(A, B, C, D, E, F, G, H), k1_tarski(I)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t134_enumset1)).
% 6.93/2.39  tff(f_62, axiom, (![A, B, C, D, E, F, G, H, I, J]: ((J = k7_enumset1(A, B, C, D, E, F, G, H, I)) <=> (![K]: (r2_hidden(K, J) <=> ~((((((((~(K = A) & ~(K = B)) & ~(K = C)) & ~(K = D)) & ~(K = E)) & ~(K = F)) & ~(K = G)) & ~(K = H)) & ~(K = I)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_enumset1)).
% 6.93/2.39  tff(c_84, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_85])).
% 6.93/2.39  tff(c_68, plain, (![C_29, D_30, B_28, G_33, F_32, A_27, E_31, H_34]: (k2_xboole_0(k5_enumset1(A_27, B_28, C_29, D_30, E_31, F_32, G_33), k1_tarski(H_34))=k6_enumset1(A_27, B_28, C_29, D_30, E_31, F_32, G_33, H_34))), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.93/2.39  tff(c_82, plain, (![D_59, A_56, B_57, G_62, F_61, C_58, E_60]: (k6_enumset1(A_56, A_56, B_57, C_58, D_59, E_60, F_61, G_62)=k5_enumset1(A_56, B_57, C_58, D_59, E_60, F_61, G_62))), inference(cnfTransformation, [status(thm)], [f_80])).
% 6.93/2.39  tff(c_80, plain, (![A_50, B_51, E_54, C_52, D_53, F_55]: (k5_enumset1(A_50, A_50, B_51, C_52, D_53, E_54, F_55)=k4_enumset1(A_50, B_51, C_52, D_53, E_54, F_55))), inference(cnfTransformation, [status(thm)], [f_78])).
% 6.93/2.39  tff(c_181, plain, (![D_179, C_177, G_182, F_176, E_180, H_178, A_183, B_181]: (k2_xboole_0(k5_enumset1(A_183, B_181, C_177, D_179, E_180, F_176, G_182), k1_tarski(H_178))=k6_enumset1(A_183, B_181, C_177, D_179, E_180, F_176, G_182, H_178))), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.93/2.39  tff(c_190, plain, (![A_50, B_51, E_54, C_52, D_53, F_55, H_178]: (k6_enumset1(A_50, A_50, B_51, C_52, D_53, E_54, F_55, H_178)=k2_xboole_0(k4_enumset1(A_50, B_51, C_52, D_53, E_54, F_55), k1_tarski(H_178)))), inference(superposition, [status(thm), theory('equality')], [c_80, c_181])).
% 6.93/2.39  tff(c_193, plain, (![A_50, B_51, E_54, C_52, D_53, F_55, H_178]: (k2_xboole_0(k4_enumset1(A_50, B_51, C_52, D_53, E_54, F_55), k1_tarski(H_178))=k5_enumset1(A_50, B_51, C_52, D_53, E_54, F_55, H_178))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_190])).
% 6.93/2.39  tff(c_78, plain, (![D_48, C_47, A_45, B_46, E_49]: (k4_enumset1(A_45, A_45, B_46, C_47, D_48, E_49)=k3_enumset1(A_45, B_46, C_47, D_48, E_49))), inference(cnfTransformation, [status(thm)], [f_76])).
% 6.93/2.39  tff(c_194, plain, (![C_187, H_186, B_188, A_185, E_184, F_189, D_190]: (k2_xboole_0(k4_enumset1(A_185, B_188, C_187, D_190, E_184, F_189), k1_tarski(H_186))=k5_enumset1(A_185, B_188, C_187, D_190, E_184, F_189, H_186))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_190])).
% 6.93/2.39  tff(c_203, plain, (![H_186, D_48, C_47, A_45, B_46, E_49]: (k5_enumset1(A_45, A_45, B_46, C_47, D_48, E_49, H_186)=k2_xboole_0(k3_enumset1(A_45, B_46, C_47, D_48, E_49), k1_tarski(H_186)))), inference(superposition, [status(thm), theory('equality')], [c_78, c_194])).
% 6.93/2.39  tff(c_206, plain, (![H_186, D_48, C_47, A_45, B_46, E_49]: (k2_xboole_0(k3_enumset1(A_45, B_46, C_47, D_48, E_49), k1_tarski(H_186))=k4_enumset1(A_45, B_46, C_47, D_48, E_49, H_186))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_203])).
% 6.93/2.39  tff(c_76, plain, (![A_41, B_42, C_43, D_44]: (k3_enumset1(A_41, A_41, B_42, C_43, D_44)=k2_enumset1(A_41, B_42, C_43, D_44))), inference(cnfTransformation, [status(thm)], [f_74])).
% 6.93/2.39  tff(c_207, plain, (![B_192, C_195, A_193, D_194, H_191, E_196]: (k2_xboole_0(k3_enumset1(A_193, B_192, C_195, D_194, E_196), k1_tarski(H_191))=k4_enumset1(A_193, B_192, C_195, D_194, E_196, H_191))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_203])).
% 6.93/2.39  tff(c_216, plain, (![D_44, C_43, A_41, H_191, B_42]: (k4_enumset1(A_41, A_41, B_42, C_43, D_44, H_191)=k2_xboole_0(k2_enumset1(A_41, B_42, C_43, D_44), k1_tarski(H_191)))), inference(superposition, [status(thm), theory('equality')], [c_76, c_207])).
% 6.93/2.39  tff(c_219, plain, (![D_44, C_43, A_41, H_191, B_42]: (k2_xboole_0(k2_enumset1(A_41, B_42, C_43, D_44), k1_tarski(H_191))=k3_enumset1(A_41, B_42, C_43, D_44, H_191))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_216])).
% 6.93/2.39  tff(c_74, plain, (![A_38, B_39, C_40]: (k2_enumset1(A_38, A_38, B_39, C_40)=k1_enumset1(A_38, B_39, C_40))), inference(cnfTransformation, [status(thm)], [f_72])).
% 6.93/2.39  tff(c_220, plain, (![H_197, C_199, A_198, D_200, B_201]: (k2_xboole_0(k2_enumset1(A_198, B_201, C_199, D_200), k1_tarski(H_197))=k3_enumset1(A_198, B_201, C_199, D_200, H_197))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_216])).
% 6.93/2.39  tff(c_229, plain, (![A_38, B_39, C_40, H_197]: (k3_enumset1(A_38, A_38, B_39, C_40, H_197)=k2_xboole_0(k1_enumset1(A_38, B_39, C_40), k1_tarski(H_197)))), inference(superposition, [status(thm), theory('equality')], [c_74, c_220])).
% 6.93/2.39  tff(c_232, plain, (![A_38, B_39, C_40, H_197]: (k2_xboole_0(k1_enumset1(A_38, B_39, C_40), k1_tarski(H_197))=k2_enumset1(A_38, B_39, C_40, H_197))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_229])).
% 6.93/2.39  tff(c_72, plain, (![A_36, B_37]: (k1_enumset1(A_36, A_36, B_37)=k2_tarski(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.93/2.39  tff(c_233, plain, (![A_202, B_203, C_204, H_205]: (k2_xboole_0(k1_enumset1(A_202, B_203, C_204), k1_tarski(H_205))=k2_enumset1(A_202, B_203, C_204, H_205))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_229])).
% 6.93/2.39  tff(c_242, plain, (![A_36, B_37, H_205]: (k2_xboole_0(k2_tarski(A_36, B_37), k1_tarski(H_205))=k2_enumset1(A_36, A_36, B_37, H_205))), inference(superposition, [status(thm), theory('equality')], [c_72, c_233])).
% 6.93/2.39  tff(c_245, plain, (![A_36, B_37, H_205]: (k2_xboole_0(k2_tarski(A_36, B_37), k1_tarski(H_205))=k1_enumset1(A_36, B_37, H_205))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_242])).
% 6.93/2.39  tff(c_70, plain, (![A_35]: (k2_tarski(A_35, A_35)=k1_tarski(A_35))), inference(cnfTransformation, [status(thm)], [f_68])).
% 6.93/2.39  tff(c_259, plain, (![A_215, B_216, H_217]: (k2_xboole_0(k2_tarski(A_215, B_216), k1_tarski(H_217))=k1_enumset1(A_215, B_216, H_217))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_242])).
% 6.93/2.39  tff(c_268, plain, (![A_35, H_217]: (k2_xboole_0(k1_tarski(A_35), k1_tarski(H_217))=k1_enumset1(A_35, A_35, H_217))), inference(superposition, [status(thm), theory('equality')], [c_70, c_259])).
% 6.93/2.39  tff(c_274, plain, (![A_35, H_217]: (k2_xboole_0(k1_tarski(A_35), k1_tarski(H_217))=k2_tarski(A_35, H_217))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_268])).
% 6.93/2.39  tff(c_86, plain, (k2_tarski('#skF_4', '#skF_5')=k1_tarski('#skF_3')), inference(cnfTransformation, [status(thm)], [f_85])).
% 6.93/2.39  tff(c_271, plain, (![H_217]: (k2_xboole_0(k1_tarski('#skF_3'), k1_tarski(H_217))=k1_enumset1('#skF_4', '#skF_5', H_217))), inference(superposition, [status(thm), theory('equality')], [c_86, c_259])).
% 6.93/2.39  tff(c_285, plain, (![H_220]: (k1_enumset1('#skF_4', '#skF_5', H_220)=k2_tarski('#skF_3', H_220))), inference(demodulation, [status(thm), theory('equality')], [c_274, c_271])).
% 6.93/2.39  tff(c_291, plain, (![H_220, H_197]: (k2_xboole_0(k2_tarski('#skF_3', H_220), k1_tarski(H_197))=k2_enumset1('#skF_4', '#skF_5', H_220, H_197))), inference(superposition, [status(thm), theory('equality')], [c_285, c_232])).
% 6.93/2.39  tff(c_298, plain, (![H_221, H_222]: (k2_enumset1('#skF_4', '#skF_5', H_221, H_222)=k1_enumset1('#skF_3', H_221, H_222))), inference(demodulation, [status(thm), theory('equality')], [c_245, c_291])).
% 6.93/2.39  tff(c_304, plain, (![H_221, H_222, H_191]: (k2_xboole_0(k1_enumset1('#skF_3', H_221, H_222), k1_tarski(H_191))=k3_enumset1('#skF_4', '#skF_5', H_221, H_222, H_191))), inference(superposition, [status(thm), theory('equality')], [c_298, c_219])).
% 6.93/2.39  tff(c_311, plain, (![H_223, H_224, H_225]: (k3_enumset1('#skF_4', '#skF_5', H_223, H_224, H_225)=k2_enumset1('#skF_3', H_223, H_224, H_225))), inference(demodulation, [status(thm), theory('equality')], [c_232, c_304])).
% 6.93/2.39  tff(c_317, plain, (![H_223, H_224, H_225, H_186]: (k2_xboole_0(k2_enumset1('#skF_3', H_223, H_224, H_225), k1_tarski(H_186))=k4_enumset1('#skF_4', '#skF_5', H_223, H_224, H_225, H_186))), inference(superposition, [status(thm), theory('equality')], [c_311, c_206])).
% 6.93/2.39  tff(c_324, plain, (![H_226, H_227, H_228, H_229]: (k4_enumset1('#skF_4', '#skF_5', H_226, H_227, H_228, H_229)=k3_enumset1('#skF_3', H_226, H_227, H_228, H_229))), inference(demodulation, [status(thm), theory('equality')], [c_219, c_317])).
% 6.93/2.39  tff(c_330, plain, (![H_228, H_226, H_227, H_178, H_229]: (k2_xboole_0(k3_enumset1('#skF_3', H_226, H_227, H_228, H_229), k1_tarski(H_178))=k5_enumset1('#skF_4', '#skF_5', H_226, H_227, H_228, H_229, H_178))), inference(superposition, [status(thm), theory('equality')], [c_324, c_193])).
% 6.93/2.39  tff(c_337, plain, (![H_230, H_233, H_231, H_234, H_232]: (k5_enumset1('#skF_4', '#skF_5', H_233, H_232, H_234, H_230, H_231)=k4_enumset1('#skF_3', H_233, H_232, H_234, H_230, H_231))), inference(demodulation, [status(thm), theory('equality')], [c_206, c_330])).
% 6.93/2.39  tff(c_343, plain, (![H_230, H_233, H_231, H_234, H_232, H_34]: (k2_xboole_0(k4_enumset1('#skF_3', H_233, H_232, H_234, H_230, H_231), k1_tarski(H_34))=k6_enumset1('#skF_4', '#skF_5', H_233, H_232, H_234, H_230, H_231, H_34))), inference(superposition, [status(thm), theory('equality')], [c_337, c_68])).
% 6.93/2.39  tff(c_350, plain, (![H_236, H_239, H_237, H_240, H_238, H_235]: (k6_enumset1('#skF_4', '#skF_5', H_236, H_240, H_239, H_238, H_235, H_237)=k5_enumset1('#skF_3', H_236, H_240, H_239, H_238, H_235, H_237))), inference(demodulation, [status(thm), theory('equality')], [c_193, c_343])).
% 6.93/2.39  tff(c_66, plain, (![H_25, E_22, G_24, D_21, F_23, A_18, C_20, B_19, I_26]: (k2_xboole_0(k6_enumset1(A_18, B_19, C_20, D_21, E_22, F_23, G_24, H_25), k1_tarski(I_26))=k7_enumset1(A_18, B_19, C_20, D_21, E_22, F_23, G_24, H_25, I_26))), inference(cnfTransformation, [status(thm)], [f_64])).
% 6.93/2.39  tff(c_356, plain, (![H_236, H_239, H_237, H_240, H_238, H_235, I_26]: (k2_xboole_0(k5_enumset1('#skF_3', H_236, H_240, H_239, H_238, H_235, H_237), k1_tarski(I_26))=k7_enumset1('#skF_4', '#skF_5', H_236, H_240, H_239, H_238, H_235, H_237, I_26))), inference(superposition, [status(thm), theory('equality')], [c_350, c_66])).
% 6.93/2.39  tff(c_821, plain, (![H_594, H_595, H_593, H_598, H_596, I_597, H_592]: (k7_enumset1('#skF_4', '#skF_5', H_595, H_596, H_594, H_593, H_592, H_598, I_597)=k6_enumset1('#skF_3', H_595, H_596, H_594, H_593, H_592, H_598, I_597))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_356])).
% 6.93/2.39  tff(c_24, plain, (![B_6, H_12, C_7, I_13, E_9, D_8, G_11, K_17, F_10]: (r2_hidden(K_17, k7_enumset1(K_17, B_6, C_7, D_8, E_9, F_10, G_11, H_12, I_13)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 6.93/2.39  tff(c_851, plain, (![H_594, H_595, H_593, H_598, H_596, I_597, H_592]: (r2_hidden('#skF_4', k6_enumset1('#skF_3', H_595, H_596, H_594, H_593, H_592, H_598, I_597)))), inference(superposition, [status(thm), theory('equality')], [c_821, c_24])).
% 6.93/2.39  tff(c_246, plain, (![A_206, D_212, I_208, G_214, E_209, C_207, H_210, B_213, F_211]: (k2_xboole_0(k6_enumset1(A_206, B_213, C_207, D_212, E_209, F_211, G_214, H_210), k1_tarski(I_208))=k7_enumset1(A_206, B_213, C_207, D_212, E_209, F_211, G_214, H_210, I_208))), inference(cnfTransformation, [status(thm)], [f_64])).
% 6.93/2.39  tff(c_255, plain, (![D_59, I_208, A_56, B_57, G_62, F_61, C_58, E_60]: (k7_enumset1(A_56, A_56, B_57, C_58, D_59, E_60, F_61, G_62, I_208)=k2_xboole_0(k5_enumset1(A_56, B_57, C_58, D_59, E_60, F_61, G_62), k1_tarski(I_208)))), inference(superposition, [status(thm), theory('equality')], [c_82, c_246])).
% 6.93/2.39  tff(c_258, plain, (![D_59, I_208, A_56, B_57, G_62, F_61, C_58, E_60]: (k7_enumset1(A_56, A_56, B_57, C_58, D_59, E_60, F_61, G_62, I_208)=k6_enumset1(A_56, B_57, C_58, D_59, E_60, F_61, G_62, I_208))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_255])).
% 6.93/2.39  tff(c_399, plain, (![I_250, G_252, D_249, A_255, K_256, F_251, E_258, B_253, H_257, C_254]: (K_256=I_250 | K_256=H_257 | K_256=G_252 | K_256=F_251 | K_256=E_258 | K_256=D_249 | K_256=C_254 | K_256=B_253 | K_256=A_255 | ~r2_hidden(K_256, k7_enumset1(A_255, B_253, C_254, D_249, E_258, F_251, G_252, H_257, I_250)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 6.93/2.39  tff(c_1560, plain, (![A_715, E_713, K_712, F_709, I_707, C_711, D_714, G_710, B_708]: (K_712=I_707 | K_712=G_710 | K_712=F_709 | K_712=E_713 | K_712=D_714 | K_712=C_711 | K_712=B_708 | K_712=A_715 | K_712=A_715 | ~r2_hidden(K_712, k6_enumset1(A_715, B_708, C_711, D_714, E_713, F_709, G_710, I_707)))), inference(superposition, [status(thm), theory('equality')], [c_258, c_399])).
% 6.93/2.39  tff(c_1570, plain, (![H_594, H_595, H_593, H_598, H_596, I_597, H_592]: (I_597='#skF_4' | H_598='#skF_4' | H_592='#skF_4' | H_593='#skF_4' | H_594='#skF_4' | H_596='#skF_4' | H_595='#skF_4' | '#skF_3'='#skF_4')), inference(resolution, [status(thm)], [c_851, c_1560])).
% 6.93/2.39  tff(c_1601, plain, (![H_594, H_595, H_593, H_598, H_596, I_597, H_592]: (I_597='#skF_4' | H_598='#skF_4' | H_592='#skF_4' | H_593='#skF_4' | H_594='#skF_4' | H_596='#skF_4' | H_595='#skF_4')), inference(negUnitSimplification, [status(thm)], [c_84, c_84, c_1570])).
% 6.93/2.39  tff(c_1619, plain, (![H_716]: (H_716='#skF_4')), inference(splitLeft, [status(thm)], [c_1601])).
% 6.93/2.39  tff(c_363, plain, (![C_245, F_243, I_241, D_247, A_248, B_242, E_246, G_244]: (k7_enumset1(A_248, A_248, B_242, C_245, D_247, E_246, F_243, G_244, I_241)=k6_enumset1(A_248, B_242, C_245, D_247, E_246, F_243, G_244, I_241))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_255])).
% 6.93/2.39  tff(c_390, plain, (![C_245, F_243, I_241, D_247, A_248, B_242, E_246, G_244]: (r2_hidden(A_248, k6_enumset1(A_248, B_242, C_245, D_247, E_246, F_243, G_244, I_241)))), inference(superposition, [status(thm), theory('equality')], [c_363, c_24])).
% 6.93/2.39  tff(c_6, plain, (![B_6, H_12, C_7, I_13, E_9, D_8, A_5, G_11, K_17, F_10]: (K_17=I_13 | K_17=H_12 | K_17=G_11 | K_17=F_10 | K_17=E_9 | K_17=D_8 | K_17=C_7 | K_17=B_6 | K_17=A_5 | ~r2_hidden(K_17, k7_enumset1(A_5, B_6, C_7, D_8, E_9, F_10, G_11, H_12, I_13)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 6.93/2.39  tff(c_879, plain, (![H_617, I_618, H_620, H_616, H_615, K_619, H_613, H_614]: (K_619=I_618 | K_619=H_614 | K_619=H_615 | K_619=H_616 | K_619=H_617 | K_619=H_613 | K_619=H_620 | K_619='#skF_5' | K_619='#skF_4' | ~r2_hidden(K_619, k6_enumset1('#skF_3', H_620, H_613, H_617, H_616, H_615, H_614, I_618)))), inference(superposition, [status(thm), theory('equality')], [c_821, c_6])).
% 6.93/2.39  tff(c_913, plain, (![C_245, F_243, I_241, D_247, B_242, E_246, G_244]: (I_241='#skF_3' | G_244='#skF_3' | F_243='#skF_3' | E_246='#skF_3' | D_247='#skF_3' | C_245='#skF_3' | B_242='#skF_3' | '#skF_5'='#skF_3' | '#skF_3'='#skF_4')), inference(resolution, [status(thm)], [c_390, c_879])).
% 6.93/2.39  tff(c_940, plain, (![C_245, F_243, I_241, D_247, B_242, E_246, G_244]: (I_241='#skF_3' | G_244='#skF_3' | F_243='#skF_3' | E_246='#skF_3' | D_247='#skF_3' | C_245='#skF_3' | B_242='#skF_3' | '#skF_5'='#skF_3')), inference(negUnitSimplification, [status(thm)], [c_84, c_913])).
% 6.93/2.39  tff(c_943, plain, ('#skF_5'='#skF_3'), inference(splitLeft, [status(thm)], [c_940])).
% 6.93/2.39  tff(c_1661, plain, ('#skF_3'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_1619, c_943])).
% 6.93/2.39  tff(c_1885, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84, c_1661])).
% 6.93/2.39  tff(c_1886, plain, (![H_594, H_593, H_598, H_596, I_597, H_592]: (H_594='#skF_4' | H_592='#skF_4' | I_597='#skF_4' | H_598='#skF_4' | H_593='#skF_4' | H_596='#skF_4')), inference(splitRight, [status(thm)], [c_1601])).
% 6.93/2.39  tff(c_1888, plain, (![H_7809]: (H_7809='#skF_4')), inference(splitLeft, [status(thm)], [c_1886])).
% 6.93/2.39  tff(c_1930, plain, ('#skF_3'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_1888, c_943])).
% 6.93/2.39  tff(c_2154, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84, c_1930])).
% 6.93/2.39  tff(c_2155, plain, (![H_594, H_593, H_598, I_597, H_592]: (H_598='#skF_4' | H_592='#skF_4' | H_594='#skF_4' | I_597='#skF_4' | H_593='#skF_4')), inference(splitRight, [status(thm)], [c_1886])).
% 6.93/2.39  tff(c_2157, plain, (![H_14818]: (H_14818='#skF_4')), inference(splitLeft, [status(thm)], [c_2155])).
% 6.93/2.39  tff(c_2199, plain, ('#skF_3'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_2157, c_943])).
% 6.93/2.39  tff(c_2423, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84, c_2199])).
% 6.93/2.39  tff(c_2424, plain, (![H_594, H_598, H_592, I_597]: (H_594='#skF_4' | H_598='#skF_4' | H_592='#skF_4' | I_597='#skF_4')), inference(splitRight, [status(thm)], [c_2155])).
% 6.93/2.39  tff(c_2427, plain, (![I_21837]: (I_21837='#skF_4')), inference(splitLeft, [status(thm)], [c_2424])).
% 6.93/2.39  tff(c_2471, plain, ('#skF_3'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_2427, c_943])).
% 6.93/2.39  tff(c_2695, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84, c_2471])).
% 6.93/2.39  tff(c_2696, plain, (![H_598, H_594, H_592]: (H_598='#skF_4' | H_594='#skF_4' | H_592='#skF_4')), inference(splitRight, [status(thm)], [c_2424])).
% 6.93/2.39  tff(c_2698, plain, (![H_28919]: (H_28919='#skF_4')), inference(splitLeft, [status(thm)], [c_2696])).
% 6.93/2.39  tff(c_2740, plain, ('#skF_3'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_2698, c_943])).
% 6.93/2.39  tff(c_2964, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84, c_2740])).
% 6.93/2.39  tff(c_2965, plain, (![H_598, H_594]: (H_598='#skF_4' | H_594='#skF_4')), inference(splitRight, [status(thm)], [c_2696])).
% 6.93/2.39  tff(c_2967, plain, (![H_35928]: (H_35928='#skF_4')), inference(splitLeft, [status(thm)], [c_2965])).
% 6.93/2.39  tff(c_3009, plain, ('#skF_3'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_2967, c_943])).
% 6.93/2.39  tff(c_3233, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84, c_3009])).
% 6.93/2.39  tff(c_3235, plain, (![H_42937]: (H_42937='#skF_4')), inference(splitRight, [status(thm)], [c_2965])).
% 6.93/2.39  tff(c_3277, plain, ('#skF_3'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_3235, c_943])).
% 6.93/2.39  tff(c_3501, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84, c_3277])).
% 6.93/2.39  tff(c_3502, plain, (![C_245, F_243, I_241, D_247, B_242, E_246, G_244]: (B_242='#skF_3' | D_247='#skF_3' | F_243='#skF_3' | I_241='#skF_3' | G_244='#skF_3' | E_246='#skF_3' | C_245='#skF_3')), inference(splitRight, [status(thm)], [c_940])).
% 6.93/2.39  tff(c_3505, plain, (![C_49946]: (C_49946='#skF_3')), inference(splitLeft, [status(thm)], [c_3502])).
% 6.93/2.39  tff(c_3503, plain, ('#skF_5'!='#skF_3'), inference(splitRight, [status(thm)], [c_940])).
% 6.93/2.39  tff(c_3835, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_3505, c_3503])).
% 6.93/2.39  tff(c_3836, plain, (![F_243, I_241, D_247, B_242, E_246, G_244]: (G_244='#skF_3' | F_243='#skF_3' | B_242='#skF_3' | D_247='#skF_3' | I_241='#skF_3' | E_246='#skF_3')), inference(splitRight, [status(thm)], [c_3502])).
% 6.93/2.39  tff(c_3839, plain, (![E_57330]: (E_57330='#skF_3')), inference(splitLeft, [status(thm)], [c_3836])).
% 6.93/2.39  tff(c_4171, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_3839, c_3503])).
% 6.93/2.39  tff(c_4172, plain, (![F_243, I_241, D_247, B_242, G_244]: (D_247='#skF_3' | F_243='#skF_3' | G_244='#skF_3' | B_242='#skF_3' | I_241='#skF_3')), inference(splitRight, [status(thm)], [c_3836])).
% 6.93/2.39  tff(c_4174, plain, (![I_64777]: (I_64777='#skF_3')), inference(splitLeft, [status(thm)], [c_4172])).
% 6.93/2.39  tff(c_4506, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_4174, c_3503])).
% 6.93/2.39  tff(c_4507, plain, (![G_244, D_247, F_243, B_242]: (G_244='#skF_3' | D_247='#skF_3' | F_243='#skF_3' | B_242='#skF_3')), inference(splitRight, [status(thm)], [c_4172])).
% 6.93/2.39  tff(c_4509, plain, (![B_72224]: (B_72224='#skF_3')), inference(splitLeft, [status(thm)], [c_4507])).
% 6.93/2.39  tff(c_4841, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_4509, c_3503])).
% 6.93/2.39  tff(c_4842, plain, (![D_247, G_244, F_243]: (D_247='#skF_3' | G_244='#skF_3' | F_243='#skF_3')), inference(splitRight, [status(thm)], [c_4507])).
% 6.93/2.39  tff(c_4844, plain, (![F_79671]: (F_79671='#skF_3')), inference(splitLeft, [status(thm)], [c_4842])).
% 6.93/2.39  tff(c_5176, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_4844, c_3503])).
% 6.93/2.39  tff(c_5177, plain, (![D_247, G_244]: (D_247='#skF_3' | G_244='#skF_3')), inference(splitRight, [status(thm)], [c_4842])).
% 6.93/2.39  tff(c_5190, plain, (![G_87128]: (G_87128='#skF_3')), inference(splitLeft, [status(thm)], [c_5177])).
% 6.93/2.39  tff(c_5524, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_5190, c_3503])).
% 6.93/2.39  tff(c_5526, plain, (![D_94648]: (D_94648='#skF_3')), inference(splitRight, [status(thm)], [c_5177])).
% 6.93/2.39  tff(c_5858, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_5526, c_3503])).
% 6.93/2.39  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.93/2.39  
% 6.93/2.39  Inference rules
% 6.93/2.39  ----------------------
% 6.93/2.39  #Ref     : 0
% 6.93/2.39  #Sup     : 2294
% 6.93/2.39  #Fact    : 0
% 6.93/2.39  #Define  : 0
% 6.93/2.39  #Split   : 13
% 6.93/2.39  #Chain   : 0
% 6.93/2.39  #Close   : 0
% 6.93/2.39  
% 6.93/2.39  Ordering : KBO
% 6.93/2.39  
% 6.93/2.39  Simplification rules
% 6.93/2.39  ----------------------
% 6.93/2.39  #Subsume      : 105
% 6.93/2.39  #Demod        : 207
% 6.93/2.39  #Tautology    : 243
% 6.93/2.39  #SimpNegUnit  : 23
% 6.93/2.39  #BackRed      : 17
% 6.93/2.39  
% 6.93/2.39  #Partial instantiations: 714
% 6.93/2.39  #Strategies tried      : 1
% 6.93/2.39  
% 6.93/2.39  Timing (in seconds)
% 6.93/2.39  ----------------------
% 7.29/2.39  Preprocessing        : 0.36
% 7.29/2.39  Parsing              : 0.17
% 7.29/2.40  CNF conversion       : 0.03
% 7.29/2.40  Main loop            : 1.24
% 7.29/2.40  Inferencing          : 0.65
% 7.29/2.40  Reduction            : 0.25
% 7.29/2.40  Demodulation         : 0.19
% 7.29/2.40  BG Simplification    : 0.04
% 7.29/2.40  Subsumption          : 0.27
% 7.29/2.40  Abstraction          : 0.07
% 7.29/2.40  MUC search           : 0.00
% 7.29/2.40  Cooper               : 0.00
% 7.29/2.40  Total                : 1.64
% 7.29/2.40  Index Insertion      : 0.00
% 7.29/2.40  Index Deletion       : 0.00
% 7.29/2.40  Index Matching       : 0.00
% 7.29/2.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
