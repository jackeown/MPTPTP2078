%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:52 EST 2020

% Result     : Theorem 2.85s
% Output     : CNFRefutation 3.21s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 169 expanded)
%              Number of leaves         :   23 (  79 expanded)
%              Depth                    :   14
%              Number of atoms          :  278 ( 740 expanded)
%              Number of equality atoms :  234 ( 593 expanded)
%              Maximal formula depth    :   25 (   8 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > k9_mcart_1 > k8_mcart_1 > k11_mcart_1 > k10_mcart_1 > k4_zfmisc_1 > k4_mcart_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_9 > #skF_3 > #skF_1 > #skF_8

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i ) > $i )).

tff(k10_mcart_1,type,(
    k10_mcart_1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i * $i ) > $i )).

tff(k4_zfmisc_1,type,(
    k4_zfmisc_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k11_mcart_1,type,(
    k11_mcart_1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff(k8_mcart_1,type,(
    k8_mcart_1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k9_mcart_1,type,(
    k9_mcart_1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k4_mcart_1,type,(
    k4_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_104,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ~ ( A != k1_xboole_0
          & B != k1_xboole_0
          & C != k1_xboole_0
          & D != k1_xboole_0
          & ~ ! [E] :
                ( m1_subset_1(E,k4_zfmisc_1(A,B,C,D))
               => E = k4_mcart_1(k8_mcart_1(A,B,C,D,E),k9_mcart_1(A,B,C,D,E),k10_mcart_1(A,B,C,D,E),k11_mcart_1(A,B,C,D,E)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_mcart_1)).

tff(f_56,axiom,(
    ! [A,B,C,D] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & D != k1_xboole_0
        & ? [E] :
            ( m1_subset_1(E,k4_zfmisc_1(A,B,C,D))
            & ! [F] :
                ( m1_subset_1(F,A)
               => ! [G] :
                    ( m1_subset_1(G,B)
                   => ! [H] :
                        ( m1_subset_1(H,C)
                       => ! [I] :
                            ( m1_subset_1(I,D)
                           => E != k4_mcart_1(F,G,H,I) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l68_mcart_1)).

tff(f_84,axiom,(
    ! [A,B,C,D] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & D != k1_xboole_0
        & ? [E] :
            ( m1_subset_1(E,k4_zfmisc_1(A,B,C,D))
            & ? [F,G,H,I] :
                ( E = k4_mcart_1(F,G,H,I)
                & ~ ( k8_mcart_1(A,B,C,D,E) = F
                    & k9_mcart_1(A,B,C,D,E) = G
                    & k10_mcart_1(A,B,C,D,E) = H
                    & k11_mcart_1(A,B,C,D,E) = I ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_mcart_1)).

tff(c_30,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_28,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_26,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_24,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_22,plain,(
    m1_subset_1('#skF_9',k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_2,plain,(
    ! [B_2,C_3,A_1,D_4,E_36] :
      ( k4_mcart_1('#skF_1'(E_36,D_4,B_2,C_3,A_1),'#skF_2'(E_36,D_4,B_2,C_3,A_1),'#skF_3'(E_36,D_4,B_2,C_3,A_1),'#skF_4'(E_36,D_4,B_2,C_3,A_1)) = E_36
      | ~ m1_subset_1(E_36,k4_zfmisc_1(A_1,B_2,C_3,D_4))
      | k1_xboole_0 = D_4
      | k1_xboole_0 = C_3
      | k1_xboole_0 = B_2
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_47,plain,(
    ! [B_140,E_138,C_141,A_142,D_139] :
      ( k4_mcart_1('#skF_1'(E_138,D_139,B_140,C_141,A_142),'#skF_2'(E_138,D_139,B_140,C_141,A_142),'#skF_3'(E_138,D_139,B_140,C_141,A_142),'#skF_4'(E_138,D_139,B_140,C_141,A_142)) = E_138
      | ~ m1_subset_1(E_138,k4_zfmisc_1(A_142,B_140,C_141,D_139))
      | k1_xboole_0 = D_139
      | k1_xboole_0 = C_141
      | k1_xboole_0 = B_140
      | k1_xboole_0 = A_142 ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_14,plain,(
    ! [D_66,B_64,G_82,F_81,C_65,A_63,H_83,I_84] :
      ( k10_mcart_1(A_63,B_64,C_65,D_66,k4_mcart_1(F_81,G_82,H_83,I_84)) = H_83
      | ~ m1_subset_1(k4_mcart_1(F_81,G_82,H_83,I_84),k4_zfmisc_1(A_63,B_64,C_65,D_66))
      | k1_xboole_0 = D_66
      | k1_xboole_0 = C_65
      | k1_xboole_0 = B_64
      | k1_xboole_0 = A_63 ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_249,plain,(
    ! [C_226,A_228,B_222,C_221,E_223,D_225,D_229,B_224,A_227] :
      ( k10_mcart_1(A_227,B_224,C_221,D_229,k4_mcart_1('#skF_1'(E_223,D_225,B_222,C_226,A_228),'#skF_2'(E_223,D_225,B_222,C_226,A_228),'#skF_3'(E_223,D_225,B_222,C_226,A_228),'#skF_4'(E_223,D_225,B_222,C_226,A_228))) = '#skF_3'(E_223,D_225,B_222,C_226,A_228)
      | ~ m1_subset_1(E_223,k4_zfmisc_1(A_227,B_224,C_221,D_229))
      | k1_xboole_0 = D_229
      | k1_xboole_0 = C_221
      | k1_xboole_0 = B_224
      | k1_xboole_0 = A_227
      | ~ m1_subset_1(E_223,k4_zfmisc_1(A_228,B_222,C_226,D_225))
      | k1_xboole_0 = D_225
      | k1_xboole_0 = C_226
      | k1_xboole_0 = B_222
      | k1_xboole_0 = A_228 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_47,c_14])).

tff(c_261,plain,(
    ! [A_235,B_234,C_230,C_237,D_232,D_233,B_236,E_231,A_238] :
      ( k10_mcart_1(A_235,B_234,C_230,D_232,E_231) = '#skF_3'(E_231,D_233,B_236,C_237,A_238)
      | ~ m1_subset_1(E_231,k4_zfmisc_1(A_235,B_234,C_230,D_232))
      | k1_xboole_0 = D_232
      | k1_xboole_0 = C_230
      | k1_xboole_0 = B_234
      | k1_xboole_0 = A_235
      | ~ m1_subset_1(E_231,k4_zfmisc_1(A_238,B_236,C_237,D_233))
      | k1_xboole_0 = D_233
      | k1_xboole_0 = C_237
      | k1_xboole_0 = B_236
      | k1_xboole_0 = A_238
      | ~ m1_subset_1(E_231,k4_zfmisc_1(A_238,B_236,C_237,D_233))
      | k1_xboole_0 = D_233
      | k1_xboole_0 = C_237
      | k1_xboole_0 = B_236
      | k1_xboole_0 = A_238 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_249])).

tff(c_275,plain,(
    ! [D_233,B_236,C_237,A_238] :
      ( k10_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_9') = '#skF_3'('#skF_9',D_233,B_236,C_237,A_238)
      | k1_xboole_0 = '#skF_8'
      | k1_xboole_0 = '#skF_7'
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_5'
      | ~ m1_subset_1('#skF_9',k4_zfmisc_1(A_238,B_236,C_237,D_233))
      | k1_xboole_0 = D_233
      | k1_xboole_0 = C_237
      | k1_xboole_0 = B_236
      | k1_xboole_0 = A_238 ) ),
    inference(resolution,[status(thm)],[c_22,c_261])).

tff(c_283,plain,(
    ! [D_239,B_240,C_241,A_242] :
      ( k10_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_9') = '#skF_3'('#skF_9',D_239,B_240,C_241,A_242)
      | ~ m1_subset_1('#skF_9',k4_zfmisc_1(A_242,B_240,C_241,D_239))
      | k1_xboole_0 = D_239
      | k1_xboole_0 = C_241
      | k1_xboole_0 = B_240
      | k1_xboole_0 = A_242 ) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_28,c_26,c_24,c_275])).

tff(c_286,plain,
    ( k10_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_9') = '#skF_3'('#skF_9','#skF_8','#skF_6','#skF_7','#skF_5')
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_22,c_283])).

tff(c_289,plain,(
    k10_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_9') = '#skF_3'('#skF_9','#skF_8','#skF_6','#skF_7','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_28,c_26,c_24,c_286])).

tff(c_16,plain,(
    ! [D_66,B_64,G_82,F_81,C_65,A_63,H_83,I_84] :
      ( k9_mcart_1(A_63,B_64,C_65,D_66,k4_mcart_1(F_81,G_82,H_83,I_84)) = G_82
      | ~ m1_subset_1(k4_mcart_1(F_81,G_82,H_83,I_84),k4_zfmisc_1(A_63,B_64,C_65,D_66))
      | k1_xboole_0 = D_66
      | k1_xboole_0 = C_65
      | k1_xboole_0 = B_64
      | k1_xboole_0 = A_63 ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_182,plain,(
    ! [C_196,B_192,B_194,D_199,E_193,D_195,A_197,A_198,C_191] :
      ( k9_mcart_1(A_197,B_194,C_191,D_199,k4_mcart_1('#skF_1'(E_193,D_195,B_192,C_196,A_198),'#skF_2'(E_193,D_195,B_192,C_196,A_198),'#skF_3'(E_193,D_195,B_192,C_196,A_198),'#skF_4'(E_193,D_195,B_192,C_196,A_198))) = '#skF_2'(E_193,D_195,B_192,C_196,A_198)
      | ~ m1_subset_1(E_193,k4_zfmisc_1(A_197,B_194,C_191,D_199))
      | k1_xboole_0 = D_199
      | k1_xboole_0 = C_191
      | k1_xboole_0 = B_194
      | k1_xboole_0 = A_197
      | ~ m1_subset_1(E_193,k4_zfmisc_1(A_198,B_192,C_196,D_195))
      | k1_xboole_0 = D_195
      | k1_xboole_0 = C_196
      | k1_xboole_0 = B_192
      | k1_xboole_0 = A_198 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_47,c_16])).

tff(c_202,plain,(
    ! [B_208,B_204,E_206,D_209,C_210,D_207,C_205,A_211,A_212] :
      ( k9_mcart_1(A_212,B_204,C_205,D_209,E_206) = '#skF_2'(E_206,D_207,B_208,C_210,A_211)
      | ~ m1_subset_1(E_206,k4_zfmisc_1(A_212,B_204,C_205,D_209))
      | k1_xboole_0 = D_209
      | k1_xboole_0 = C_205
      | k1_xboole_0 = B_204
      | k1_xboole_0 = A_212
      | ~ m1_subset_1(E_206,k4_zfmisc_1(A_211,B_208,C_210,D_207))
      | k1_xboole_0 = D_207
      | k1_xboole_0 = C_210
      | k1_xboole_0 = B_208
      | k1_xboole_0 = A_211
      | ~ m1_subset_1(E_206,k4_zfmisc_1(A_211,B_208,C_210,D_207))
      | k1_xboole_0 = D_207
      | k1_xboole_0 = C_210
      | k1_xboole_0 = B_208
      | k1_xboole_0 = A_211 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_182])).

tff(c_216,plain,(
    ! [D_207,B_208,C_210,A_211] :
      ( k9_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_9') = '#skF_2'('#skF_9',D_207,B_208,C_210,A_211)
      | k1_xboole_0 = '#skF_8'
      | k1_xboole_0 = '#skF_7'
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_5'
      | ~ m1_subset_1('#skF_9',k4_zfmisc_1(A_211,B_208,C_210,D_207))
      | k1_xboole_0 = D_207
      | k1_xboole_0 = C_210
      | k1_xboole_0 = B_208
      | k1_xboole_0 = A_211 ) ),
    inference(resolution,[status(thm)],[c_22,c_202])).

tff(c_224,plain,(
    ! [D_213,B_214,C_215,A_216] :
      ( k9_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_9') = '#skF_2'('#skF_9',D_213,B_214,C_215,A_216)
      | ~ m1_subset_1('#skF_9',k4_zfmisc_1(A_216,B_214,C_215,D_213))
      | k1_xboole_0 = D_213
      | k1_xboole_0 = C_215
      | k1_xboole_0 = B_214
      | k1_xboole_0 = A_216 ) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_28,c_26,c_24,c_216])).

tff(c_227,plain,
    ( k9_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_9') = '#skF_2'('#skF_9','#skF_8','#skF_6','#skF_7','#skF_5')
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_22,c_224])).

tff(c_230,plain,(
    k9_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_9') = '#skF_2'('#skF_9','#skF_8','#skF_6','#skF_7','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_28,c_26,c_24,c_227])).

tff(c_12,plain,(
    ! [D_66,B_64,G_82,F_81,C_65,A_63,H_83,I_84] :
      ( k11_mcart_1(A_63,B_64,C_65,D_66,k4_mcart_1(F_81,G_82,H_83,I_84)) = I_84
      | ~ m1_subset_1(k4_mcart_1(F_81,G_82,H_83,I_84),k4_zfmisc_1(A_63,B_64,C_65,D_66))
      | k1_xboole_0 = D_66
      | k1_xboole_0 = C_65
      | k1_xboole_0 = B_64
      | k1_xboole_0 = A_63 ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_131,plain,(
    ! [C_169,D_173,B_172,D_177,A_176,A_175,C_174,E_171,B_170] :
      ( k11_mcart_1(A_175,B_172,C_169,D_177,k4_mcart_1('#skF_1'(E_171,D_173,B_170,C_174,A_176),'#skF_2'(E_171,D_173,B_170,C_174,A_176),'#skF_3'(E_171,D_173,B_170,C_174,A_176),'#skF_4'(E_171,D_173,B_170,C_174,A_176))) = '#skF_4'(E_171,D_173,B_170,C_174,A_176)
      | ~ m1_subset_1(E_171,k4_zfmisc_1(A_175,B_172,C_169,D_177))
      | k1_xboole_0 = D_177
      | k1_xboole_0 = C_169
      | k1_xboole_0 = B_172
      | k1_xboole_0 = A_175
      | ~ m1_subset_1(E_171,k4_zfmisc_1(A_176,B_170,C_174,D_173))
      | k1_xboole_0 = D_173
      | k1_xboole_0 = C_174
      | k1_xboole_0 = B_170
      | k1_xboole_0 = A_176 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_47,c_12])).

tff(c_143,plain,(
    ! [B_183,A_185,D_181,E_178,D_182,C_184,C_180,B_186,A_179] :
      ( k11_mcart_1(A_179,B_186,C_180,D_182,E_178) = '#skF_4'(E_178,D_181,B_183,C_184,A_185)
      | ~ m1_subset_1(E_178,k4_zfmisc_1(A_179,B_186,C_180,D_182))
      | k1_xboole_0 = D_182
      | k1_xboole_0 = C_180
      | k1_xboole_0 = B_186
      | k1_xboole_0 = A_179
      | ~ m1_subset_1(E_178,k4_zfmisc_1(A_185,B_183,C_184,D_181))
      | k1_xboole_0 = D_181
      | k1_xboole_0 = C_184
      | k1_xboole_0 = B_183
      | k1_xboole_0 = A_185
      | ~ m1_subset_1(E_178,k4_zfmisc_1(A_185,B_183,C_184,D_181))
      | k1_xboole_0 = D_181
      | k1_xboole_0 = C_184
      | k1_xboole_0 = B_183
      | k1_xboole_0 = A_185 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_131])).

tff(c_157,plain,(
    ! [D_181,B_183,C_184,A_185] :
      ( k11_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_9') = '#skF_4'('#skF_9',D_181,B_183,C_184,A_185)
      | k1_xboole_0 = '#skF_8'
      | k1_xboole_0 = '#skF_7'
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_5'
      | ~ m1_subset_1('#skF_9',k4_zfmisc_1(A_185,B_183,C_184,D_181))
      | k1_xboole_0 = D_181
      | k1_xboole_0 = C_184
      | k1_xboole_0 = B_183
      | k1_xboole_0 = A_185 ) ),
    inference(resolution,[status(thm)],[c_22,c_143])).

tff(c_165,plain,(
    ! [D_187,B_188,C_189,A_190] :
      ( k11_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_9') = '#skF_4'('#skF_9',D_187,B_188,C_189,A_190)
      | ~ m1_subset_1('#skF_9',k4_zfmisc_1(A_190,B_188,C_189,D_187))
      | k1_xboole_0 = D_187
      | k1_xboole_0 = C_189
      | k1_xboole_0 = B_188
      | k1_xboole_0 = A_190 ) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_28,c_26,c_24,c_157])).

tff(c_168,plain,
    ( k11_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_9') = '#skF_4'('#skF_9','#skF_8','#skF_6','#skF_7','#skF_5')
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_22,c_165])).

tff(c_171,plain,(
    k11_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_9') = '#skF_4'('#skF_9','#skF_8','#skF_6','#skF_7','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_28,c_26,c_24,c_168])).

tff(c_18,plain,(
    ! [D_66,B_64,G_82,F_81,C_65,A_63,H_83,I_84] :
      ( k8_mcart_1(A_63,B_64,C_65,D_66,k4_mcart_1(F_81,G_82,H_83,I_84)) = F_81
      | ~ m1_subset_1(k4_mcart_1(F_81,G_82,H_83,I_84),k4_zfmisc_1(A_63,B_64,C_65,D_66))
      | k1_xboole_0 = D_66
      | k1_xboole_0 = C_65
      | k1_xboole_0 = B_64
      | k1_xboole_0 = A_63 ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_72,plain,(
    ! [C_148,B_144,C_143,A_149,D_151,D_147,E_145,A_150,B_146] :
      ( k8_mcart_1(A_149,B_146,C_143,D_151,k4_mcart_1('#skF_1'(E_145,D_147,B_144,C_148,A_150),'#skF_2'(E_145,D_147,B_144,C_148,A_150),'#skF_3'(E_145,D_147,B_144,C_148,A_150),'#skF_4'(E_145,D_147,B_144,C_148,A_150))) = '#skF_1'(E_145,D_147,B_144,C_148,A_150)
      | ~ m1_subset_1(E_145,k4_zfmisc_1(A_149,B_146,C_143,D_151))
      | k1_xboole_0 = D_151
      | k1_xboole_0 = C_143
      | k1_xboole_0 = B_146
      | k1_xboole_0 = A_149
      | ~ m1_subset_1(E_145,k4_zfmisc_1(A_150,B_144,C_148,D_147))
      | k1_xboole_0 = D_147
      | k1_xboole_0 = C_148
      | k1_xboole_0 = B_144
      | k1_xboole_0 = A_150 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_47,c_18])).

tff(c_84,plain,(
    ! [C_154,D_155,C_159,A_160,B_156,D_152,E_153,A_157,B_158] :
      ( k8_mcart_1(A_157,B_156,C_154,D_152,E_153) = '#skF_1'(E_153,D_155,B_158,C_159,A_160)
      | ~ m1_subset_1(E_153,k4_zfmisc_1(A_157,B_156,C_154,D_152))
      | k1_xboole_0 = D_152
      | k1_xboole_0 = C_154
      | k1_xboole_0 = B_156
      | k1_xboole_0 = A_157
      | ~ m1_subset_1(E_153,k4_zfmisc_1(A_160,B_158,C_159,D_155))
      | k1_xboole_0 = D_155
      | k1_xboole_0 = C_159
      | k1_xboole_0 = B_158
      | k1_xboole_0 = A_160
      | ~ m1_subset_1(E_153,k4_zfmisc_1(A_160,B_158,C_159,D_155))
      | k1_xboole_0 = D_155
      | k1_xboole_0 = C_159
      | k1_xboole_0 = B_158
      | k1_xboole_0 = A_160 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_72])).

tff(c_98,plain,(
    ! [D_155,B_158,C_159,A_160] :
      ( k8_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_9') = '#skF_1'('#skF_9',D_155,B_158,C_159,A_160)
      | k1_xboole_0 = '#skF_8'
      | k1_xboole_0 = '#skF_7'
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_5'
      | ~ m1_subset_1('#skF_9',k4_zfmisc_1(A_160,B_158,C_159,D_155))
      | k1_xboole_0 = D_155
      | k1_xboole_0 = C_159
      | k1_xboole_0 = B_158
      | k1_xboole_0 = A_160 ) ),
    inference(resolution,[status(thm)],[c_22,c_84])).

tff(c_106,plain,(
    ! [D_161,B_162,C_163,A_164] :
      ( k8_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_9') = '#skF_1'('#skF_9',D_161,B_162,C_163,A_164)
      | ~ m1_subset_1('#skF_9',k4_zfmisc_1(A_164,B_162,C_163,D_161))
      | k1_xboole_0 = D_161
      | k1_xboole_0 = C_163
      | k1_xboole_0 = B_162
      | k1_xboole_0 = A_164 ) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_28,c_26,c_24,c_98])).

tff(c_109,plain,
    ( k8_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_9') = '#skF_1'('#skF_9','#skF_8','#skF_6','#skF_7','#skF_5')
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_22,c_106])).

tff(c_112,plain,(
    k8_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_9') = '#skF_1'('#skF_9','#skF_8','#skF_6','#skF_7','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_28,c_26,c_24,c_109])).

tff(c_20,plain,(
    k4_mcart_1(k8_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_9'),k9_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_9'),k10_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_9'),k11_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_9')) != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_114,plain,(
    k4_mcart_1('#skF_1'('#skF_9','#skF_8','#skF_6','#skF_7','#skF_5'),k9_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_9'),k10_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_9'),k11_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_9')) != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_20])).

tff(c_173,plain,(
    k4_mcart_1('#skF_1'('#skF_9','#skF_8','#skF_6','#skF_7','#skF_5'),k9_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_9'),k10_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_9'),'#skF_4'('#skF_9','#skF_8','#skF_6','#skF_7','#skF_5')) != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_171,c_114])).

tff(c_232,plain,(
    k4_mcart_1('#skF_1'('#skF_9','#skF_8','#skF_6','#skF_7','#skF_5'),'#skF_2'('#skF_9','#skF_8','#skF_6','#skF_7','#skF_5'),k10_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_9'),'#skF_4'('#skF_9','#skF_8','#skF_6','#skF_7','#skF_5')) != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_230,c_173])).

tff(c_291,plain,(
    k4_mcart_1('#skF_1'('#skF_9','#skF_8','#skF_6','#skF_7','#skF_5'),'#skF_2'('#skF_9','#skF_8','#skF_6','#skF_7','#skF_5'),'#skF_3'('#skF_9','#skF_8','#skF_6','#skF_7','#skF_5'),'#skF_4'('#skF_9','#skF_8','#skF_6','#skF_7','#skF_5')) != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_289,c_232])).

tff(c_298,plain,
    ( ~ m1_subset_1('#skF_9',k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8'))
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_291])).

tff(c_301,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_298])).

tff(c_303,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_28,c_26,c_24,c_301])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:28:41 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.85/1.42  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.85/1.42  
% 2.85/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.85/1.42  %$ m1_subset_1 > k9_mcart_1 > k8_mcart_1 > k11_mcart_1 > k10_mcart_1 > k4_zfmisc_1 > k4_mcart_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_9 > #skF_3 > #skF_1 > #skF_8
% 2.85/1.42  
% 2.85/1.42  %Foreground sorts:
% 2.85/1.42  
% 2.85/1.42  
% 2.85/1.42  %Background operators:
% 2.85/1.42  
% 2.85/1.42  
% 2.85/1.42  %Foreground operators:
% 2.85/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.85/1.42  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i) > $i).
% 2.85/1.42  tff(k10_mcart_1, type, k10_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 2.85/1.42  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.85/1.42  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i * $i) > $i).
% 2.85/1.42  tff(k4_zfmisc_1, type, k4_zfmisc_1: ($i * $i * $i * $i) > $i).
% 2.85/1.42  tff('#skF_7', type, '#skF_7': $i).
% 2.85/1.42  tff('#skF_5', type, '#skF_5': $i).
% 2.85/1.42  tff(k11_mcart_1, type, k11_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 2.85/1.42  tff('#skF_6', type, '#skF_6': $i).
% 2.85/1.42  tff('#skF_9', type, '#skF_9': $i).
% 2.85/1.42  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i * $i) > $i).
% 2.85/1.42  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i) > $i).
% 2.85/1.42  tff('#skF_8', type, '#skF_8': $i).
% 2.85/1.42  tff(k8_mcart_1, type, k8_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 2.85/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.85/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.85/1.42  tff(k9_mcart_1, type, k9_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 2.85/1.42  tff(k4_mcart_1, type, k4_mcart_1: ($i * $i * $i * $i) > $i).
% 2.85/1.42  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.85/1.42  
% 3.21/1.44  tff(f_104, negated_conjecture, ~(![A, B, C, D]: ~((((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(D = k1_xboole_0)) & ~(![E]: (m1_subset_1(E, k4_zfmisc_1(A, B, C, D)) => (E = k4_mcart_1(k8_mcart_1(A, B, C, D, E), k9_mcart_1(A, B, C, D, E), k10_mcart_1(A, B, C, D, E), k11_mcart_1(A, B, C, D, E))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_mcart_1)).
% 3.21/1.44  tff(f_56, axiom, (![A, B, C, D]: ~((((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(D = k1_xboole_0)) & (?[E]: (m1_subset_1(E, k4_zfmisc_1(A, B, C, D)) & (![F]: (m1_subset_1(F, A) => (![G]: (m1_subset_1(G, B) => (![H]: (m1_subset_1(H, C) => (![I]: (m1_subset_1(I, D) => ~(E = k4_mcart_1(F, G, H, I)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l68_mcart_1)).
% 3.21/1.44  tff(f_84, axiom, (![A, B, C, D]: ~((((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(D = k1_xboole_0)) & (?[E]: (m1_subset_1(E, k4_zfmisc_1(A, B, C, D)) & (?[F, G, H, I]: ((E = k4_mcart_1(F, G, H, I)) & ~((((k8_mcart_1(A, B, C, D, E) = F) & (k9_mcart_1(A, B, C, D, E) = G)) & (k10_mcart_1(A, B, C, D, E) = H)) & (k11_mcart_1(A, B, C, D, E) = I)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_mcart_1)).
% 3.21/1.44  tff(c_30, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.21/1.44  tff(c_28, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.21/1.44  tff(c_26, plain, (k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.21/1.44  tff(c_24, plain, (k1_xboole_0!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.21/1.44  tff(c_22, plain, (m1_subset_1('#skF_9', k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.21/1.44  tff(c_2, plain, (![B_2, C_3, A_1, D_4, E_36]: (k4_mcart_1('#skF_1'(E_36, D_4, B_2, C_3, A_1), '#skF_2'(E_36, D_4, B_2, C_3, A_1), '#skF_3'(E_36, D_4, B_2, C_3, A_1), '#skF_4'(E_36, D_4, B_2, C_3, A_1))=E_36 | ~m1_subset_1(E_36, k4_zfmisc_1(A_1, B_2, C_3, D_4)) | k1_xboole_0=D_4 | k1_xboole_0=C_3 | k1_xboole_0=B_2 | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.21/1.44  tff(c_47, plain, (![B_140, E_138, C_141, A_142, D_139]: (k4_mcart_1('#skF_1'(E_138, D_139, B_140, C_141, A_142), '#skF_2'(E_138, D_139, B_140, C_141, A_142), '#skF_3'(E_138, D_139, B_140, C_141, A_142), '#skF_4'(E_138, D_139, B_140, C_141, A_142))=E_138 | ~m1_subset_1(E_138, k4_zfmisc_1(A_142, B_140, C_141, D_139)) | k1_xboole_0=D_139 | k1_xboole_0=C_141 | k1_xboole_0=B_140 | k1_xboole_0=A_142)), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.21/1.44  tff(c_14, plain, (![D_66, B_64, G_82, F_81, C_65, A_63, H_83, I_84]: (k10_mcart_1(A_63, B_64, C_65, D_66, k4_mcart_1(F_81, G_82, H_83, I_84))=H_83 | ~m1_subset_1(k4_mcart_1(F_81, G_82, H_83, I_84), k4_zfmisc_1(A_63, B_64, C_65, D_66)) | k1_xboole_0=D_66 | k1_xboole_0=C_65 | k1_xboole_0=B_64 | k1_xboole_0=A_63)), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.21/1.44  tff(c_249, plain, (![C_226, A_228, B_222, C_221, E_223, D_225, D_229, B_224, A_227]: (k10_mcart_1(A_227, B_224, C_221, D_229, k4_mcart_1('#skF_1'(E_223, D_225, B_222, C_226, A_228), '#skF_2'(E_223, D_225, B_222, C_226, A_228), '#skF_3'(E_223, D_225, B_222, C_226, A_228), '#skF_4'(E_223, D_225, B_222, C_226, A_228)))='#skF_3'(E_223, D_225, B_222, C_226, A_228) | ~m1_subset_1(E_223, k4_zfmisc_1(A_227, B_224, C_221, D_229)) | k1_xboole_0=D_229 | k1_xboole_0=C_221 | k1_xboole_0=B_224 | k1_xboole_0=A_227 | ~m1_subset_1(E_223, k4_zfmisc_1(A_228, B_222, C_226, D_225)) | k1_xboole_0=D_225 | k1_xboole_0=C_226 | k1_xboole_0=B_222 | k1_xboole_0=A_228)), inference(superposition, [status(thm), theory('equality')], [c_47, c_14])).
% 3.21/1.44  tff(c_261, plain, (![A_235, B_234, C_230, C_237, D_232, D_233, B_236, E_231, A_238]: (k10_mcart_1(A_235, B_234, C_230, D_232, E_231)='#skF_3'(E_231, D_233, B_236, C_237, A_238) | ~m1_subset_1(E_231, k4_zfmisc_1(A_235, B_234, C_230, D_232)) | k1_xboole_0=D_232 | k1_xboole_0=C_230 | k1_xboole_0=B_234 | k1_xboole_0=A_235 | ~m1_subset_1(E_231, k4_zfmisc_1(A_238, B_236, C_237, D_233)) | k1_xboole_0=D_233 | k1_xboole_0=C_237 | k1_xboole_0=B_236 | k1_xboole_0=A_238 | ~m1_subset_1(E_231, k4_zfmisc_1(A_238, B_236, C_237, D_233)) | k1_xboole_0=D_233 | k1_xboole_0=C_237 | k1_xboole_0=B_236 | k1_xboole_0=A_238)), inference(superposition, [status(thm), theory('equality')], [c_2, c_249])).
% 3.21/1.44  tff(c_275, plain, (![D_233, B_236, C_237, A_238]: (k10_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9')='#skF_3'('#skF_9', D_233, B_236, C_237, A_238) | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | ~m1_subset_1('#skF_9', k4_zfmisc_1(A_238, B_236, C_237, D_233)) | k1_xboole_0=D_233 | k1_xboole_0=C_237 | k1_xboole_0=B_236 | k1_xboole_0=A_238)), inference(resolution, [status(thm)], [c_22, c_261])).
% 3.21/1.44  tff(c_283, plain, (![D_239, B_240, C_241, A_242]: (k10_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9')='#skF_3'('#skF_9', D_239, B_240, C_241, A_242) | ~m1_subset_1('#skF_9', k4_zfmisc_1(A_242, B_240, C_241, D_239)) | k1_xboole_0=D_239 | k1_xboole_0=C_241 | k1_xboole_0=B_240 | k1_xboole_0=A_242)), inference(negUnitSimplification, [status(thm)], [c_30, c_28, c_26, c_24, c_275])).
% 3.21/1.44  tff(c_286, plain, (k10_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9')='#skF_3'('#skF_9', '#skF_8', '#skF_6', '#skF_7', '#skF_5') | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_22, c_283])).
% 3.21/1.44  tff(c_289, plain, (k10_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9')='#skF_3'('#skF_9', '#skF_8', '#skF_6', '#skF_7', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_30, c_28, c_26, c_24, c_286])).
% 3.21/1.44  tff(c_16, plain, (![D_66, B_64, G_82, F_81, C_65, A_63, H_83, I_84]: (k9_mcart_1(A_63, B_64, C_65, D_66, k4_mcart_1(F_81, G_82, H_83, I_84))=G_82 | ~m1_subset_1(k4_mcart_1(F_81, G_82, H_83, I_84), k4_zfmisc_1(A_63, B_64, C_65, D_66)) | k1_xboole_0=D_66 | k1_xboole_0=C_65 | k1_xboole_0=B_64 | k1_xboole_0=A_63)), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.21/1.44  tff(c_182, plain, (![C_196, B_192, B_194, D_199, E_193, D_195, A_197, A_198, C_191]: (k9_mcart_1(A_197, B_194, C_191, D_199, k4_mcart_1('#skF_1'(E_193, D_195, B_192, C_196, A_198), '#skF_2'(E_193, D_195, B_192, C_196, A_198), '#skF_3'(E_193, D_195, B_192, C_196, A_198), '#skF_4'(E_193, D_195, B_192, C_196, A_198)))='#skF_2'(E_193, D_195, B_192, C_196, A_198) | ~m1_subset_1(E_193, k4_zfmisc_1(A_197, B_194, C_191, D_199)) | k1_xboole_0=D_199 | k1_xboole_0=C_191 | k1_xboole_0=B_194 | k1_xboole_0=A_197 | ~m1_subset_1(E_193, k4_zfmisc_1(A_198, B_192, C_196, D_195)) | k1_xboole_0=D_195 | k1_xboole_0=C_196 | k1_xboole_0=B_192 | k1_xboole_0=A_198)), inference(superposition, [status(thm), theory('equality')], [c_47, c_16])).
% 3.21/1.44  tff(c_202, plain, (![B_208, B_204, E_206, D_209, C_210, D_207, C_205, A_211, A_212]: (k9_mcart_1(A_212, B_204, C_205, D_209, E_206)='#skF_2'(E_206, D_207, B_208, C_210, A_211) | ~m1_subset_1(E_206, k4_zfmisc_1(A_212, B_204, C_205, D_209)) | k1_xboole_0=D_209 | k1_xboole_0=C_205 | k1_xboole_0=B_204 | k1_xboole_0=A_212 | ~m1_subset_1(E_206, k4_zfmisc_1(A_211, B_208, C_210, D_207)) | k1_xboole_0=D_207 | k1_xboole_0=C_210 | k1_xboole_0=B_208 | k1_xboole_0=A_211 | ~m1_subset_1(E_206, k4_zfmisc_1(A_211, B_208, C_210, D_207)) | k1_xboole_0=D_207 | k1_xboole_0=C_210 | k1_xboole_0=B_208 | k1_xboole_0=A_211)), inference(superposition, [status(thm), theory('equality')], [c_2, c_182])).
% 3.21/1.44  tff(c_216, plain, (![D_207, B_208, C_210, A_211]: (k9_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9')='#skF_2'('#skF_9', D_207, B_208, C_210, A_211) | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | ~m1_subset_1('#skF_9', k4_zfmisc_1(A_211, B_208, C_210, D_207)) | k1_xboole_0=D_207 | k1_xboole_0=C_210 | k1_xboole_0=B_208 | k1_xboole_0=A_211)), inference(resolution, [status(thm)], [c_22, c_202])).
% 3.21/1.44  tff(c_224, plain, (![D_213, B_214, C_215, A_216]: (k9_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9')='#skF_2'('#skF_9', D_213, B_214, C_215, A_216) | ~m1_subset_1('#skF_9', k4_zfmisc_1(A_216, B_214, C_215, D_213)) | k1_xboole_0=D_213 | k1_xboole_0=C_215 | k1_xboole_0=B_214 | k1_xboole_0=A_216)), inference(negUnitSimplification, [status(thm)], [c_30, c_28, c_26, c_24, c_216])).
% 3.21/1.44  tff(c_227, plain, (k9_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9')='#skF_2'('#skF_9', '#skF_8', '#skF_6', '#skF_7', '#skF_5') | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_22, c_224])).
% 3.21/1.44  tff(c_230, plain, (k9_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9')='#skF_2'('#skF_9', '#skF_8', '#skF_6', '#skF_7', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_30, c_28, c_26, c_24, c_227])).
% 3.21/1.44  tff(c_12, plain, (![D_66, B_64, G_82, F_81, C_65, A_63, H_83, I_84]: (k11_mcart_1(A_63, B_64, C_65, D_66, k4_mcart_1(F_81, G_82, H_83, I_84))=I_84 | ~m1_subset_1(k4_mcart_1(F_81, G_82, H_83, I_84), k4_zfmisc_1(A_63, B_64, C_65, D_66)) | k1_xboole_0=D_66 | k1_xboole_0=C_65 | k1_xboole_0=B_64 | k1_xboole_0=A_63)), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.21/1.44  tff(c_131, plain, (![C_169, D_173, B_172, D_177, A_176, A_175, C_174, E_171, B_170]: (k11_mcart_1(A_175, B_172, C_169, D_177, k4_mcart_1('#skF_1'(E_171, D_173, B_170, C_174, A_176), '#skF_2'(E_171, D_173, B_170, C_174, A_176), '#skF_3'(E_171, D_173, B_170, C_174, A_176), '#skF_4'(E_171, D_173, B_170, C_174, A_176)))='#skF_4'(E_171, D_173, B_170, C_174, A_176) | ~m1_subset_1(E_171, k4_zfmisc_1(A_175, B_172, C_169, D_177)) | k1_xboole_0=D_177 | k1_xboole_0=C_169 | k1_xboole_0=B_172 | k1_xboole_0=A_175 | ~m1_subset_1(E_171, k4_zfmisc_1(A_176, B_170, C_174, D_173)) | k1_xboole_0=D_173 | k1_xboole_0=C_174 | k1_xboole_0=B_170 | k1_xboole_0=A_176)), inference(superposition, [status(thm), theory('equality')], [c_47, c_12])).
% 3.21/1.44  tff(c_143, plain, (![B_183, A_185, D_181, E_178, D_182, C_184, C_180, B_186, A_179]: (k11_mcart_1(A_179, B_186, C_180, D_182, E_178)='#skF_4'(E_178, D_181, B_183, C_184, A_185) | ~m1_subset_1(E_178, k4_zfmisc_1(A_179, B_186, C_180, D_182)) | k1_xboole_0=D_182 | k1_xboole_0=C_180 | k1_xboole_0=B_186 | k1_xboole_0=A_179 | ~m1_subset_1(E_178, k4_zfmisc_1(A_185, B_183, C_184, D_181)) | k1_xboole_0=D_181 | k1_xboole_0=C_184 | k1_xboole_0=B_183 | k1_xboole_0=A_185 | ~m1_subset_1(E_178, k4_zfmisc_1(A_185, B_183, C_184, D_181)) | k1_xboole_0=D_181 | k1_xboole_0=C_184 | k1_xboole_0=B_183 | k1_xboole_0=A_185)), inference(superposition, [status(thm), theory('equality')], [c_2, c_131])).
% 3.21/1.44  tff(c_157, plain, (![D_181, B_183, C_184, A_185]: (k11_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9')='#skF_4'('#skF_9', D_181, B_183, C_184, A_185) | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | ~m1_subset_1('#skF_9', k4_zfmisc_1(A_185, B_183, C_184, D_181)) | k1_xboole_0=D_181 | k1_xboole_0=C_184 | k1_xboole_0=B_183 | k1_xboole_0=A_185)), inference(resolution, [status(thm)], [c_22, c_143])).
% 3.21/1.44  tff(c_165, plain, (![D_187, B_188, C_189, A_190]: (k11_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9')='#skF_4'('#skF_9', D_187, B_188, C_189, A_190) | ~m1_subset_1('#skF_9', k4_zfmisc_1(A_190, B_188, C_189, D_187)) | k1_xboole_0=D_187 | k1_xboole_0=C_189 | k1_xboole_0=B_188 | k1_xboole_0=A_190)), inference(negUnitSimplification, [status(thm)], [c_30, c_28, c_26, c_24, c_157])).
% 3.21/1.44  tff(c_168, plain, (k11_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9')='#skF_4'('#skF_9', '#skF_8', '#skF_6', '#skF_7', '#skF_5') | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_22, c_165])).
% 3.21/1.44  tff(c_171, plain, (k11_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9')='#skF_4'('#skF_9', '#skF_8', '#skF_6', '#skF_7', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_30, c_28, c_26, c_24, c_168])).
% 3.21/1.44  tff(c_18, plain, (![D_66, B_64, G_82, F_81, C_65, A_63, H_83, I_84]: (k8_mcart_1(A_63, B_64, C_65, D_66, k4_mcart_1(F_81, G_82, H_83, I_84))=F_81 | ~m1_subset_1(k4_mcart_1(F_81, G_82, H_83, I_84), k4_zfmisc_1(A_63, B_64, C_65, D_66)) | k1_xboole_0=D_66 | k1_xboole_0=C_65 | k1_xboole_0=B_64 | k1_xboole_0=A_63)), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.21/1.44  tff(c_72, plain, (![C_148, B_144, C_143, A_149, D_151, D_147, E_145, A_150, B_146]: (k8_mcart_1(A_149, B_146, C_143, D_151, k4_mcart_1('#skF_1'(E_145, D_147, B_144, C_148, A_150), '#skF_2'(E_145, D_147, B_144, C_148, A_150), '#skF_3'(E_145, D_147, B_144, C_148, A_150), '#skF_4'(E_145, D_147, B_144, C_148, A_150)))='#skF_1'(E_145, D_147, B_144, C_148, A_150) | ~m1_subset_1(E_145, k4_zfmisc_1(A_149, B_146, C_143, D_151)) | k1_xboole_0=D_151 | k1_xboole_0=C_143 | k1_xboole_0=B_146 | k1_xboole_0=A_149 | ~m1_subset_1(E_145, k4_zfmisc_1(A_150, B_144, C_148, D_147)) | k1_xboole_0=D_147 | k1_xboole_0=C_148 | k1_xboole_0=B_144 | k1_xboole_0=A_150)), inference(superposition, [status(thm), theory('equality')], [c_47, c_18])).
% 3.21/1.44  tff(c_84, plain, (![C_154, D_155, C_159, A_160, B_156, D_152, E_153, A_157, B_158]: (k8_mcart_1(A_157, B_156, C_154, D_152, E_153)='#skF_1'(E_153, D_155, B_158, C_159, A_160) | ~m1_subset_1(E_153, k4_zfmisc_1(A_157, B_156, C_154, D_152)) | k1_xboole_0=D_152 | k1_xboole_0=C_154 | k1_xboole_0=B_156 | k1_xboole_0=A_157 | ~m1_subset_1(E_153, k4_zfmisc_1(A_160, B_158, C_159, D_155)) | k1_xboole_0=D_155 | k1_xboole_0=C_159 | k1_xboole_0=B_158 | k1_xboole_0=A_160 | ~m1_subset_1(E_153, k4_zfmisc_1(A_160, B_158, C_159, D_155)) | k1_xboole_0=D_155 | k1_xboole_0=C_159 | k1_xboole_0=B_158 | k1_xboole_0=A_160)), inference(superposition, [status(thm), theory('equality')], [c_2, c_72])).
% 3.21/1.44  tff(c_98, plain, (![D_155, B_158, C_159, A_160]: (k8_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9')='#skF_1'('#skF_9', D_155, B_158, C_159, A_160) | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | ~m1_subset_1('#skF_9', k4_zfmisc_1(A_160, B_158, C_159, D_155)) | k1_xboole_0=D_155 | k1_xboole_0=C_159 | k1_xboole_0=B_158 | k1_xboole_0=A_160)), inference(resolution, [status(thm)], [c_22, c_84])).
% 3.21/1.44  tff(c_106, plain, (![D_161, B_162, C_163, A_164]: (k8_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9')='#skF_1'('#skF_9', D_161, B_162, C_163, A_164) | ~m1_subset_1('#skF_9', k4_zfmisc_1(A_164, B_162, C_163, D_161)) | k1_xboole_0=D_161 | k1_xboole_0=C_163 | k1_xboole_0=B_162 | k1_xboole_0=A_164)), inference(negUnitSimplification, [status(thm)], [c_30, c_28, c_26, c_24, c_98])).
% 3.21/1.44  tff(c_109, plain, (k8_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9')='#skF_1'('#skF_9', '#skF_8', '#skF_6', '#skF_7', '#skF_5') | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_22, c_106])).
% 3.21/1.44  tff(c_112, plain, (k8_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9')='#skF_1'('#skF_9', '#skF_8', '#skF_6', '#skF_7', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_30, c_28, c_26, c_24, c_109])).
% 3.21/1.44  tff(c_20, plain, (k4_mcart_1(k8_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9'), k9_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9'), k10_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9'), k11_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9'))!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.21/1.44  tff(c_114, plain, (k4_mcart_1('#skF_1'('#skF_9', '#skF_8', '#skF_6', '#skF_7', '#skF_5'), k9_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9'), k10_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9'), k11_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9'))!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_112, c_20])).
% 3.21/1.44  tff(c_173, plain, (k4_mcart_1('#skF_1'('#skF_9', '#skF_8', '#skF_6', '#skF_7', '#skF_5'), k9_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9'), k10_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9'), '#skF_4'('#skF_9', '#skF_8', '#skF_6', '#skF_7', '#skF_5'))!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_171, c_114])).
% 3.21/1.44  tff(c_232, plain, (k4_mcart_1('#skF_1'('#skF_9', '#skF_8', '#skF_6', '#skF_7', '#skF_5'), '#skF_2'('#skF_9', '#skF_8', '#skF_6', '#skF_7', '#skF_5'), k10_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9'), '#skF_4'('#skF_9', '#skF_8', '#skF_6', '#skF_7', '#skF_5'))!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_230, c_173])).
% 3.21/1.44  tff(c_291, plain, (k4_mcart_1('#skF_1'('#skF_9', '#skF_8', '#skF_6', '#skF_7', '#skF_5'), '#skF_2'('#skF_9', '#skF_8', '#skF_6', '#skF_7', '#skF_5'), '#skF_3'('#skF_9', '#skF_8', '#skF_6', '#skF_7', '#skF_5'), '#skF_4'('#skF_9', '#skF_8', '#skF_6', '#skF_7', '#skF_5'))!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_289, c_232])).
% 3.21/1.44  tff(c_298, plain, (~m1_subset_1('#skF_9', k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')) | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_2, c_291])).
% 3.21/1.44  tff(c_301, plain, (k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_22, c_298])).
% 3.21/1.44  tff(c_303, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_28, c_26, c_24, c_301])).
% 3.21/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.21/1.44  
% 3.21/1.44  Inference rules
% 3.21/1.44  ----------------------
% 3.21/1.44  #Ref     : 0
% 3.21/1.44  #Sup     : 54
% 3.21/1.44  #Fact    : 0
% 3.21/1.44  #Define  : 0
% 3.21/1.44  #Split   : 0
% 3.21/1.44  #Chain   : 0
% 3.21/1.44  #Close   : 0
% 3.21/1.44  
% 3.21/1.44  Ordering : KBO
% 3.21/1.44  
% 3.21/1.44  Simplification rules
% 3.21/1.44  ----------------------
% 3.21/1.44  #Subsume      : 0
% 3.21/1.44  #Demod        : 9
% 3.21/1.44  #Tautology    : 21
% 3.21/1.44  #SimpNegUnit  : 12
% 3.21/1.44  #BackRed      : 8
% 3.21/1.44  
% 3.21/1.44  #Partial instantiations: 0
% 3.21/1.44  #Strategies tried      : 1
% 3.21/1.44  
% 3.21/1.44  Timing (in seconds)
% 3.21/1.44  ----------------------
% 3.21/1.44  Preprocessing        : 0.32
% 3.21/1.44  Parsing              : 0.16
% 3.21/1.44  CNF conversion       : 0.03
% 3.21/1.44  Main loop            : 0.30
% 3.21/1.45  Inferencing          : 0.14
% 3.21/1.45  Reduction            : 0.06
% 3.21/1.45  Demodulation         : 0.04
% 3.21/1.45  BG Simplification    : 0.02
% 3.21/1.45  Subsumption          : 0.06
% 3.21/1.45  Abstraction          : 0.03
% 3.21/1.45  MUC search           : 0.00
% 3.21/1.45  Cooper               : 0.00
% 3.21/1.45  Total                : 0.66
% 3.21/1.45  Index Insertion      : 0.00
% 3.21/1.45  Index Deletion       : 0.00
% 3.21/1.45  Index Matching       : 0.00
% 3.21/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
