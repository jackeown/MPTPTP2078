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
% DateTime   : Thu Dec  3 10:10:15 EST 2020

% Result     : Theorem 2.67s
% Output     : CNFRefutation 2.67s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 183 expanded)
%              Number of leaves         :   29 (  86 expanded)
%              Depth                    :    7
%              Number of atoms          :  164 ( 835 expanded)
%              Number of equality atoms :  143 ( 747 expanded)
%              Maximal formula depth    :   22 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > k9_mcart_1 > k8_mcart_1 > k11_mcart_1 > k10_mcart_1 > k4_zfmisc_1 > k4_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_9 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k10_mcart_1,type,(
    k10_mcart_1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff(k8_mcart_1,type,(
    k8_mcart_1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(k9_mcart_1,type,(
    k9_mcart_1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k4_mcart_1,type,(
    k4_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_110,negated_conjecture,(
    ~ ! [A,B,C,D,E] :
        ( m1_subset_1(E,k4_zfmisc_1(A,B,C,D))
       => ~ ( A != k1_xboole_0
            & B != k1_xboole_0
            & C != k1_xboole_0
            & D != k1_xboole_0
            & ? [F,G,H,I] :
                ( E = k4_mcart_1(F,G,H,I)
                & ~ ( k8_mcart_1(A,B,C,D,E) = F
                    & k9_mcart_1(A,B,C,D,E) = G
                    & k10_mcart_1(A,B,C,D,E) = H
                    & k11_mcart_1(A,B,C,D,E) = I ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_mcart_1)).

tff(f_82,axiom,(
    ! [A,B,C,D] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & D != k1_xboole_0
        & ~ ! [E] :
              ( m1_subset_1(E,k4_zfmisc_1(A,B,C,D))
             => ( k8_mcart_1(A,B,C,D,E) = k1_mcart_1(k1_mcart_1(k1_mcart_1(E)))
                & k9_mcart_1(A,B,C,D,E) = k2_mcart_1(k1_mcart_1(k1_mcart_1(E)))
                & k10_mcart_1(A,B,C,D,E) = k2_mcart_1(k1_mcart_1(E))
                & k11_mcart_1(A,B,C,D,E) = k2_mcart_1(E) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_mcart_1)).

tff(f_57,axiom,(
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

tff(c_32,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_30,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_28,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_26,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_34,plain,(
    m1_subset_1('#skF_5',k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_57,plain,(
    ! [E_51,D_49,B_50,A_52,C_53] :
      ( k11_mcart_1(A_52,B_50,C_53,D_49,E_51) = k2_mcart_1(E_51)
      | ~ m1_subset_1(E_51,k4_zfmisc_1(A_52,B_50,C_53,D_49))
      | k1_xboole_0 = D_49
      | k1_xboole_0 = C_53
      | k1_xboole_0 = B_50
      | k1_xboole_0 = A_52 ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_60,plain,
    ( k11_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') = k2_mcart_1('#skF_5')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_34,c_57])).

tff(c_63,plain,(
    k11_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') = k2_mcart_1('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_30,c_28,c_26,c_60])).

tff(c_22,plain,
    ( k11_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') != '#skF_9'
    | k10_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') != '#skF_8'
    | k9_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') != '#skF_7'
    | k8_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_64,plain,(
    k8_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_22])).

tff(c_24,plain,(
    k4_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9') = '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_163,plain,(
    ! [G_107,A_112,I_111,H_108,F_105,C_109,D_110,B_106] :
      ( k8_mcart_1(A_112,B_106,C_109,D_110,k4_mcart_1(F_105,G_107,H_108,I_111)) = F_105
      | ~ m1_subset_1(k4_mcart_1(F_105,G_107,H_108,I_111),k4_zfmisc_1(A_112,B_106,C_109,D_110))
      | k1_xboole_0 = D_110
      | k1_xboole_0 = C_109
      | k1_xboole_0 = B_106
      | k1_xboole_0 = A_112 ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_166,plain,(
    ! [A_112,B_106,C_109,D_110] :
      ( k8_mcart_1(A_112,B_106,C_109,D_110,k4_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9')) = '#skF_6'
      | ~ m1_subset_1('#skF_5',k4_zfmisc_1(A_112,B_106,C_109,D_110))
      | k1_xboole_0 = D_110
      | k1_xboole_0 = C_109
      | k1_xboole_0 = B_106
      | k1_xboole_0 = A_112 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_163])).

tff(c_168,plain,(
    ! [A_113,B_114,C_115,D_116] :
      ( k8_mcart_1(A_113,B_114,C_115,D_116,'#skF_5') = '#skF_6'
      | ~ m1_subset_1('#skF_5',k4_zfmisc_1(A_113,B_114,C_115,D_116))
      | k1_xboole_0 = D_116
      | k1_xboole_0 = C_115
      | k1_xboole_0 = B_114
      | k1_xboole_0 = A_113 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_166])).

tff(c_171,plain,
    ( k8_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') = '#skF_6'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_34,c_168])).

tff(c_175,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_30,c_28,c_26,c_64,c_171])).

tff(c_176,plain,
    ( k9_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') != '#skF_7'
    | k10_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') != '#skF_8'
    | k11_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') != '#skF_9' ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_186,plain,
    ( k9_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') != '#skF_7'
    | k10_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') != '#skF_8'
    | k2_mcart_1('#skF_5') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_176])).

tff(c_187,plain,(
    k2_mcart_1('#skF_5') != '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_186])).

tff(c_236,plain,(
    ! [C_148,D_149,H_147,G_146,I_150,F_144,B_145,A_151] :
      ( k11_mcart_1(A_151,B_145,C_148,D_149,k4_mcart_1(F_144,G_146,H_147,I_150)) = I_150
      | ~ m1_subset_1(k4_mcart_1(F_144,G_146,H_147,I_150),k4_zfmisc_1(A_151,B_145,C_148,D_149))
      | k1_xboole_0 = D_149
      | k1_xboole_0 = C_148
      | k1_xboole_0 = B_145
      | k1_xboole_0 = A_151 ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_239,plain,(
    ! [A_151,B_145,C_148,D_149] :
      ( k11_mcart_1(A_151,B_145,C_148,D_149,k4_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9')) = '#skF_9'
      | ~ m1_subset_1('#skF_5',k4_zfmisc_1(A_151,B_145,C_148,D_149))
      | k1_xboole_0 = D_149
      | k1_xboole_0 = C_148
      | k1_xboole_0 = B_145
      | k1_xboole_0 = A_151 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_236])).

tff(c_245,plain,(
    ! [A_152,B_153,C_154,D_155] :
      ( k11_mcart_1(A_152,B_153,C_154,D_155,'#skF_5') = '#skF_9'
      | ~ m1_subset_1('#skF_5',k4_zfmisc_1(A_152,B_153,C_154,D_155))
      | k1_xboole_0 = D_155
      | k1_xboole_0 = C_154
      | k1_xboole_0 = B_153
      | k1_xboole_0 = A_152 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_239])).

tff(c_248,plain,
    ( k11_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') = '#skF_9'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_34,c_245])).

tff(c_250,plain,
    ( k2_mcart_1('#skF_5') = '#skF_9'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_248])).

tff(c_252,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_30,c_28,c_26,c_187,c_250])).

tff(c_253,plain,
    ( k10_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') != '#skF_8'
    | k9_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_186])).

tff(c_264,plain,(
    k9_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_253])).

tff(c_334,plain,(
    ! [B_204,F_203,D_208,I_209,A_210,C_207,H_206,G_205] :
      ( k9_mcart_1(A_210,B_204,C_207,D_208,k4_mcart_1(F_203,G_205,H_206,I_209)) = G_205
      | ~ m1_subset_1(k4_mcart_1(F_203,G_205,H_206,I_209),k4_zfmisc_1(A_210,B_204,C_207,D_208))
      | k1_xboole_0 = D_208
      | k1_xboole_0 = C_207
      | k1_xboole_0 = B_204
      | k1_xboole_0 = A_210 ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_337,plain,(
    ! [A_210,B_204,C_207,D_208] :
      ( k9_mcart_1(A_210,B_204,C_207,D_208,k4_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9')) = '#skF_7'
      | ~ m1_subset_1('#skF_5',k4_zfmisc_1(A_210,B_204,C_207,D_208))
      | k1_xboole_0 = D_208
      | k1_xboole_0 = C_207
      | k1_xboole_0 = B_204
      | k1_xboole_0 = A_210 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_334])).

tff(c_346,plain,(
    ! [A_215,B_216,C_217,D_218] :
      ( k9_mcart_1(A_215,B_216,C_217,D_218,'#skF_5') = '#skF_7'
      | ~ m1_subset_1('#skF_5',k4_zfmisc_1(A_215,B_216,C_217,D_218))
      | k1_xboole_0 = D_218
      | k1_xboole_0 = C_217
      | k1_xboole_0 = B_216
      | k1_xboole_0 = A_215 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_337])).

tff(c_349,plain,
    ( k9_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') = '#skF_7'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_34,c_346])).

tff(c_353,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_30,c_28,c_26,c_264,c_349])).

tff(c_354,plain,(
    k10_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_253])).

tff(c_427,plain,(
    ! [H_273,A_277,C_274,G_272,D_275,F_270,I_276,B_271] :
      ( k10_mcart_1(A_277,B_271,C_274,D_275,k4_mcart_1(F_270,G_272,H_273,I_276)) = H_273
      | ~ m1_subset_1(k4_mcart_1(F_270,G_272,H_273,I_276),k4_zfmisc_1(A_277,B_271,C_274,D_275))
      | k1_xboole_0 = D_275
      | k1_xboole_0 = C_274
      | k1_xboole_0 = B_271
      | k1_xboole_0 = A_277 ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_430,plain,(
    ! [A_277,B_271,C_274,D_275] :
      ( k10_mcart_1(A_277,B_271,C_274,D_275,k4_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9')) = '#skF_8'
      | ~ m1_subset_1('#skF_5',k4_zfmisc_1(A_277,B_271,C_274,D_275))
      | k1_xboole_0 = D_275
      | k1_xboole_0 = C_274
      | k1_xboole_0 = B_271
      | k1_xboole_0 = A_277 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_427])).

tff(c_432,plain,(
    ! [A_278,B_279,C_280,D_281] :
      ( k10_mcart_1(A_278,B_279,C_280,D_281,'#skF_5') = '#skF_8'
      | ~ m1_subset_1('#skF_5',k4_zfmisc_1(A_278,B_279,C_280,D_281))
      | k1_xboole_0 = D_281
      | k1_xboole_0 = C_280
      | k1_xboole_0 = B_279
      | k1_xboole_0 = A_278 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_430])).

tff(c_435,plain,
    ( k10_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') = '#skF_8'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_34,c_432])).

tff(c_439,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_30,c_28,c_26,c_354,c_435])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:34:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.67/1.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.67/1.33  
% 2.67/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.67/1.33  %$ m1_subset_1 > k9_mcart_1 > k8_mcart_1 > k11_mcart_1 > k10_mcart_1 > k4_zfmisc_1 > k4_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_9 > #skF_8 > #skF_4
% 2.67/1.33  
% 2.67/1.33  %Foreground sorts:
% 2.67/1.33  
% 2.67/1.33  
% 2.67/1.33  %Background operators:
% 2.67/1.33  
% 2.67/1.33  
% 2.67/1.33  %Foreground operators:
% 2.67/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.67/1.33  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.67/1.33  tff(k10_mcart_1, type, k10_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 2.67/1.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.67/1.33  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 2.67/1.33  tff(k4_zfmisc_1, type, k4_zfmisc_1: ($i * $i * $i * $i) > $i).
% 2.67/1.33  tff('#skF_7', type, '#skF_7': $i).
% 2.67/1.33  tff('#skF_5', type, '#skF_5': $i).
% 2.67/1.33  tff(k11_mcart_1, type, k11_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 2.67/1.33  tff('#skF_6', type, '#skF_6': $i).
% 2.67/1.33  tff('#skF_2', type, '#skF_2': $i).
% 2.67/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.67/1.33  tff('#skF_1', type, '#skF_1': $i).
% 2.67/1.33  tff('#skF_9', type, '#skF_9': $i).
% 2.67/1.33  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 2.67/1.33  tff('#skF_8', type, '#skF_8': $i).
% 2.67/1.33  tff(k8_mcart_1, type, k8_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 2.67/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.67/1.33  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.67/1.33  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.67/1.33  tff('#skF_4', type, '#skF_4': $i).
% 2.67/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.67/1.33  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.67/1.33  tff(k9_mcart_1, type, k9_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 2.67/1.33  tff(k4_mcart_1, type, k4_mcart_1: ($i * $i * $i * $i) > $i).
% 2.67/1.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.67/1.33  
% 2.67/1.35  tff(f_110, negated_conjecture, ~(![A, B, C, D, E]: (m1_subset_1(E, k4_zfmisc_1(A, B, C, D)) => ~((((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(D = k1_xboole_0)) & (?[F, G, H, I]: ((E = k4_mcart_1(F, G, H, I)) & ~((((k8_mcart_1(A, B, C, D, E) = F) & (k9_mcart_1(A, B, C, D, E) = G)) & (k10_mcart_1(A, B, C, D, E) = H)) & (k11_mcart_1(A, B, C, D, E) = I))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_mcart_1)).
% 2.67/1.35  tff(f_82, axiom, (![A, B, C, D]: ~((((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(D = k1_xboole_0)) & ~(![E]: (m1_subset_1(E, k4_zfmisc_1(A, B, C, D)) => ((((k8_mcart_1(A, B, C, D, E) = k1_mcart_1(k1_mcart_1(k1_mcart_1(E)))) & (k9_mcart_1(A, B, C, D, E) = k2_mcart_1(k1_mcart_1(k1_mcart_1(E))))) & (k10_mcart_1(A, B, C, D, E) = k2_mcart_1(k1_mcart_1(E)))) & (k11_mcart_1(A, B, C, D, E) = k2_mcart_1(E))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_mcart_1)).
% 2.67/1.35  tff(f_57, axiom, (![A, B, C, D]: ~((((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(D = k1_xboole_0)) & (?[E]: (m1_subset_1(E, k4_zfmisc_1(A, B, C, D)) & (?[F, G, H, I]: ((E = k4_mcart_1(F, G, H, I)) & ~((((k8_mcart_1(A, B, C, D, E) = F) & (k9_mcart_1(A, B, C, D, E) = G)) & (k10_mcart_1(A, B, C, D, E) = H)) & (k11_mcart_1(A, B, C, D, E) = I)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_mcart_1)).
% 2.67/1.35  tff(c_32, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.67/1.35  tff(c_30, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.67/1.35  tff(c_28, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.67/1.35  tff(c_26, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.67/1.35  tff(c_34, plain, (m1_subset_1('#skF_5', k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.67/1.35  tff(c_57, plain, (![E_51, D_49, B_50, A_52, C_53]: (k11_mcart_1(A_52, B_50, C_53, D_49, E_51)=k2_mcart_1(E_51) | ~m1_subset_1(E_51, k4_zfmisc_1(A_52, B_50, C_53, D_49)) | k1_xboole_0=D_49 | k1_xboole_0=C_53 | k1_xboole_0=B_50 | k1_xboole_0=A_52)), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.67/1.35  tff(c_60, plain, (k11_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k2_mcart_1('#skF_5') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_34, c_57])).
% 2.67/1.35  tff(c_63, plain, (k11_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k2_mcart_1('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_32, c_30, c_28, c_26, c_60])).
% 2.67/1.35  tff(c_22, plain, (k11_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')!='#skF_9' | k10_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')!='#skF_8' | k9_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')!='#skF_7' | k8_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.67/1.35  tff(c_64, plain, (k8_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')!='#skF_6'), inference(splitLeft, [status(thm)], [c_22])).
% 2.67/1.35  tff(c_24, plain, (k4_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9')='#skF_5'), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.67/1.35  tff(c_163, plain, (![G_107, A_112, I_111, H_108, F_105, C_109, D_110, B_106]: (k8_mcart_1(A_112, B_106, C_109, D_110, k4_mcart_1(F_105, G_107, H_108, I_111))=F_105 | ~m1_subset_1(k4_mcart_1(F_105, G_107, H_108, I_111), k4_zfmisc_1(A_112, B_106, C_109, D_110)) | k1_xboole_0=D_110 | k1_xboole_0=C_109 | k1_xboole_0=B_106 | k1_xboole_0=A_112)), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.67/1.35  tff(c_166, plain, (![A_112, B_106, C_109, D_110]: (k8_mcart_1(A_112, B_106, C_109, D_110, k4_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'))='#skF_6' | ~m1_subset_1('#skF_5', k4_zfmisc_1(A_112, B_106, C_109, D_110)) | k1_xboole_0=D_110 | k1_xboole_0=C_109 | k1_xboole_0=B_106 | k1_xboole_0=A_112)), inference(superposition, [status(thm), theory('equality')], [c_24, c_163])).
% 2.67/1.35  tff(c_168, plain, (![A_113, B_114, C_115, D_116]: (k8_mcart_1(A_113, B_114, C_115, D_116, '#skF_5')='#skF_6' | ~m1_subset_1('#skF_5', k4_zfmisc_1(A_113, B_114, C_115, D_116)) | k1_xboole_0=D_116 | k1_xboole_0=C_115 | k1_xboole_0=B_114 | k1_xboole_0=A_113)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_166])).
% 2.67/1.35  tff(c_171, plain, (k8_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')='#skF_6' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_34, c_168])).
% 2.67/1.35  tff(c_175, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_30, c_28, c_26, c_64, c_171])).
% 2.67/1.35  tff(c_176, plain, (k9_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')!='#skF_7' | k10_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')!='#skF_8' | k11_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')!='#skF_9'), inference(splitRight, [status(thm)], [c_22])).
% 2.67/1.35  tff(c_186, plain, (k9_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')!='#skF_7' | k10_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')!='#skF_8' | k2_mcart_1('#skF_5')!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_63, c_176])).
% 2.67/1.35  tff(c_187, plain, (k2_mcart_1('#skF_5')!='#skF_9'), inference(splitLeft, [status(thm)], [c_186])).
% 2.67/1.35  tff(c_236, plain, (![C_148, D_149, H_147, G_146, I_150, F_144, B_145, A_151]: (k11_mcart_1(A_151, B_145, C_148, D_149, k4_mcart_1(F_144, G_146, H_147, I_150))=I_150 | ~m1_subset_1(k4_mcart_1(F_144, G_146, H_147, I_150), k4_zfmisc_1(A_151, B_145, C_148, D_149)) | k1_xboole_0=D_149 | k1_xboole_0=C_148 | k1_xboole_0=B_145 | k1_xboole_0=A_151)), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.67/1.35  tff(c_239, plain, (![A_151, B_145, C_148, D_149]: (k11_mcart_1(A_151, B_145, C_148, D_149, k4_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'))='#skF_9' | ~m1_subset_1('#skF_5', k4_zfmisc_1(A_151, B_145, C_148, D_149)) | k1_xboole_0=D_149 | k1_xboole_0=C_148 | k1_xboole_0=B_145 | k1_xboole_0=A_151)), inference(superposition, [status(thm), theory('equality')], [c_24, c_236])).
% 2.67/1.35  tff(c_245, plain, (![A_152, B_153, C_154, D_155]: (k11_mcart_1(A_152, B_153, C_154, D_155, '#skF_5')='#skF_9' | ~m1_subset_1('#skF_5', k4_zfmisc_1(A_152, B_153, C_154, D_155)) | k1_xboole_0=D_155 | k1_xboole_0=C_154 | k1_xboole_0=B_153 | k1_xboole_0=A_152)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_239])).
% 2.67/1.35  tff(c_248, plain, (k11_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')='#skF_9' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_34, c_245])).
% 2.67/1.35  tff(c_250, plain, (k2_mcart_1('#skF_5')='#skF_9' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_63, c_248])).
% 2.67/1.35  tff(c_252, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_30, c_28, c_26, c_187, c_250])).
% 2.67/1.35  tff(c_253, plain, (k10_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')!='#skF_8' | k9_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')!='#skF_7'), inference(splitRight, [status(thm)], [c_186])).
% 2.67/1.35  tff(c_264, plain, (k9_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')!='#skF_7'), inference(splitLeft, [status(thm)], [c_253])).
% 2.67/1.35  tff(c_334, plain, (![B_204, F_203, D_208, I_209, A_210, C_207, H_206, G_205]: (k9_mcart_1(A_210, B_204, C_207, D_208, k4_mcart_1(F_203, G_205, H_206, I_209))=G_205 | ~m1_subset_1(k4_mcart_1(F_203, G_205, H_206, I_209), k4_zfmisc_1(A_210, B_204, C_207, D_208)) | k1_xboole_0=D_208 | k1_xboole_0=C_207 | k1_xboole_0=B_204 | k1_xboole_0=A_210)), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.67/1.35  tff(c_337, plain, (![A_210, B_204, C_207, D_208]: (k9_mcart_1(A_210, B_204, C_207, D_208, k4_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'))='#skF_7' | ~m1_subset_1('#skF_5', k4_zfmisc_1(A_210, B_204, C_207, D_208)) | k1_xboole_0=D_208 | k1_xboole_0=C_207 | k1_xboole_0=B_204 | k1_xboole_0=A_210)), inference(superposition, [status(thm), theory('equality')], [c_24, c_334])).
% 2.67/1.35  tff(c_346, plain, (![A_215, B_216, C_217, D_218]: (k9_mcart_1(A_215, B_216, C_217, D_218, '#skF_5')='#skF_7' | ~m1_subset_1('#skF_5', k4_zfmisc_1(A_215, B_216, C_217, D_218)) | k1_xboole_0=D_218 | k1_xboole_0=C_217 | k1_xboole_0=B_216 | k1_xboole_0=A_215)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_337])).
% 2.67/1.35  tff(c_349, plain, (k9_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')='#skF_7' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_34, c_346])).
% 2.67/1.35  tff(c_353, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_30, c_28, c_26, c_264, c_349])).
% 2.67/1.35  tff(c_354, plain, (k10_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')!='#skF_8'), inference(splitRight, [status(thm)], [c_253])).
% 2.67/1.35  tff(c_427, plain, (![H_273, A_277, C_274, G_272, D_275, F_270, I_276, B_271]: (k10_mcart_1(A_277, B_271, C_274, D_275, k4_mcart_1(F_270, G_272, H_273, I_276))=H_273 | ~m1_subset_1(k4_mcart_1(F_270, G_272, H_273, I_276), k4_zfmisc_1(A_277, B_271, C_274, D_275)) | k1_xboole_0=D_275 | k1_xboole_0=C_274 | k1_xboole_0=B_271 | k1_xboole_0=A_277)), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.67/1.35  tff(c_430, plain, (![A_277, B_271, C_274, D_275]: (k10_mcart_1(A_277, B_271, C_274, D_275, k4_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'))='#skF_8' | ~m1_subset_1('#skF_5', k4_zfmisc_1(A_277, B_271, C_274, D_275)) | k1_xboole_0=D_275 | k1_xboole_0=C_274 | k1_xboole_0=B_271 | k1_xboole_0=A_277)), inference(superposition, [status(thm), theory('equality')], [c_24, c_427])).
% 2.67/1.35  tff(c_432, plain, (![A_278, B_279, C_280, D_281]: (k10_mcart_1(A_278, B_279, C_280, D_281, '#skF_5')='#skF_8' | ~m1_subset_1('#skF_5', k4_zfmisc_1(A_278, B_279, C_280, D_281)) | k1_xboole_0=D_281 | k1_xboole_0=C_280 | k1_xboole_0=B_279 | k1_xboole_0=A_278)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_430])).
% 2.67/1.35  tff(c_435, plain, (k10_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')='#skF_8' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_34, c_432])).
% 2.67/1.35  tff(c_439, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_30, c_28, c_26, c_354, c_435])).
% 2.67/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.67/1.35  
% 2.67/1.35  Inference rules
% 2.67/1.35  ----------------------
% 2.67/1.35  #Ref     : 0
% 2.67/1.35  #Sup     : 103
% 2.67/1.35  #Fact    : 0
% 2.67/1.35  #Define  : 0
% 2.67/1.35  #Split   : 3
% 2.67/1.35  #Chain   : 0
% 2.67/1.35  #Close   : 0
% 2.67/1.35  
% 2.67/1.35  Ordering : KBO
% 2.67/1.35  
% 2.67/1.35  Simplification rules
% 2.67/1.35  ----------------------
% 2.67/1.35  #Subsume      : 0
% 2.67/1.35  #Demod        : 32
% 2.67/1.35  #Tautology    : 67
% 2.67/1.35  #SimpNegUnit  : 27
% 2.67/1.35  #BackRed      : 6
% 2.67/1.35  
% 2.67/1.35  #Partial instantiations: 0
% 2.67/1.35  #Strategies tried      : 1
% 2.67/1.35  
% 2.67/1.35  Timing (in seconds)
% 2.67/1.35  ----------------------
% 2.67/1.35  Preprocessing        : 0.32
% 2.67/1.35  Parsing              : 0.16
% 2.67/1.35  CNF conversion       : 0.02
% 2.67/1.35  Main loop            : 0.26
% 2.67/1.35  Inferencing          : 0.11
% 2.67/1.35  Reduction            : 0.08
% 2.67/1.35  Demodulation         : 0.05
% 2.67/1.35  BG Simplification    : 0.02
% 2.67/1.35  Subsumption          : 0.02
% 2.67/1.35  Abstraction          : 0.02
% 2.67/1.35  MUC search           : 0.00
% 2.67/1.35  Cooper               : 0.00
% 2.67/1.35  Total                : 0.61
% 2.67/1.35  Index Insertion      : 0.00
% 2.67/1.35  Index Deletion       : 0.00
% 2.67/1.35  Index Matching       : 0.00
% 2.67/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
