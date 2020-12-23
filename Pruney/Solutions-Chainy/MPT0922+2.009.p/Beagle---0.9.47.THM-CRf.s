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
% DateTime   : Thu Dec  3 10:10:20 EST 2020

% Result     : Theorem 3.15s
% Output     : CNFRefutation 3.38s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 141 expanded)
%              Number of leaves         :   28 (  70 expanded)
%              Depth                    :   12
%              Number of atoms          :  210 ( 743 expanded)
%              Number of equality atoms :  153 ( 475 expanded)
%              Maximal formula depth    :   21 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > k9_mcart_1 > k8_mcart_1 > k11_mcart_1 > k10_mcart_1 > k4_zfmisc_1 > k4_mcart_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_4 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_9 > #skF_3 > #skF_1 > #skF_8

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

tff('#skF_10',type,(
    '#skF_10': $i )).

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

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

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

tff(f_139,negated_conjecture,(
    ~ ! [A,B,C,D,E,F] :
        ( m1_subset_1(F,k4_zfmisc_1(A,B,C,D))
       => ( ! [G] :
              ( m1_subset_1(G,A)
             => ! [H] :
                  ( m1_subset_1(H,B)
                 => ! [I] :
                      ( m1_subset_1(I,C)
                     => ! [J] :
                          ( m1_subset_1(J,D)
                         => ( F = k4_mcart_1(G,H,I,J)
                           => E = J ) ) ) ) )
         => ( A = k1_xboole_0
            | B = k1_xboole_0
            | C = k1_xboole_0
            | D = k1_xboole_0
            | E = k11_mcart_1(A,B,C,D,F) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_mcart_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l68_mcart_1)).

tff(f_110,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_mcart_1)).

tff(f_85,axiom,(
    ! [A,B,C,D] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & D != k1_xboole_0
        & ~ ! [E] :
              ( m1_subset_1(E,k4_zfmisc_1(A,B,C,D))
             => E = k4_mcart_1(k8_mcart_1(A,B,C,D,E),k9_mcart_1(A,B,C,D,E),k10_mcart_1(A,B,C,D,E),k11_mcart_1(A,B,C,D,E)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_mcart_1)).

tff(f_66,axiom,(
    ! [A,B,C,D,E,F,G,H] :
      ( k4_mcart_1(A,B,C,D) = k4_mcart_1(E,F,G,H)
     => ( A = E
        & B = F
        & C = G
        & D = H ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_mcart_1)).

tff(c_38,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_36,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_34,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_32,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_42,plain,(
    m1_subset_1('#skF_10',k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_2,plain,(
    ! [B_2,C_3,A_1,D_4,E_36] :
      ( k4_mcart_1('#skF_1'(E_36,D_4,B_2,C_3,A_1),'#skF_2'(E_36,D_4,B_2,C_3,A_1),'#skF_3'(E_36,D_4,B_2,C_3,A_1),'#skF_4'(E_36,D_4,B_2,C_3,A_1)) = E_36
      | ~ m1_subset_1(E_36,k4_zfmisc_1(A_1,B_2,C_3,D_4))
      | k1_xboole_0 = D_4
      | k1_xboole_0 = C_3
      | k1_xboole_0 = B_2
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_64,plain,(
    ! [D_149,C_152,A_150,E_153,B_151] :
      ( k11_mcart_1(A_150,B_151,C_152,D_149,E_153) = k2_mcart_1(E_153)
      | ~ m1_subset_1(E_153,k4_zfmisc_1(A_150,B_151,C_152,D_149))
      | k1_xboole_0 = D_149
      | k1_xboole_0 = C_152
      | k1_xboole_0 = B_151
      | k1_xboole_0 = A_150 ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_67,plain,
    ( k11_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = k2_mcart_1('#skF_10')
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_42,c_64])).

tff(c_70,plain,(
    k11_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = k2_mcart_1('#skF_10') ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_36,c_34,c_32,c_67])).

tff(c_191,plain,(
    ! [E_193,B_190,A_189,D_191,C_192] :
      ( k4_mcart_1(k8_mcart_1(A_189,B_190,C_192,D_191,E_193),k9_mcart_1(A_189,B_190,C_192,D_191,E_193),k10_mcart_1(A_189,B_190,C_192,D_191,E_193),k11_mcart_1(A_189,B_190,C_192,D_191,E_193)) = E_193
      | ~ m1_subset_1(E_193,k4_zfmisc_1(A_189,B_190,C_192,D_191))
      | k1_xboole_0 = D_191
      | k1_xboole_0 = C_192
      | k1_xboole_0 = B_190
      | k1_xboole_0 = A_189 ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_226,plain,
    ( k4_mcart_1(k8_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10'),k9_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10'),k10_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10'),k2_mcart_1('#skF_10')) = '#skF_10'
    | ~ m1_subset_1('#skF_10',k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8'))
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_191])).

tff(c_230,plain,
    ( k4_mcart_1(k8_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10'),k9_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10'),k10_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10'),k2_mcart_1('#skF_10')) = '#skF_10'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_226])).

tff(c_231,plain,(
    k4_mcart_1(k8_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10'),k9_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10'),k10_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10'),k2_mcart_1('#skF_10')) = '#skF_10' ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_36,c_34,c_32,c_230])).

tff(c_12,plain,(
    ! [D_66,F_68,H_70,B_64,C_65,A_63,G_69,E_67] :
      ( H_70 = D_66
      | k4_mcart_1(E_67,F_68,G_69,H_70) != k4_mcart_1(A_63,B_64,C_65,D_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_308,plain,(
    ! [D_199,A_200,B_201,C_202] :
      ( k2_mcart_1('#skF_10') = D_199
      | k4_mcart_1(A_200,B_201,C_202,D_199) != '#skF_10' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_231,c_12])).

tff(c_363,plain,(
    ! [A_233,E_229,B_231,C_232,D_230] :
      ( k2_mcart_1('#skF_10') = '#skF_4'(E_229,D_230,B_231,C_232,A_233)
      | E_229 != '#skF_10'
      | ~ m1_subset_1(E_229,k4_zfmisc_1(A_233,B_231,C_232,D_230))
      | k1_xboole_0 = D_230
      | k1_xboole_0 = C_232
      | k1_xboole_0 = B_231
      | k1_xboole_0 = A_233 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_308])).

tff(c_382,plain,
    ( k2_mcart_1('#skF_10') = '#skF_4'('#skF_10','#skF_8','#skF_6','#skF_7','#skF_5')
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_42,c_363])).

tff(c_389,plain,(
    k2_mcart_1('#skF_10') = '#skF_4'('#skF_10','#skF_8','#skF_6','#skF_7','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_36,c_34,c_32,c_382])).

tff(c_30,plain,(
    k11_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_71,plain,(
    k2_mcart_1('#skF_10') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_30])).

tff(c_393,plain,(
    '#skF_4'('#skF_10','#skF_8','#skF_6','#skF_7','#skF_5') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_389,c_71])).

tff(c_10,plain,(
    ! [B_2,C_3,A_1,D_4,E_36] :
      ( m1_subset_1('#skF_1'(E_36,D_4,B_2,C_3,A_1),A_1)
      | ~ m1_subset_1(E_36,k4_zfmisc_1(A_1,B_2,C_3,D_4))
      | k1_xboole_0 = D_4
      | k1_xboole_0 = C_3
      | k1_xboole_0 = B_2
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_6,plain,(
    ! [B_2,C_3,A_1,D_4,E_36] :
      ( m1_subset_1('#skF_3'(E_36,D_4,B_2,C_3,A_1),C_3)
      | ~ m1_subset_1(E_36,k4_zfmisc_1(A_1,B_2,C_3,D_4))
      | k1_xboole_0 = D_4
      | k1_xboole_0 = C_3
      | k1_xboole_0 = B_2
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_4,plain,(
    ! [B_2,C_3,A_1,D_4,E_36] :
      ( m1_subset_1('#skF_4'(E_36,D_4,B_2,C_3,A_1),D_4)
      | ~ m1_subset_1(E_36,k4_zfmisc_1(A_1,B_2,C_3,D_4))
      | k1_xboole_0 = D_4
      | k1_xboole_0 = C_3
      | k1_xboole_0 = B_2
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_8,plain,(
    ! [B_2,C_3,A_1,D_4,E_36] :
      ( m1_subset_1('#skF_2'(E_36,D_4,B_2,C_3,A_1),B_2)
      | ~ m1_subset_1(E_36,k4_zfmisc_1(A_1,B_2,C_3,D_4))
      | k1_xboole_0 = D_4
      | k1_xboole_0 = C_3
      | k1_xboole_0 = B_2
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_240,plain,(
    ! [D_195,B_196,C_197,E_194,A_198] :
      ( k4_mcart_1('#skF_1'(E_194,D_195,B_196,C_197,A_198),'#skF_2'(E_194,D_195,B_196,C_197,A_198),'#skF_3'(E_194,D_195,B_196,C_197,A_198),'#skF_4'(E_194,D_195,B_196,C_197,A_198)) = E_194
      | ~ m1_subset_1(E_194,k4_zfmisc_1(A_198,B_196,C_197,D_195))
      | k1_xboole_0 = D_195
      | k1_xboole_0 = C_197
      | k1_xboole_0 = B_196
      | k1_xboole_0 = A_198 ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_40,plain,(
    ! [J_112,G_98,H_106,I_110] :
      ( J_112 = '#skF_9'
      | k4_mcart_1(G_98,H_106,I_110,J_112) != '#skF_10'
      | ~ m1_subset_1(J_112,'#skF_8')
      | ~ m1_subset_1(I_110,'#skF_7')
      | ~ m1_subset_1(H_106,'#skF_6')
      | ~ m1_subset_1(G_98,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_400,plain,(
    ! [B_234,D_237,C_236,E_235,A_238] :
      ( '#skF_4'(E_235,D_237,B_234,C_236,A_238) = '#skF_9'
      | E_235 != '#skF_10'
      | ~ m1_subset_1('#skF_4'(E_235,D_237,B_234,C_236,A_238),'#skF_8')
      | ~ m1_subset_1('#skF_3'(E_235,D_237,B_234,C_236,A_238),'#skF_7')
      | ~ m1_subset_1('#skF_2'(E_235,D_237,B_234,C_236,A_238),'#skF_6')
      | ~ m1_subset_1('#skF_1'(E_235,D_237,B_234,C_236,A_238),'#skF_5')
      | ~ m1_subset_1(E_235,k4_zfmisc_1(A_238,B_234,C_236,D_237))
      | k1_xboole_0 = D_237
      | k1_xboole_0 = C_236
      | k1_xboole_0 = B_234
      | k1_xboole_0 = A_238 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_240,c_40])).

tff(c_404,plain,(
    ! [E_36,D_4,C_3,A_1] :
      ( '#skF_4'(E_36,D_4,'#skF_6',C_3,A_1) = '#skF_9'
      | E_36 != '#skF_10'
      | ~ m1_subset_1('#skF_4'(E_36,D_4,'#skF_6',C_3,A_1),'#skF_8')
      | ~ m1_subset_1('#skF_3'(E_36,D_4,'#skF_6',C_3,A_1),'#skF_7')
      | ~ m1_subset_1('#skF_1'(E_36,D_4,'#skF_6',C_3,A_1),'#skF_5')
      | ~ m1_subset_1(E_36,k4_zfmisc_1(A_1,'#skF_6',C_3,D_4))
      | k1_xboole_0 = D_4
      | k1_xboole_0 = C_3
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = A_1 ) ),
    inference(resolution,[status(thm)],[c_8,c_400])).

tff(c_547,plain,(
    ! [E_275,D_276,C_277,A_278] :
      ( '#skF_4'(E_275,D_276,'#skF_6',C_277,A_278) = '#skF_9'
      | E_275 != '#skF_10'
      | ~ m1_subset_1('#skF_4'(E_275,D_276,'#skF_6',C_277,A_278),'#skF_8')
      | ~ m1_subset_1('#skF_3'(E_275,D_276,'#skF_6',C_277,A_278),'#skF_7')
      | ~ m1_subset_1('#skF_1'(E_275,D_276,'#skF_6',C_277,A_278),'#skF_5')
      | ~ m1_subset_1(E_275,k4_zfmisc_1(A_278,'#skF_6',C_277,D_276))
      | k1_xboole_0 = D_276
      | k1_xboole_0 = C_277
      | k1_xboole_0 = A_278 ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_36,c_404])).

tff(c_551,plain,(
    ! [E_36,C_3,A_1] :
      ( '#skF_4'(E_36,'#skF_8','#skF_6',C_3,A_1) = '#skF_9'
      | E_36 != '#skF_10'
      | ~ m1_subset_1('#skF_3'(E_36,'#skF_8','#skF_6',C_3,A_1),'#skF_7')
      | ~ m1_subset_1('#skF_1'(E_36,'#skF_8','#skF_6',C_3,A_1),'#skF_5')
      | ~ m1_subset_1(E_36,k4_zfmisc_1(A_1,'#skF_6',C_3,'#skF_8'))
      | k1_xboole_0 = '#skF_8'
      | k1_xboole_0 = C_3
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = A_1 ) ),
    inference(resolution,[status(thm)],[c_4,c_547])).

tff(c_608,plain,(
    ! [E_315,C_316,A_317] :
      ( '#skF_4'(E_315,'#skF_8','#skF_6',C_316,A_317) = '#skF_9'
      | E_315 != '#skF_10'
      | ~ m1_subset_1('#skF_3'(E_315,'#skF_8','#skF_6',C_316,A_317),'#skF_7')
      | ~ m1_subset_1('#skF_1'(E_315,'#skF_8','#skF_6',C_316,A_317),'#skF_5')
      | ~ m1_subset_1(E_315,k4_zfmisc_1(A_317,'#skF_6',C_316,'#skF_8'))
      | k1_xboole_0 = C_316
      | k1_xboole_0 = A_317 ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_32,c_32,c_551])).

tff(c_612,plain,(
    ! [E_36,A_1] :
      ( '#skF_4'(E_36,'#skF_8','#skF_6','#skF_7',A_1) = '#skF_9'
      | E_36 != '#skF_10'
      | ~ m1_subset_1('#skF_1'(E_36,'#skF_8','#skF_6','#skF_7',A_1),'#skF_5')
      | ~ m1_subset_1(E_36,k4_zfmisc_1(A_1,'#skF_6','#skF_7','#skF_8'))
      | k1_xboole_0 = '#skF_8'
      | k1_xboole_0 = '#skF_7'
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = A_1 ) ),
    inference(resolution,[status(thm)],[c_6,c_608])).

tff(c_617,plain,(
    ! [E_318,A_319] :
      ( '#skF_4'(E_318,'#skF_8','#skF_6','#skF_7',A_319) = '#skF_9'
      | E_318 != '#skF_10'
      | ~ m1_subset_1('#skF_1'(E_318,'#skF_8','#skF_6','#skF_7',A_319),'#skF_5')
      | ~ m1_subset_1(E_318,k4_zfmisc_1(A_319,'#skF_6','#skF_7','#skF_8'))
      | k1_xboole_0 = A_319 ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_34,c_32,c_34,c_612])).

tff(c_621,plain,(
    ! [E_36] :
      ( '#skF_4'(E_36,'#skF_8','#skF_6','#skF_7','#skF_5') = '#skF_9'
      | E_36 != '#skF_10'
      | ~ m1_subset_1(E_36,k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8'))
      | k1_xboole_0 = '#skF_8'
      | k1_xboole_0 = '#skF_7'
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_10,c_617])).

tff(c_626,plain,(
    ! [E_320] :
      ( '#skF_4'(E_320,'#skF_8','#skF_6','#skF_7','#skF_5') = '#skF_9'
      | E_320 != '#skF_10'
      | ~ m1_subset_1(E_320,k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_36,c_34,c_32,c_38,c_621])).

tff(c_645,plain,(
    '#skF_4'('#skF_10','#skF_8','#skF_6','#skF_7','#skF_5') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_42,c_626])).

tff(c_653,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_393,c_645])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n002.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 11:44:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.15/1.52  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.38/1.53  
% 3.38/1.53  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.38/1.53  %$ m1_subset_1 > k9_mcart_1 > k8_mcart_1 > k11_mcart_1 > k10_mcart_1 > k4_zfmisc_1 > k4_mcart_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_4 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_9 > #skF_3 > #skF_1 > #skF_8
% 3.38/1.53  
% 3.38/1.53  %Foreground sorts:
% 3.38/1.53  
% 3.38/1.53  
% 3.38/1.53  %Background operators:
% 3.38/1.53  
% 3.38/1.53  
% 3.38/1.53  %Foreground operators:
% 3.38/1.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.38/1.53  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i) > $i).
% 3.38/1.53  tff(k10_mcart_1, type, k10_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 3.38/1.53  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.38/1.53  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i * $i) > $i).
% 3.38/1.53  tff(k4_zfmisc_1, type, k4_zfmisc_1: ($i * $i * $i * $i) > $i).
% 3.38/1.53  tff('#skF_7', type, '#skF_7': $i).
% 3.38/1.53  tff('#skF_10', type, '#skF_10': $i).
% 3.38/1.53  tff('#skF_5', type, '#skF_5': $i).
% 3.38/1.53  tff(k11_mcart_1, type, k11_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 3.38/1.53  tff('#skF_6', type, '#skF_6': $i).
% 3.38/1.53  tff('#skF_9', type, '#skF_9': $i).
% 3.38/1.53  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i * $i) > $i).
% 3.38/1.53  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i) > $i).
% 3.38/1.53  tff('#skF_8', type, '#skF_8': $i).
% 3.38/1.53  tff(k8_mcart_1, type, k8_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 3.38/1.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.38/1.53  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 3.38/1.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.38/1.53  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 3.38/1.53  tff(k9_mcart_1, type, k9_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 3.38/1.53  tff(k4_mcart_1, type, k4_mcart_1: ($i * $i * $i * $i) > $i).
% 3.38/1.53  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.38/1.53  
% 3.38/1.55  tff(f_139, negated_conjecture, ~(![A, B, C, D, E, F]: (m1_subset_1(F, k4_zfmisc_1(A, B, C, D)) => ((![G]: (m1_subset_1(G, A) => (![H]: (m1_subset_1(H, B) => (![I]: (m1_subset_1(I, C) => (![J]: (m1_subset_1(J, D) => ((F = k4_mcart_1(G, H, I, J)) => (E = J)))))))))) => (((((A = k1_xboole_0) | (B = k1_xboole_0)) | (C = k1_xboole_0)) | (D = k1_xboole_0)) | (E = k11_mcart_1(A, B, C, D, F)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t82_mcart_1)).
% 3.38/1.55  tff(f_56, axiom, (![A, B, C, D]: ~((((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(D = k1_xboole_0)) & (?[E]: (m1_subset_1(E, k4_zfmisc_1(A, B, C, D)) & (![F]: (m1_subset_1(F, A) => (![G]: (m1_subset_1(G, B) => (![H]: (m1_subset_1(H, C) => (![I]: (m1_subset_1(I, D) => ~(E = k4_mcart_1(F, G, H, I)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l68_mcart_1)).
% 3.38/1.55  tff(f_110, axiom, (![A, B, C, D]: ~((((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(D = k1_xboole_0)) & ~(![E]: (m1_subset_1(E, k4_zfmisc_1(A, B, C, D)) => ((((k8_mcart_1(A, B, C, D, E) = k1_mcart_1(k1_mcart_1(k1_mcart_1(E)))) & (k9_mcart_1(A, B, C, D, E) = k2_mcart_1(k1_mcart_1(k1_mcart_1(E))))) & (k10_mcart_1(A, B, C, D, E) = k2_mcart_1(k1_mcart_1(E)))) & (k11_mcart_1(A, B, C, D, E) = k2_mcart_1(E))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_mcart_1)).
% 3.38/1.55  tff(f_85, axiom, (![A, B, C, D]: ~((((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(D = k1_xboole_0)) & ~(![E]: (m1_subset_1(E, k4_zfmisc_1(A, B, C, D)) => (E = k4_mcart_1(k8_mcart_1(A, B, C, D, E), k9_mcart_1(A, B, C, D, E), k10_mcart_1(A, B, C, D, E), k11_mcart_1(A, B, C, D, E))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_mcart_1)).
% 3.38/1.55  tff(f_66, axiom, (![A, B, C, D, E, F, G, H]: ((k4_mcart_1(A, B, C, D) = k4_mcart_1(E, F, G, H)) => ((((A = E) & (B = F)) & (C = G)) & (D = H)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_mcart_1)).
% 3.38/1.55  tff(c_38, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.38/1.55  tff(c_36, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.38/1.55  tff(c_34, plain, (k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.38/1.55  tff(c_32, plain, (k1_xboole_0!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.38/1.55  tff(c_42, plain, (m1_subset_1('#skF_10', k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.38/1.55  tff(c_2, plain, (![B_2, C_3, A_1, D_4, E_36]: (k4_mcart_1('#skF_1'(E_36, D_4, B_2, C_3, A_1), '#skF_2'(E_36, D_4, B_2, C_3, A_1), '#skF_3'(E_36, D_4, B_2, C_3, A_1), '#skF_4'(E_36, D_4, B_2, C_3, A_1))=E_36 | ~m1_subset_1(E_36, k4_zfmisc_1(A_1, B_2, C_3, D_4)) | k1_xboole_0=D_4 | k1_xboole_0=C_3 | k1_xboole_0=B_2 | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.38/1.55  tff(c_64, plain, (![D_149, C_152, A_150, E_153, B_151]: (k11_mcart_1(A_150, B_151, C_152, D_149, E_153)=k2_mcart_1(E_153) | ~m1_subset_1(E_153, k4_zfmisc_1(A_150, B_151, C_152, D_149)) | k1_xboole_0=D_149 | k1_xboole_0=C_152 | k1_xboole_0=B_151 | k1_xboole_0=A_150)), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.38/1.55  tff(c_67, plain, (k11_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')=k2_mcart_1('#skF_10') | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_42, c_64])).
% 3.38/1.55  tff(c_70, plain, (k11_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')=k2_mcart_1('#skF_10')), inference(negUnitSimplification, [status(thm)], [c_38, c_36, c_34, c_32, c_67])).
% 3.38/1.55  tff(c_191, plain, (![E_193, B_190, A_189, D_191, C_192]: (k4_mcart_1(k8_mcart_1(A_189, B_190, C_192, D_191, E_193), k9_mcart_1(A_189, B_190, C_192, D_191, E_193), k10_mcart_1(A_189, B_190, C_192, D_191, E_193), k11_mcart_1(A_189, B_190, C_192, D_191, E_193))=E_193 | ~m1_subset_1(E_193, k4_zfmisc_1(A_189, B_190, C_192, D_191)) | k1_xboole_0=D_191 | k1_xboole_0=C_192 | k1_xboole_0=B_190 | k1_xboole_0=A_189)), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.38/1.55  tff(c_226, plain, (k4_mcart_1(k8_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10'), k9_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10'), k10_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10'), k2_mcart_1('#skF_10'))='#skF_10' | ~m1_subset_1('#skF_10', k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')) | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_70, c_191])).
% 3.38/1.55  tff(c_230, plain, (k4_mcart_1(k8_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10'), k9_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10'), k10_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10'), k2_mcart_1('#skF_10'))='#skF_10' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_226])).
% 3.38/1.55  tff(c_231, plain, (k4_mcart_1(k8_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10'), k9_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10'), k10_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10'), k2_mcart_1('#skF_10'))='#skF_10'), inference(negUnitSimplification, [status(thm)], [c_38, c_36, c_34, c_32, c_230])).
% 3.38/1.55  tff(c_12, plain, (![D_66, F_68, H_70, B_64, C_65, A_63, G_69, E_67]: (H_70=D_66 | k4_mcart_1(E_67, F_68, G_69, H_70)!=k4_mcart_1(A_63, B_64, C_65, D_66))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.38/1.55  tff(c_308, plain, (![D_199, A_200, B_201, C_202]: (k2_mcart_1('#skF_10')=D_199 | k4_mcart_1(A_200, B_201, C_202, D_199)!='#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_231, c_12])).
% 3.38/1.55  tff(c_363, plain, (![A_233, E_229, B_231, C_232, D_230]: (k2_mcart_1('#skF_10')='#skF_4'(E_229, D_230, B_231, C_232, A_233) | E_229!='#skF_10' | ~m1_subset_1(E_229, k4_zfmisc_1(A_233, B_231, C_232, D_230)) | k1_xboole_0=D_230 | k1_xboole_0=C_232 | k1_xboole_0=B_231 | k1_xboole_0=A_233)), inference(superposition, [status(thm), theory('equality')], [c_2, c_308])).
% 3.38/1.55  tff(c_382, plain, (k2_mcart_1('#skF_10')='#skF_4'('#skF_10', '#skF_8', '#skF_6', '#skF_7', '#skF_5') | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_42, c_363])).
% 3.38/1.55  tff(c_389, plain, (k2_mcart_1('#skF_10')='#skF_4'('#skF_10', '#skF_8', '#skF_6', '#skF_7', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_38, c_36, c_34, c_32, c_382])).
% 3.38/1.55  tff(c_30, plain, (k11_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.38/1.55  tff(c_71, plain, (k2_mcart_1('#skF_10')!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_30])).
% 3.38/1.55  tff(c_393, plain, ('#skF_4'('#skF_10', '#skF_8', '#skF_6', '#skF_7', '#skF_5')!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_389, c_71])).
% 3.38/1.55  tff(c_10, plain, (![B_2, C_3, A_1, D_4, E_36]: (m1_subset_1('#skF_1'(E_36, D_4, B_2, C_3, A_1), A_1) | ~m1_subset_1(E_36, k4_zfmisc_1(A_1, B_2, C_3, D_4)) | k1_xboole_0=D_4 | k1_xboole_0=C_3 | k1_xboole_0=B_2 | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.38/1.55  tff(c_6, plain, (![B_2, C_3, A_1, D_4, E_36]: (m1_subset_1('#skF_3'(E_36, D_4, B_2, C_3, A_1), C_3) | ~m1_subset_1(E_36, k4_zfmisc_1(A_1, B_2, C_3, D_4)) | k1_xboole_0=D_4 | k1_xboole_0=C_3 | k1_xboole_0=B_2 | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.38/1.55  tff(c_4, plain, (![B_2, C_3, A_1, D_4, E_36]: (m1_subset_1('#skF_4'(E_36, D_4, B_2, C_3, A_1), D_4) | ~m1_subset_1(E_36, k4_zfmisc_1(A_1, B_2, C_3, D_4)) | k1_xboole_0=D_4 | k1_xboole_0=C_3 | k1_xboole_0=B_2 | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.38/1.55  tff(c_8, plain, (![B_2, C_3, A_1, D_4, E_36]: (m1_subset_1('#skF_2'(E_36, D_4, B_2, C_3, A_1), B_2) | ~m1_subset_1(E_36, k4_zfmisc_1(A_1, B_2, C_3, D_4)) | k1_xboole_0=D_4 | k1_xboole_0=C_3 | k1_xboole_0=B_2 | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.38/1.55  tff(c_240, plain, (![D_195, B_196, C_197, E_194, A_198]: (k4_mcart_1('#skF_1'(E_194, D_195, B_196, C_197, A_198), '#skF_2'(E_194, D_195, B_196, C_197, A_198), '#skF_3'(E_194, D_195, B_196, C_197, A_198), '#skF_4'(E_194, D_195, B_196, C_197, A_198))=E_194 | ~m1_subset_1(E_194, k4_zfmisc_1(A_198, B_196, C_197, D_195)) | k1_xboole_0=D_195 | k1_xboole_0=C_197 | k1_xboole_0=B_196 | k1_xboole_0=A_198)), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.38/1.55  tff(c_40, plain, (![J_112, G_98, H_106, I_110]: (J_112='#skF_9' | k4_mcart_1(G_98, H_106, I_110, J_112)!='#skF_10' | ~m1_subset_1(J_112, '#skF_8') | ~m1_subset_1(I_110, '#skF_7') | ~m1_subset_1(H_106, '#skF_6') | ~m1_subset_1(G_98, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.38/1.55  tff(c_400, plain, (![B_234, D_237, C_236, E_235, A_238]: ('#skF_4'(E_235, D_237, B_234, C_236, A_238)='#skF_9' | E_235!='#skF_10' | ~m1_subset_1('#skF_4'(E_235, D_237, B_234, C_236, A_238), '#skF_8') | ~m1_subset_1('#skF_3'(E_235, D_237, B_234, C_236, A_238), '#skF_7') | ~m1_subset_1('#skF_2'(E_235, D_237, B_234, C_236, A_238), '#skF_6') | ~m1_subset_1('#skF_1'(E_235, D_237, B_234, C_236, A_238), '#skF_5') | ~m1_subset_1(E_235, k4_zfmisc_1(A_238, B_234, C_236, D_237)) | k1_xboole_0=D_237 | k1_xboole_0=C_236 | k1_xboole_0=B_234 | k1_xboole_0=A_238)), inference(superposition, [status(thm), theory('equality')], [c_240, c_40])).
% 3.38/1.55  tff(c_404, plain, (![E_36, D_4, C_3, A_1]: ('#skF_4'(E_36, D_4, '#skF_6', C_3, A_1)='#skF_9' | E_36!='#skF_10' | ~m1_subset_1('#skF_4'(E_36, D_4, '#skF_6', C_3, A_1), '#skF_8') | ~m1_subset_1('#skF_3'(E_36, D_4, '#skF_6', C_3, A_1), '#skF_7') | ~m1_subset_1('#skF_1'(E_36, D_4, '#skF_6', C_3, A_1), '#skF_5') | ~m1_subset_1(E_36, k4_zfmisc_1(A_1, '#skF_6', C_3, D_4)) | k1_xboole_0=D_4 | k1_xboole_0=C_3 | k1_xboole_0='#skF_6' | k1_xboole_0=A_1)), inference(resolution, [status(thm)], [c_8, c_400])).
% 3.38/1.55  tff(c_547, plain, (![E_275, D_276, C_277, A_278]: ('#skF_4'(E_275, D_276, '#skF_6', C_277, A_278)='#skF_9' | E_275!='#skF_10' | ~m1_subset_1('#skF_4'(E_275, D_276, '#skF_6', C_277, A_278), '#skF_8') | ~m1_subset_1('#skF_3'(E_275, D_276, '#skF_6', C_277, A_278), '#skF_7') | ~m1_subset_1('#skF_1'(E_275, D_276, '#skF_6', C_277, A_278), '#skF_5') | ~m1_subset_1(E_275, k4_zfmisc_1(A_278, '#skF_6', C_277, D_276)) | k1_xboole_0=D_276 | k1_xboole_0=C_277 | k1_xboole_0=A_278)), inference(negUnitSimplification, [status(thm)], [c_36, c_36, c_404])).
% 3.38/1.55  tff(c_551, plain, (![E_36, C_3, A_1]: ('#skF_4'(E_36, '#skF_8', '#skF_6', C_3, A_1)='#skF_9' | E_36!='#skF_10' | ~m1_subset_1('#skF_3'(E_36, '#skF_8', '#skF_6', C_3, A_1), '#skF_7') | ~m1_subset_1('#skF_1'(E_36, '#skF_8', '#skF_6', C_3, A_1), '#skF_5') | ~m1_subset_1(E_36, k4_zfmisc_1(A_1, '#skF_6', C_3, '#skF_8')) | k1_xboole_0='#skF_8' | k1_xboole_0=C_3 | k1_xboole_0='#skF_6' | k1_xboole_0=A_1)), inference(resolution, [status(thm)], [c_4, c_547])).
% 3.38/1.55  tff(c_608, plain, (![E_315, C_316, A_317]: ('#skF_4'(E_315, '#skF_8', '#skF_6', C_316, A_317)='#skF_9' | E_315!='#skF_10' | ~m1_subset_1('#skF_3'(E_315, '#skF_8', '#skF_6', C_316, A_317), '#skF_7') | ~m1_subset_1('#skF_1'(E_315, '#skF_8', '#skF_6', C_316, A_317), '#skF_5') | ~m1_subset_1(E_315, k4_zfmisc_1(A_317, '#skF_6', C_316, '#skF_8')) | k1_xboole_0=C_316 | k1_xboole_0=A_317)), inference(negUnitSimplification, [status(thm)], [c_36, c_32, c_32, c_551])).
% 3.38/1.55  tff(c_612, plain, (![E_36, A_1]: ('#skF_4'(E_36, '#skF_8', '#skF_6', '#skF_7', A_1)='#skF_9' | E_36!='#skF_10' | ~m1_subset_1('#skF_1'(E_36, '#skF_8', '#skF_6', '#skF_7', A_1), '#skF_5') | ~m1_subset_1(E_36, k4_zfmisc_1(A_1, '#skF_6', '#skF_7', '#skF_8')) | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0=A_1)), inference(resolution, [status(thm)], [c_6, c_608])).
% 3.38/1.55  tff(c_617, plain, (![E_318, A_319]: ('#skF_4'(E_318, '#skF_8', '#skF_6', '#skF_7', A_319)='#skF_9' | E_318!='#skF_10' | ~m1_subset_1('#skF_1'(E_318, '#skF_8', '#skF_6', '#skF_7', A_319), '#skF_5') | ~m1_subset_1(E_318, k4_zfmisc_1(A_319, '#skF_6', '#skF_7', '#skF_8')) | k1_xboole_0=A_319)), inference(negUnitSimplification, [status(thm)], [c_36, c_34, c_32, c_34, c_612])).
% 3.38/1.55  tff(c_621, plain, (![E_36]: ('#skF_4'(E_36, '#skF_8', '#skF_6', '#skF_7', '#skF_5')='#skF_9' | E_36!='#skF_10' | ~m1_subset_1(E_36, k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')) | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5')), inference(resolution, [status(thm)], [c_10, c_617])).
% 3.38/1.55  tff(c_626, plain, (![E_320]: ('#skF_4'(E_320, '#skF_8', '#skF_6', '#skF_7', '#skF_5')='#skF_9' | E_320!='#skF_10' | ~m1_subset_1(E_320, k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')))), inference(negUnitSimplification, [status(thm)], [c_38, c_36, c_34, c_32, c_38, c_621])).
% 3.38/1.55  tff(c_645, plain, ('#skF_4'('#skF_10', '#skF_8', '#skF_6', '#skF_7', '#skF_5')='#skF_9'), inference(resolution, [status(thm)], [c_42, c_626])).
% 3.38/1.55  tff(c_653, plain, $false, inference(negUnitSimplification, [status(thm)], [c_393, c_645])).
% 3.38/1.55  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.38/1.55  
% 3.38/1.55  Inference rules
% 3.38/1.55  ----------------------
% 3.38/1.55  #Ref     : 12
% 3.38/1.55  #Sup     : 140
% 3.38/1.55  #Fact    : 0
% 3.38/1.55  #Define  : 0
% 3.38/1.55  #Split   : 0
% 3.38/1.55  #Chain   : 0
% 3.38/1.55  #Close   : 0
% 3.38/1.55  
% 3.38/1.55  Ordering : KBO
% 3.38/1.55  
% 3.38/1.55  Simplification rules
% 3.38/1.55  ----------------------
% 3.38/1.55  #Subsume      : 18
% 3.38/1.55  #Demod        : 11
% 3.38/1.55  #Tautology    : 34
% 3.38/1.55  #SimpNegUnit  : 15
% 3.38/1.55  #BackRed      : 6
% 3.38/1.55  
% 3.38/1.55  #Partial instantiations: 0
% 3.38/1.55  #Strategies tried      : 1
% 3.38/1.55  
% 3.38/1.55  Timing (in seconds)
% 3.38/1.55  ----------------------
% 3.49/1.55  Preprocessing        : 0.36
% 3.49/1.55  Parsing              : 0.19
% 3.49/1.55  CNF conversion       : 0.04
% 3.49/1.55  Main loop            : 0.38
% 3.49/1.55  Inferencing          : 0.14
% 3.49/1.55  Reduction            : 0.08
% 3.49/1.55  Demodulation         : 0.05
% 3.49/1.55  BG Simplification    : 0.03
% 3.49/1.55  Subsumption          : 0.10
% 3.49/1.55  Abstraction          : 0.03
% 3.49/1.55  MUC search           : 0.00
% 3.49/1.55  Cooper               : 0.00
% 3.49/1.55  Total                : 0.77
% 3.49/1.55  Index Insertion      : 0.00
% 3.49/1.55  Index Deletion       : 0.00
% 3.49/1.55  Index Matching       : 0.00
% 3.49/1.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
