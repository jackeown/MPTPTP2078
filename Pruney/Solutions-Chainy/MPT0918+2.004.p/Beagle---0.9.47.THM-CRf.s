%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:14 EST 2020

% Result     : Theorem 2.99s
% Output     : CNFRefutation 2.99s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 151 expanded)
%              Number of leaves         :   27 (  72 expanded)
%              Depth                    :    6
%              Number of atoms          :  162 ( 675 expanded)
%              Number of equality atoms :  141 ( 603 expanded)
%              Maximal formula depth    :   22 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > k9_mcart_1 > k8_mcart_1 > k11_mcart_1 > k10_mcart_1 > k4_zfmisc_1 > k4_mcart_1 > k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_9 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k10_mcart_1,type,(
    k10_mcart_1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(c_347,plain,(
    ! [D_137,E_133,C_134,B_135,A_136] :
      ( k11_mcart_1(A_136,B_135,C_134,D_137,E_133) = k2_mcart_1(E_133)
      | ~ m1_subset_1(E_133,k4_zfmisc_1(A_136,B_135,C_134,D_137))
      | k1_xboole_0 = D_137
      | k1_xboole_0 = C_134
      | k1_xboole_0 = B_135
      | k1_xboole_0 = A_136 ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_356,plain,
    ( k11_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') = k2_mcart_1('#skF_5')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_34,c_347])).

tff(c_359,plain,(
    k11_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') = k2_mcart_1('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_30,c_28,c_26,c_356])).

tff(c_22,plain,
    ( k11_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') != '#skF_9'
    | k10_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') != '#skF_8'
    | k9_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') != '#skF_7'
    | k8_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_85,plain,(
    k8_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_22])).

tff(c_24,plain,(
    k4_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9') = '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_256,plain,(
    ! [A_108,I_106,B_110,D_112,F_109,C_111,H_107,G_105] :
      ( k8_mcart_1(A_108,B_110,C_111,D_112,k4_mcart_1(F_109,G_105,H_107,I_106)) = F_109
      | ~ m1_subset_1(k4_mcart_1(F_109,G_105,H_107,I_106),k4_zfmisc_1(A_108,B_110,C_111,D_112))
      | k1_xboole_0 = D_112
      | k1_xboole_0 = C_111
      | k1_xboole_0 = B_110
      | k1_xboole_0 = A_108 ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_265,plain,(
    ! [A_108,B_110,C_111,D_112] :
      ( k8_mcart_1(A_108,B_110,C_111,D_112,k4_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9')) = '#skF_6'
      | ~ m1_subset_1('#skF_5',k4_zfmisc_1(A_108,B_110,C_111,D_112))
      | k1_xboole_0 = D_112
      | k1_xboole_0 = C_111
      | k1_xboole_0 = B_110
      | k1_xboole_0 = A_108 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_256])).

tff(c_267,plain,(
    ! [A_113,B_114,C_115,D_116] :
      ( k8_mcart_1(A_113,B_114,C_115,D_116,'#skF_5') = '#skF_6'
      | ~ m1_subset_1('#skF_5',k4_zfmisc_1(A_113,B_114,C_115,D_116))
      | k1_xboole_0 = D_116
      | k1_xboole_0 = C_115
      | k1_xboole_0 = B_114
      | k1_xboole_0 = A_113 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_265])).

tff(c_276,plain,
    ( k8_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') = '#skF_6'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_34,c_267])).

tff(c_280,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_30,c_28,c_26,c_85,c_276])).

tff(c_281,plain,
    ( k9_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') != '#skF_7'
    | k10_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') != '#skF_8'
    | k11_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') != '#skF_9' ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_288,plain,(
    k11_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') != '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_281])).

tff(c_360,plain,(
    k2_mcart_1('#skF_5') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_359,c_288])).

tff(c_469,plain,(
    ! [I_185,H_186,G_184,C_190,B_189,F_188,A_187,D_191] :
      ( k11_mcart_1(A_187,B_189,C_190,D_191,k4_mcart_1(F_188,G_184,H_186,I_185)) = I_185
      | ~ m1_subset_1(k4_mcart_1(F_188,G_184,H_186,I_185),k4_zfmisc_1(A_187,B_189,C_190,D_191))
      | k1_xboole_0 = D_191
      | k1_xboole_0 = C_190
      | k1_xboole_0 = B_189
      | k1_xboole_0 = A_187 ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_478,plain,(
    ! [A_187,B_189,C_190,D_191] :
      ( k11_mcart_1(A_187,B_189,C_190,D_191,k4_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9')) = '#skF_9'
      | ~ m1_subset_1('#skF_5',k4_zfmisc_1(A_187,B_189,C_190,D_191))
      | k1_xboole_0 = D_191
      | k1_xboole_0 = C_190
      | k1_xboole_0 = B_189
      | k1_xboole_0 = A_187 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_469])).

tff(c_502,plain,(
    ! [A_196,B_197,C_198,D_199] :
      ( k11_mcart_1(A_196,B_197,C_198,D_199,'#skF_5') = '#skF_9'
      | ~ m1_subset_1('#skF_5',k4_zfmisc_1(A_196,B_197,C_198,D_199))
      | k1_xboole_0 = D_199
      | k1_xboole_0 = C_198
      | k1_xboole_0 = B_197
      | k1_xboole_0 = A_196 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_478])).

tff(c_511,plain,
    ( k11_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') = '#skF_9'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_34,c_502])).

tff(c_513,plain,
    ( k2_mcart_1('#skF_5') = '#skF_9'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_359,c_511])).

tff(c_515,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_30,c_28,c_26,c_360,c_513])).

tff(c_516,plain,
    ( k10_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') != '#skF_8'
    | k9_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_281])).

tff(c_522,plain,(
    k9_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_516])).

tff(c_766,plain,(
    ! [A_296,F_297,I_294,C_299,H_295,D_300,B_298,G_293] :
      ( k9_mcart_1(A_296,B_298,C_299,D_300,k4_mcart_1(F_297,G_293,H_295,I_294)) = G_293
      | ~ m1_subset_1(k4_mcart_1(F_297,G_293,H_295,I_294),k4_zfmisc_1(A_296,B_298,C_299,D_300))
      | k1_xboole_0 = D_300
      | k1_xboole_0 = C_299
      | k1_xboole_0 = B_298
      | k1_xboole_0 = A_296 ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_775,plain,(
    ! [A_296,B_298,C_299,D_300] :
      ( k9_mcart_1(A_296,B_298,C_299,D_300,k4_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9')) = '#skF_7'
      | ~ m1_subset_1('#skF_5',k4_zfmisc_1(A_296,B_298,C_299,D_300))
      | k1_xboole_0 = D_300
      | k1_xboole_0 = C_299
      | k1_xboole_0 = B_298
      | k1_xboole_0 = A_296 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_766])).

tff(c_777,plain,(
    ! [A_301,B_302,C_303,D_304] :
      ( k9_mcart_1(A_301,B_302,C_303,D_304,'#skF_5') = '#skF_7'
      | ~ m1_subset_1('#skF_5',k4_zfmisc_1(A_301,B_302,C_303,D_304))
      | k1_xboole_0 = D_304
      | k1_xboole_0 = C_303
      | k1_xboole_0 = B_302
      | k1_xboole_0 = A_301 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_775])).

tff(c_786,plain,
    ( k9_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') = '#skF_7'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_34,c_777])).

tff(c_790,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_30,c_28,c_26,c_522,c_786])).

tff(c_791,plain,(
    k10_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_516])).

tff(c_1007,plain,(
    ! [F_391,A_390,H_389,C_393,B_392,I_388,G_387,D_394] :
      ( k10_mcart_1(A_390,B_392,C_393,D_394,k4_mcart_1(F_391,G_387,H_389,I_388)) = H_389
      | ~ m1_subset_1(k4_mcart_1(F_391,G_387,H_389,I_388),k4_zfmisc_1(A_390,B_392,C_393,D_394))
      | k1_xboole_0 = D_394
      | k1_xboole_0 = C_393
      | k1_xboole_0 = B_392
      | k1_xboole_0 = A_390 ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1016,plain,(
    ! [A_390,B_392,C_393,D_394] :
      ( k10_mcart_1(A_390,B_392,C_393,D_394,k4_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9')) = '#skF_8'
      | ~ m1_subset_1('#skF_5',k4_zfmisc_1(A_390,B_392,C_393,D_394))
      | k1_xboole_0 = D_394
      | k1_xboole_0 = C_393
      | k1_xboole_0 = B_392
      | k1_xboole_0 = A_390 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_1007])).

tff(c_1018,plain,(
    ! [A_395,B_396,C_397,D_398] :
      ( k10_mcart_1(A_395,B_396,C_397,D_398,'#skF_5') = '#skF_8'
      | ~ m1_subset_1('#skF_5',k4_zfmisc_1(A_395,B_396,C_397,D_398))
      | k1_xboole_0 = D_398
      | k1_xboole_0 = C_397
      | k1_xboole_0 = B_396
      | k1_xboole_0 = A_395 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_1016])).

tff(c_1027,plain,
    ( k10_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') = '#skF_8'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_34,c_1018])).

tff(c_1031,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_30,c_28,c_26,c_791,c_1027])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 11:34:59 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.99/1.60  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.99/1.61  
% 2.99/1.61  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.99/1.61  %$ m1_subset_1 > k9_mcart_1 > k8_mcart_1 > k11_mcart_1 > k10_mcart_1 > k4_zfmisc_1 > k4_mcart_1 > k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_9 > #skF_8 > #skF_4
% 2.99/1.61  
% 2.99/1.61  %Foreground sorts:
% 2.99/1.61  
% 2.99/1.61  
% 2.99/1.61  %Background operators:
% 2.99/1.61  
% 2.99/1.61  
% 2.99/1.61  %Foreground operators:
% 2.99/1.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.99/1.61  tff(k10_mcart_1, type, k10_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 2.99/1.61  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.99/1.61  tff(k4_zfmisc_1, type, k4_zfmisc_1: ($i * $i * $i * $i) > $i).
% 2.99/1.61  tff('#skF_7', type, '#skF_7': $i).
% 2.99/1.61  tff('#skF_5', type, '#skF_5': $i).
% 2.99/1.61  tff(k11_mcart_1, type, k11_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 2.99/1.61  tff('#skF_6', type, '#skF_6': $i).
% 2.99/1.61  tff('#skF_2', type, '#skF_2': $i).
% 2.99/1.61  tff('#skF_3', type, '#skF_3': $i).
% 2.99/1.61  tff('#skF_1', type, '#skF_1': $i).
% 2.99/1.61  tff('#skF_9', type, '#skF_9': $i).
% 2.99/1.61  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 2.99/1.61  tff('#skF_8', type, '#skF_8': $i).
% 2.99/1.61  tff(k8_mcart_1, type, k8_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 2.99/1.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.99/1.61  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.99/1.61  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.99/1.61  tff('#skF_4', type, '#skF_4': $i).
% 2.99/1.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.99/1.61  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.99/1.61  tff(k9_mcart_1, type, k9_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 2.99/1.61  tff(k4_mcart_1, type, k4_mcart_1: ($i * $i * $i * $i) > $i).
% 2.99/1.61  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.99/1.61  
% 2.99/1.63  tff(f_110, negated_conjecture, ~(![A, B, C, D, E]: (m1_subset_1(E, k4_zfmisc_1(A, B, C, D)) => ~((((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(D = k1_xboole_0)) & (?[F, G, H, I]: ((E = k4_mcart_1(F, G, H, I)) & ~((((k8_mcart_1(A, B, C, D, E) = F) & (k9_mcart_1(A, B, C, D, E) = G)) & (k10_mcart_1(A, B, C, D, E) = H)) & (k11_mcart_1(A, B, C, D, E) = I))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_mcart_1)).
% 2.99/1.63  tff(f_82, axiom, (![A, B, C, D]: ~((((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(D = k1_xboole_0)) & ~(![E]: (m1_subset_1(E, k4_zfmisc_1(A, B, C, D)) => ((((k8_mcart_1(A, B, C, D, E) = k1_mcart_1(k1_mcart_1(k1_mcart_1(E)))) & (k9_mcart_1(A, B, C, D, E) = k2_mcart_1(k1_mcart_1(k1_mcart_1(E))))) & (k10_mcart_1(A, B, C, D, E) = k2_mcart_1(k1_mcart_1(E)))) & (k11_mcart_1(A, B, C, D, E) = k2_mcart_1(E))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_mcart_1)).
% 2.99/1.63  tff(f_57, axiom, (![A, B, C, D]: ~((((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(D = k1_xboole_0)) & (?[E]: (m1_subset_1(E, k4_zfmisc_1(A, B, C, D)) & (?[F, G, H, I]: ((E = k4_mcart_1(F, G, H, I)) & ~((((k8_mcart_1(A, B, C, D, E) = F) & (k9_mcart_1(A, B, C, D, E) = G)) & (k10_mcart_1(A, B, C, D, E) = H)) & (k11_mcart_1(A, B, C, D, E) = I)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_mcart_1)).
% 2.99/1.63  tff(c_32, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.99/1.63  tff(c_30, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.99/1.63  tff(c_28, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.99/1.63  tff(c_26, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.99/1.63  tff(c_34, plain, (m1_subset_1('#skF_5', k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.99/1.63  tff(c_347, plain, (![D_137, E_133, C_134, B_135, A_136]: (k11_mcart_1(A_136, B_135, C_134, D_137, E_133)=k2_mcart_1(E_133) | ~m1_subset_1(E_133, k4_zfmisc_1(A_136, B_135, C_134, D_137)) | k1_xboole_0=D_137 | k1_xboole_0=C_134 | k1_xboole_0=B_135 | k1_xboole_0=A_136)), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.99/1.63  tff(c_356, plain, (k11_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k2_mcart_1('#skF_5') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_34, c_347])).
% 2.99/1.63  tff(c_359, plain, (k11_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k2_mcart_1('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_32, c_30, c_28, c_26, c_356])).
% 2.99/1.63  tff(c_22, plain, (k11_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')!='#skF_9' | k10_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')!='#skF_8' | k9_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')!='#skF_7' | k8_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.99/1.63  tff(c_85, plain, (k8_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')!='#skF_6'), inference(splitLeft, [status(thm)], [c_22])).
% 2.99/1.63  tff(c_24, plain, (k4_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9')='#skF_5'), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.99/1.63  tff(c_256, plain, (![A_108, I_106, B_110, D_112, F_109, C_111, H_107, G_105]: (k8_mcart_1(A_108, B_110, C_111, D_112, k4_mcart_1(F_109, G_105, H_107, I_106))=F_109 | ~m1_subset_1(k4_mcart_1(F_109, G_105, H_107, I_106), k4_zfmisc_1(A_108, B_110, C_111, D_112)) | k1_xboole_0=D_112 | k1_xboole_0=C_111 | k1_xboole_0=B_110 | k1_xboole_0=A_108)), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.99/1.63  tff(c_265, plain, (![A_108, B_110, C_111, D_112]: (k8_mcart_1(A_108, B_110, C_111, D_112, k4_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'))='#skF_6' | ~m1_subset_1('#skF_5', k4_zfmisc_1(A_108, B_110, C_111, D_112)) | k1_xboole_0=D_112 | k1_xboole_0=C_111 | k1_xboole_0=B_110 | k1_xboole_0=A_108)), inference(superposition, [status(thm), theory('equality')], [c_24, c_256])).
% 2.99/1.63  tff(c_267, plain, (![A_113, B_114, C_115, D_116]: (k8_mcart_1(A_113, B_114, C_115, D_116, '#skF_5')='#skF_6' | ~m1_subset_1('#skF_5', k4_zfmisc_1(A_113, B_114, C_115, D_116)) | k1_xboole_0=D_116 | k1_xboole_0=C_115 | k1_xboole_0=B_114 | k1_xboole_0=A_113)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_265])).
% 2.99/1.63  tff(c_276, plain, (k8_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')='#skF_6' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_34, c_267])).
% 2.99/1.63  tff(c_280, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_30, c_28, c_26, c_85, c_276])).
% 2.99/1.63  tff(c_281, plain, (k9_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')!='#skF_7' | k10_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')!='#skF_8' | k11_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')!='#skF_9'), inference(splitRight, [status(thm)], [c_22])).
% 2.99/1.63  tff(c_288, plain, (k11_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')!='#skF_9'), inference(splitLeft, [status(thm)], [c_281])).
% 2.99/1.63  tff(c_360, plain, (k2_mcart_1('#skF_5')!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_359, c_288])).
% 2.99/1.63  tff(c_469, plain, (![I_185, H_186, G_184, C_190, B_189, F_188, A_187, D_191]: (k11_mcart_1(A_187, B_189, C_190, D_191, k4_mcart_1(F_188, G_184, H_186, I_185))=I_185 | ~m1_subset_1(k4_mcart_1(F_188, G_184, H_186, I_185), k4_zfmisc_1(A_187, B_189, C_190, D_191)) | k1_xboole_0=D_191 | k1_xboole_0=C_190 | k1_xboole_0=B_189 | k1_xboole_0=A_187)), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.99/1.63  tff(c_478, plain, (![A_187, B_189, C_190, D_191]: (k11_mcart_1(A_187, B_189, C_190, D_191, k4_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'))='#skF_9' | ~m1_subset_1('#skF_5', k4_zfmisc_1(A_187, B_189, C_190, D_191)) | k1_xboole_0=D_191 | k1_xboole_0=C_190 | k1_xboole_0=B_189 | k1_xboole_0=A_187)), inference(superposition, [status(thm), theory('equality')], [c_24, c_469])).
% 2.99/1.63  tff(c_502, plain, (![A_196, B_197, C_198, D_199]: (k11_mcart_1(A_196, B_197, C_198, D_199, '#skF_5')='#skF_9' | ~m1_subset_1('#skF_5', k4_zfmisc_1(A_196, B_197, C_198, D_199)) | k1_xboole_0=D_199 | k1_xboole_0=C_198 | k1_xboole_0=B_197 | k1_xboole_0=A_196)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_478])).
% 2.99/1.63  tff(c_511, plain, (k11_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')='#skF_9' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_34, c_502])).
% 2.99/1.63  tff(c_513, plain, (k2_mcart_1('#skF_5')='#skF_9' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_359, c_511])).
% 2.99/1.63  tff(c_515, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_30, c_28, c_26, c_360, c_513])).
% 2.99/1.63  tff(c_516, plain, (k10_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')!='#skF_8' | k9_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')!='#skF_7'), inference(splitRight, [status(thm)], [c_281])).
% 2.99/1.63  tff(c_522, plain, (k9_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')!='#skF_7'), inference(splitLeft, [status(thm)], [c_516])).
% 2.99/1.63  tff(c_766, plain, (![A_296, F_297, I_294, C_299, H_295, D_300, B_298, G_293]: (k9_mcart_1(A_296, B_298, C_299, D_300, k4_mcart_1(F_297, G_293, H_295, I_294))=G_293 | ~m1_subset_1(k4_mcart_1(F_297, G_293, H_295, I_294), k4_zfmisc_1(A_296, B_298, C_299, D_300)) | k1_xboole_0=D_300 | k1_xboole_0=C_299 | k1_xboole_0=B_298 | k1_xboole_0=A_296)), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.99/1.63  tff(c_775, plain, (![A_296, B_298, C_299, D_300]: (k9_mcart_1(A_296, B_298, C_299, D_300, k4_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'))='#skF_7' | ~m1_subset_1('#skF_5', k4_zfmisc_1(A_296, B_298, C_299, D_300)) | k1_xboole_0=D_300 | k1_xboole_0=C_299 | k1_xboole_0=B_298 | k1_xboole_0=A_296)), inference(superposition, [status(thm), theory('equality')], [c_24, c_766])).
% 2.99/1.63  tff(c_777, plain, (![A_301, B_302, C_303, D_304]: (k9_mcart_1(A_301, B_302, C_303, D_304, '#skF_5')='#skF_7' | ~m1_subset_1('#skF_5', k4_zfmisc_1(A_301, B_302, C_303, D_304)) | k1_xboole_0=D_304 | k1_xboole_0=C_303 | k1_xboole_0=B_302 | k1_xboole_0=A_301)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_775])).
% 2.99/1.63  tff(c_786, plain, (k9_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')='#skF_7' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_34, c_777])).
% 2.99/1.63  tff(c_790, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_30, c_28, c_26, c_522, c_786])).
% 2.99/1.63  tff(c_791, plain, (k10_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')!='#skF_8'), inference(splitRight, [status(thm)], [c_516])).
% 2.99/1.63  tff(c_1007, plain, (![F_391, A_390, H_389, C_393, B_392, I_388, G_387, D_394]: (k10_mcart_1(A_390, B_392, C_393, D_394, k4_mcart_1(F_391, G_387, H_389, I_388))=H_389 | ~m1_subset_1(k4_mcart_1(F_391, G_387, H_389, I_388), k4_zfmisc_1(A_390, B_392, C_393, D_394)) | k1_xboole_0=D_394 | k1_xboole_0=C_393 | k1_xboole_0=B_392 | k1_xboole_0=A_390)), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.99/1.63  tff(c_1016, plain, (![A_390, B_392, C_393, D_394]: (k10_mcart_1(A_390, B_392, C_393, D_394, k4_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'))='#skF_8' | ~m1_subset_1('#skF_5', k4_zfmisc_1(A_390, B_392, C_393, D_394)) | k1_xboole_0=D_394 | k1_xboole_0=C_393 | k1_xboole_0=B_392 | k1_xboole_0=A_390)), inference(superposition, [status(thm), theory('equality')], [c_24, c_1007])).
% 2.99/1.63  tff(c_1018, plain, (![A_395, B_396, C_397, D_398]: (k10_mcart_1(A_395, B_396, C_397, D_398, '#skF_5')='#skF_8' | ~m1_subset_1('#skF_5', k4_zfmisc_1(A_395, B_396, C_397, D_398)) | k1_xboole_0=D_398 | k1_xboole_0=C_397 | k1_xboole_0=B_396 | k1_xboole_0=A_395)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_1016])).
% 2.99/1.63  tff(c_1027, plain, (k10_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')='#skF_8' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_34, c_1018])).
% 2.99/1.63  tff(c_1031, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_30, c_28, c_26, c_791, c_1027])).
% 2.99/1.63  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.99/1.63  
% 2.99/1.63  Inference rules
% 2.99/1.63  ----------------------
% 2.99/1.63  #Ref     : 0
% 2.99/1.63  #Sup     : 262
% 2.99/1.63  #Fact    : 0
% 2.99/1.63  #Define  : 0
% 2.99/1.63  #Split   : 3
% 2.99/1.63  #Chain   : 0
% 2.99/1.63  #Close   : 0
% 2.99/1.63  
% 2.99/1.63  Ordering : KBO
% 2.99/1.63  
% 2.99/1.63  Simplification rules
% 2.99/1.63  ----------------------
% 2.99/1.63  #Subsume      : 12
% 2.99/1.63  #Demod        : 187
% 2.99/1.63  #Tautology    : 125
% 2.99/1.63  #SimpNegUnit  : 28
% 2.99/1.63  #BackRed      : 4
% 2.99/1.63  
% 2.99/1.63  #Partial instantiations: 0
% 2.99/1.63  #Strategies tried      : 1
% 2.99/1.63  
% 2.99/1.63  Timing (in seconds)
% 2.99/1.63  ----------------------
% 2.99/1.63  Preprocessing        : 0.30
% 2.99/1.63  Parsing              : 0.15
% 2.99/1.63  CNF conversion       : 0.02
% 2.99/1.63  Main loop            : 0.45
% 2.99/1.63  Inferencing          : 0.18
% 2.99/1.63  Reduction            : 0.14
% 2.99/1.63  Demodulation         : 0.11
% 2.99/1.63  BG Simplification    : 0.03
% 2.99/1.63  Subsumption          : 0.06
% 2.99/1.63  Abstraction          : 0.03
% 2.99/1.63  MUC search           : 0.00
% 2.99/1.63  Cooper               : 0.00
% 2.99/1.63  Total                : 0.77
% 2.99/1.63  Index Insertion      : 0.00
% 2.99/1.63  Index Deletion       : 0.00
% 2.99/1.63  Index Matching       : 0.00
% 2.99/1.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------
