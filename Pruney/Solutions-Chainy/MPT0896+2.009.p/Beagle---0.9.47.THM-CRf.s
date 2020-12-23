%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:46 EST 2020

% Result     : Theorem 9.16s
% Output     : CNFRefutation 9.35s
% Verified   : 
% Statistics : Number of formulae       :  479 (16951 expanded)
%              Number of leaves         :   21 (5140 expanded)
%              Depth                    :   36
%              Number of atoms          :  876 (44513 expanded)
%              Number of equality atoms :  841 (44478 expanded)
%              Maximal formula depth    :   18 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k4_zfmisc_1 > k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k4_zfmisc_1,type,(
    k4_zfmisc_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_80,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G,H] :
        ( k4_zfmisc_1(A,B,C,D) = k4_zfmisc_1(E,F,G,H)
       => ( A = k1_xboole_0
          | B = k1_xboole_0
          | C = k1_xboole_0
          | D = k1_xboole_0
          | ( A = E
            & B = F
            & C = G
            & D = H ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_mcart_1)).

tff(f_37,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B,C,D] : k4_zfmisc_1(A,B,C,D) = k2_zfmisc_1(k3_zfmisc_1(A,B,C),D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0 )
    <=> k3_zfmisc_1(A,B,C) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_mcart_1)).

tff(f_35,axiom,(
    ! [A,B,C,D] :
      ( k2_zfmisc_1(A,B) = k2_zfmisc_1(C,D)
     => ( A = k1_xboole_0
        | B = k1_xboole_0
        | ( A = C
          & B = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_zfmisc_1)).

tff(f_61,axiom,(
    ! [A,B,C,D,E,F] :
      ( k3_zfmisc_1(A,B,C) = k3_zfmisc_1(D,E,F)
     => ( k3_zfmisc_1(A,B,C) = k1_xboole_0
        | ( A = D
          & B = E
          & C = F ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_mcart_1)).

tff(c_30,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_32,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_28,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_26,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_24,plain,
    ( '#skF_8' != '#skF_4'
    | '#skF_7' != '#skF_3'
    | '#skF_6' != '#skF_2'
    | '#skF_5' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_80,plain,(
    '#skF_5' != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_6,plain,(
    ! [A_5,B_6,C_7] : k2_zfmisc_1(k2_zfmisc_1(A_5,B_6),C_7) = k3_zfmisc_1(A_5,B_6,C_7) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_8,plain,(
    ! [A_8,B_9,C_10,D_11] : k2_zfmisc_1(k3_zfmisc_1(A_8,B_9,C_10),D_11) = k4_zfmisc_1(A_8,B_9,C_10,D_11) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_85,plain,(
    ! [A_27,B_28,C_29] : k2_zfmisc_1(k2_zfmisc_1(A_27,B_28),C_29) = k3_zfmisc_1(A_27,B_28,C_29) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_94,plain,(
    ! [A_5,B_6,C_7,C_29] : k3_zfmisc_1(k2_zfmisc_1(A_5,B_6),C_7,C_29) = k2_zfmisc_1(k3_zfmisc_1(A_5,B_6,C_7),C_29) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_85])).

tff(c_228,plain,(
    ! [A_5,B_6,C_7,C_29] : k3_zfmisc_1(k2_zfmisc_1(A_5,B_6),C_7,C_29) = k4_zfmisc_1(A_5,B_6,C_7,C_29) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_94])).

tff(c_34,plain,(
    k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8') = k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_229,plain,(
    ! [A_54,B_55,C_56,C_57] : k3_zfmisc_1(k2_zfmisc_1(A_54,B_55),C_56,C_57) = k4_zfmisc_1(A_54,B_55,C_56,C_57) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_94])).

tff(c_10,plain,(
    ! [A_12,B_13,C_14] :
      ( k3_zfmisc_1(A_12,B_13,C_14) != k1_xboole_0
      | k1_xboole_0 = C_14
      | k1_xboole_0 = B_13
      | k1_xboole_0 = A_12 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_922,plain,(
    ! [A_133,B_134,C_135,C_136] :
      ( k4_zfmisc_1(A_133,B_134,C_135,C_136) != k1_xboole_0
      | k1_xboole_0 = C_136
      | k1_xboole_0 = C_135
      | k2_zfmisc_1(A_133,B_134) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_229,c_10])).

tff(c_940,plain,
    ( k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k2_zfmisc_1('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_922])).

tff(c_966,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_940])).

tff(c_215,plain,(
    ! [D_50,B_51,A_52,C_53] :
      ( D_50 = B_51
      | k1_xboole_0 = B_51
      | k1_xboole_0 = A_52
      | k2_zfmisc_1(C_53,D_50) != k2_zfmisc_1(A_52,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1052,plain,(
    ! [C_152,C_155,D_151,D_156,A_153,B_154] :
      ( D_156 = D_151
      | k1_xboole_0 = D_156
      | k3_zfmisc_1(A_153,B_154,C_155) = k1_xboole_0
      | k4_zfmisc_1(A_153,B_154,C_155,D_156) != k2_zfmisc_1(C_152,D_151) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_215])).

tff(c_1082,plain,(
    ! [D_151,C_152] :
      ( D_151 = '#skF_8'
      | k1_xboole_0 = '#skF_8'
      | k3_zfmisc_1('#skF_5','#skF_6','#skF_7') = k1_xboole_0
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_zfmisc_1(C_152,D_151) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_1052])).

tff(c_1110,plain,(
    k3_zfmisc_1('#skF_5','#skF_6','#skF_7') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_1082])).

tff(c_1162,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_1110,c_10])).

tff(c_1164,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_1162])).

tff(c_1170,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1164,c_966])).

tff(c_16,plain,(
    ! [B_13,C_14] : k3_zfmisc_1(k1_xboole_0,B_13,C_14) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_12,plain,(
    ! [A_12,B_13] : k3_zfmisc_1(A_12,B_13,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_299,plain,(
    ! [A_64,B_65,C_66] : k4_zfmisc_1(A_64,B_65,C_66,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_229,c_12])).

tff(c_116,plain,(
    ! [A_33,B_34,C_35,D_36] : k2_zfmisc_1(k3_zfmisc_1(A_33,B_34,C_35),D_36) = k4_zfmisc_1(A_33,B_34,C_35,D_36) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_134,plain,(
    ! [B_13,C_14,D_36] : k4_zfmisc_1(k1_xboole_0,B_13,C_14,D_36) = k2_zfmisc_1(k1_xboole_0,D_36) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_116])).

tff(c_305,plain,(
    k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_299,c_134])).

tff(c_348,plain,(
    ! [C_7] : k3_zfmisc_1(k1_xboole_0,k1_xboole_0,C_7) = k2_zfmisc_1(k1_xboole_0,C_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_305,c_6])).

tff(c_354,plain,(
    ! [C_7] : k2_zfmisc_1(k1_xboole_0,C_7) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_348])).

tff(c_1149,plain,(
    ! [D_11] : k4_zfmisc_1('#skF_5','#skF_6','#skF_7',D_11) = k2_zfmisc_1(k1_xboole_0,D_11) ),
    inference(superposition,[status(thm),theory(equality)],[c_1110,c_8])).

tff(c_1161,plain,(
    ! [D_11] : k4_zfmisc_1('#skF_5','#skF_6','#skF_7',D_11) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_354,c_1149])).

tff(c_1505,plain,(
    ! [D_11] : k4_zfmisc_1('#skF_5','#skF_6','#skF_7',D_11) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1164,c_1161])).

tff(c_1506,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1505,c_34])).

tff(c_1508,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1170,c_1506])).

tff(c_1509,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_1162])).

tff(c_1547,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_1509])).

tff(c_14,plain,(
    ! [A_12,C_14] : k3_zfmisc_1(A_12,k1_xboole_0,C_14) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_263,plain,(
    ! [A_54,B_55,C_14] : k4_zfmisc_1(A_54,B_55,k1_xboole_0,C_14) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_229])).

tff(c_1567,plain,(
    ! [A_54,B_55,C_14] : k4_zfmisc_1(A_54,B_55,'#skF_7',C_14) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1547,c_1547,c_263])).

tff(c_1837,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1567,c_34])).

tff(c_1555,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1547,c_966])).

tff(c_1883,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1837,c_1555])).

tff(c_1884,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_1509])).

tff(c_1894,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1884,c_966])).

tff(c_2253,plain,(
    ! [D_11] : k4_zfmisc_1('#skF_5','#skF_6','#skF_7',D_11) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1884,c_1161])).

tff(c_2254,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2253,c_34])).

tff(c_2256,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1894,c_2254])).

tff(c_2257,plain,(
    ! [D_151,C_152] :
      ( k1_xboole_0 = '#skF_8'
      | D_151 = '#skF_8'
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_zfmisc_1(C_152,D_151) ) ),
    inference(splitRight,[status(thm)],[c_1082])).

tff(c_2259,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_2257])).

tff(c_242,plain,(
    ! [A_54,B_55,C_56] : k4_zfmisc_1(A_54,B_55,C_56,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_229,c_12])).

tff(c_2302,plain,(
    ! [A_54,B_55,C_56] : k4_zfmisc_1(A_54,B_55,C_56,'#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2259,c_2259,c_242])).

tff(c_2555,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2302,c_34])).

tff(c_2286,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2259,c_966])).

tff(c_2648,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2555,c_2286])).

tff(c_2651,plain,(
    ! [D_295,C_296] :
      ( D_295 = '#skF_8'
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_zfmisc_1(C_296,D_295) ) ),
    inference(splitRight,[status(thm)],[c_2257])).

tff(c_2660,plain,(
    ! [D_11,A_8,B_9,C_10] :
      ( D_11 = '#skF_8'
      | k4_zfmisc_1(A_8,B_9,C_10,D_11) != k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_2651])).

tff(c_2705,plain,(
    '#skF_8' = '#skF_4' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_2660])).

tff(c_2732,plain,(
    k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_4') = k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2705,c_34])).

tff(c_270,plain,(
    ! [E_62,D_59,F_61,A_63,C_58,B_60] :
      ( E_62 = B_60
      | k3_zfmisc_1(A_63,B_60,C_58) = k1_xboole_0
      | k3_zfmisc_1(D_59,E_62,F_61) != k3_zfmisc_1(A_63,B_60,C_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_276,plain,(
    ! [B_6,C_29,C_7,E_62,D_59,A_5,F_61] :
      ( E_62 = C_7
      | k3_zfmisc_1(k2_zfmisc_1(A_5,B_6),C_7,C_29) = k1_xboole_0
      | k4_zfmisc_1(A_5,B_6,C_7,C_29) != k3_zfmisc_1(D_59,E_62,F_61) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_228,c_270])).

tff(c_3129,plain,(
    ! [A_364,D_366,C_361,E_365,F_360,C_363,B_362] :
      ( E_365 = C_363
      | k4_zfmisc_1(A_364,B_362,C_363,C_361) = k1_xboole_0
      | k4_zfmisc_1(A_364,B_362,C_363,C_361) != k3_zfmisc_1(D_366,E_365,F_360) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_228,c_276])).

tff(c_3135,plain,(
    ! [E_365,D_366,F_360] :
      ( E_365 = '#skF_7'
      | k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_4') = k1_xboole_0
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k3_zfmisc_1(D_366,E_365,F_360) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2732,c_3129])).

tff(c_3167,plain,(
    ! [E_365,D_366,F_360] :
      ( E_365 = '#skF_7'
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = k1_xboole_0
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k3_zfmisc_1(D_366,E_365,F_360) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2732,c_3135])).

tff(c_3215,plain,(
    ! [E_373,D_374,F_375] :
      ( E_373 = '#skF_7'
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k3_zfmisc_1(D_374,E_373,F_375) ) ),
    inference(negUnitSimplification,[status(thm)],[c_966,c_3167])).

tff(c_3221,plain,(
    ! [C_7,A_5,B_6,C_29] :
      ( C_7 = '#skF_7'
      | k4_zfmisc_1(A_5,B_6,C_7,C_29) != k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_228,c_3215])).

tff(c_3233,plain,(
    '#skF_7' = '#skF_3' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_3221])).

tff(c_2258,plain,(
    k3_zfmisc_1('#skF_5','#skF_6','#skF_7') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1082])).

tff(c_169,plain,(
    ! [C_43,A_44,B_45,D_46] :
      ( C_43 = A_44
      | k1_xboole_0 = B_45
      | k1_xboole_0 = A_44
      | k2_zfmisc_1(C_43,D_46) != k2_zfmisc_1(A_44,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_3174,plain,(
    ! [C_367,D_372,D_368,C_371,A_369,B_370] :
      ( k3_zfmisc_1(A_369,B_370,C_371) = C_367
      | k1_xboole_0 = D_372
      | k3_zfmisc_1(A_369,B_370,C_371) = k1_xboole_0
      | k4_zfmisc_1(A_369,B_370,C_371,D_372) != k2_zfmisc_1(C_367,D_368) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_169])).

tff(c_3180,plain,(
    ! [C_367,D_368] :
      ( k3_zfmisc_1('#skF_5','#skF_6','#skF_7') = C_367
      | k1_xboole_0 = '#skF_4'
      | k3_zfmisc_1('#skF_5','#skF_6','#skF_7') = k1_xboole_0
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_zfmisc_1(C_367,D_368) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2732,c_3174])).

tff(c_3209,plain,(
    ! [C_367,D_368] :
      ( k3_zfmisc_1('#skF_5','#skF_6','#skF_7') = C_367
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_zfmisc_1(C_367,D_368) ) ),
    inference(negUnitSimplification,[status(thm)],[c_2258,c_26,c_3180])).

tff(c_3267,plain,(
    ! [C_380,D_381] :
      ( k3_zfmisc_1('#skF_5','#skF_6','#skF_3') = C_380
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_zfmisc_1(C_380,D_381) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3233,c_3209])).

tff(c_3276,plain,(
    ! [A_8,B_9,C_10,D_11] :
      ( k3_zfmisc_1(A_8,B_9,C_10) = k3_zfmisc_1('#skF_5','#skF_6','#skF_3')
      | k4_zfmisc_1(A_8,B_9,C_10,D_11) != k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_3267])).

tff(c_3559,plain,(
    k3_zfmisc_1('#skF_5','#skF_6','#skF_3') = k3_zfmisc_1('#skF_1','#skF_2','#skF_3') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_3276])).

tff(c_3261,plain,(
    k3_zfmisc_1('#skF_5','#skF_6','#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3233,c_2258])).

tff(c_3594,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3559,c_3261])).

tff(c_3645,plain,(
    ! [D_11] : k2_zfmisc_1(k3_zfmisc_1('#skF_1','#skF_2','#skF_3'),D_11) = k4_zfmisc_1('#skF_5','#skF_6','#skF_3',D_11) ),
    inference(superposition,[status(thm),theory(equality)],[c_3559,c_8])).

tff(c_3665,plain,(
    ! [D_421] : k4_zfmisc_1('#skF_5','#skF_6','#skF_3',D_421) = k4_zfmisc_1('#skF_1','#skF_2','#skF_3',D_421) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_3645])).

tff(c_238,plain,(
    ! [A_54,B_55,C_56,C_57] :
      ( k4_zfmisc_1(A_54,B_55,C_56,C_57) != k1_xboole_0
      | k1_xboole_0 = C_57
      | k1_xboole_0 = C_56
      | k2_zfmisc_1(A_54,B_55) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_229,c_10])).

tff(c_3709,plain,(
    ! [D_421] :
      ( k4_zfmisc_1('#skF_1','#skF_2','#skF_3',D_421) != k1_xboole_0
      | k1_xboole_0 = D_421
      | k1_xboole_0 = '#skF_3'
      | k2_zfmisc_1('#skF_5','#skF_6') = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3665,c_238])).

tff(c_3736,plain,(
    ! [D_421] :
      ( k4_zfmisc_1('#skF_1','#skF_2','#skF_3',D_421) != k1_xboole_0
      | k1_xboole_0 = D_421
      | k2_zfmisc_1('#skF_5','#skF_6') = k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_3709])).

tff(c_3746,plain,(
    k2_zfmisc_1('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_3736])).

tff(c_3772,plain,(
    ! [C_7] : k3_zfmisc_1('#skF_5','#skF_6',C_7) = k2_zfmisc_1(k1_xboole_0,C_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_3746,c_6])).

tff(c_3779,plain,(
    ! [C_7] : k3_zfmisc_1('#skF_5','#skF_6',C_7) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_354,c_3772])).

tff(c_3782,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3779,c_3559])).

tff(c_3784,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3594,c_3782])).

tff(c_3786,plain,(
    k2_zfmisc_1('#skF_5','#skF_6') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_3736])).

tff(c_181,plain,(
    ! [B_6,C_7,C_43,A_5,D_46] :
      ( k2_zfmisc_1(A_5,B_6) = C_43
      | k1_xboole_0 = C_7
      | k2_zfmisc_1(A_5,B_6) = k1_xboole_0
      | k3_zfmisc_1(A_5,B_6,C_7) != k2_zfmisc_1(C_43,D_46) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_169])).

tff(c_3610,plain,(
    ! [C_43,D_46] :
      ( k2_zfmisc_1('#skF_5','#skF_6') = C_43
      | k1_xboole_0 = '#skF_3'
      | k2_zfmisc_1('#skF_5','#skF_6') = k1_xboole_0
      | k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != k2_zfmisc_1(C_43,D_46) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3559,c_181])).

tff(c_3654,plain,(
    ! [C_43,D_46] :
      ( k2_zfmisc_1('#skF_5','#skF_6') = C_43
      | k2_zfmisc_1('#skF_5','#skF_6') = k1_xboole_0
      | k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != k2_zfmisc_1(C_43,D_46) ) ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_3610])).

tff(c_4055,plain,(
    ! [C_465,D_466] :
      ( k2_zfmisc_1('#skF_5','#skF_6') = C_465
      | k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != k2_zfmisc_1(C_465,D_466) ) ),
    inference(negUnitSimplification,[status(thm)],[c_3786,c_3654])).

tff(c_4067,plain,(
    ! [A_5,B_6,C_7] :
      ( k2_zfmisc_1(A_5,B_6) = k2_zfmisc_1('#skF_5','#skF_6')
      | k3_zfmisc_1(A_5,B_6,C_7) != k3_zfmisc_1('#skF_1','#skF_2','#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_4055])).

tff(c_4071,plain,(
    k2_zfmisc_1('#skF_5','#skF_6') = k2_zfmisc_1('#skF_1','#skF_2') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_4067])).

tff(c_4127,plain,(
    ! [C_7] : k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),C_7) = k3_zfmisc_1('#skF_5','#skF_6',C_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_4071,c_6])).

tff(c_4135,plain,(
    ! [C_470] : k3_zfmisc_1('#skF_5','#skF_6',C_470) = k3_zfmisc_1('#skF_1','#skF_2',C_470) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_4127])).

tff(c_4223,plain,(
    ! [C_470] :
      ( k3_zfmisc_1('#skF_1','#skF_2',C_470) != k1_xboole_0
      | k1_xboole_0 = C_470
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_5' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4135,c_10])).

tff(c_4391,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_4223])).

tff(c_4101,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4071,c_3786])).

tff(c_4394,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4391,c_4101])).

tff(c_4431,plain,(
    ! [C_7] : k2_zfmisc_1('#skF_5',C_7) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4391,c_4391,c_354])).

tff(c_4471,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4431,c_4071])).

tff(c_4563,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4394,c_4471])).

tff(c_4565,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_4223])).

tff(c_4564,plain,(
    ! [C_470] :
      ( k1_xboole_0 = '#skF_6'
      | k3_zfmisc_1('#skF_1','#skF_2',C_470) != k1_xboole_0
      | k1_xboole_0 = C_470 ) ),
    inference(splitRight,[status(thm)],[c_4223])).

tff(c_4566,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_4564])).

tff(c_4570,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4566,c_4101])).

tff(c_2,plain,(
    ! [D_4,B_2,A_1,C_3] :
      ( D_4 = B_2
      | k1_xboole_0 = B_2
      | k1_xboole_0 = A_1
      | k2_zfmisc_1(C_3,D_4) != k2_zfmisc_1(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_547,plain,(
    ! [B_91,A_92] :
      ( k1_xboole_0 = B_91
      | k1_xboole_0 = B_91
      | k1_xboole_0 = A_92
      | k2_zfmisc_1(A_92,B_91) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_305,c_2])).

tff(c_591,plain,(
    ! [C_101,A_102,B_103] :
      ( k1_xboole_0 = C_101
      | k1_xboole_0 = C_101
      | k2_zfmisc_1(A_102,B_103) = k1_xboole_0
      | k3_zfmisc_1(A_102,B_103,C_101) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_547])).

tff(c_607,plain,(
    ! [C_14,A_12] :
      ( k1_xboole_0 = C_14
      | k2_zfmisc_1(A_12,k1_xboole_0) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_591])).

tff(c_695,plain,(
    ! [A_12] : k2_zfmisc_1(A_12,k1_xboole_0) = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_607])).

tff(c_4600,plain,(
    ! [A_12] : k2_zfmisc_1(A_12,'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4566,c_4566,c_695])).

tff(c_4676,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4600,c_4071])).

tff(c_4678,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4570,c_4676])).

tff(c_4680,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_4564])).

tff(c_4118,plain,(
    ! [D_4,C_3] :
      ( D_4 = '#skF_6'
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_5'
      | k2_zfmisc_1(C_3,D_4) != k2_zfmisc_1('#skF_1','#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4071,c_2])).

tff(c_4791,plain,(
    ! [D_4,C_3] :
      ( D_4 = '#skF_6'
      | k2_zfmisc_1(C_3,D_4) != k2_zfmisc_1('#skF_1','#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_4565,c_4680,c_4118])).

tff(c_4794,plain,(
    '#skF_6' = '#skF_2' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_4791])).

tff(c_4818,plain,(
    k2_zfmisc_1('#skF_5','#skF_2') = k2_zfmisc_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4794,c_4071])).

tff(c_4,plain,(
    ! [C_3,A_1,B_2,D_4] :
      ( C_3 = A_1
      | k1_xboole_0 = B_2
      | k1_xboole_0 = A_1
      | k2_zfmisc_1(C_3,D_4) != k2_zfmisc_1(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_4845,plain,(
    ! [C_3,D_4] :
      ( C_3 = '#skF_5'
      | k1_xboole_0 = '#skF_2'
      | k1_xboole_0 = '#skF_5'
      | k2_zfmisc_1(C_3,D_4) != k2_zfmisc_1('#skF_1','#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4818,c_4])).

tff(c_4856,plain,(
    ! [C_3,D_4] :
      ( C_3 = '#skF_5'
      | k2_zfmisc_1(C_3,D_4) != k2_zfmisc_1('#skF_1','#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_4565,c_30,c_4845])).

tff(c_5062,plain,(
    '#skF_5' = '#skF_1' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_4856])).

tff(c_5064,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_5062])).

tff(c_5066,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_940])).

tff(c_5072,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_5066,c_238])).

tff(c_5080,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_26,c_5072])).

tff(c_398,plain,(
    ! [C_73] : k2_zfmisc_1(k1_xboole_0,C_73) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_348])).

tff(c_406,plain,(
    ! [C_73,B_2,A_1] :
      ( C_73 = B_2
      | k1_xboole_0 = B_2
      | k1_xboole_0 = A_1
      | k2_zfmisc_1(A_1,B_2) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_398,c_2])).

tff(c_5089,plain,(
    ! [C_73] :
      ( C_73 = '#skF_2'
      | k1_xboole_0 = '#skF_2'
      | k1_xboole_0 = '#skF_1' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5080,c_406])).

tff(c_5122,plain,(
    ! [C_527] : C_527 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_30,c_5089])).

tff(c_5148,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_5122,c_5080])).

tff(c_5284,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_5148])).

tff(c_5287,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_607])).

tff(c_5285,plain,(
    ! [C_14] : k1_xboole_0 = C_14 ),
    inference(splitRight,[status(thm)],[c_607])).

tff(c_5357,plain,(
    ! [C_979] : C_979 = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_5287,c_5285])).

tff(c_5423,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_5357,c_30])).

tff(c_5424,plain,
    ( '#skF_6' != '#skF_2'
    | '#skF_7' != '#skF_3'
    | '#skF_8' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_5430,plain,(
    '#skF_8' != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_5424])).

tff(c_5431,plain,(
    ! [A_1106,B_1107,C_1108] : k2_zfmisc_1(k2_zfmisc_1(A_1106,B_1107),C_1108) = k3_zfmisc_1(A_1106,B_1107,C_1108) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_5440,plain,(
    ! [A_5,B_6,C_7,C_1108] : k3_zfmisc_1(k2_zfmisc_1(A_5,B_6),C_7,C_1108) = k2_zfmisc_1(k3_zfmisc_1(A_5,B_6,C_7),C_1108) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_5431])).

tff(c_5579,plain,(
    ! [A_5,B_6,C_7,C_1108] : k3_zfmisc_1(k2_zfmisc_1(A_5,B_6),C_7,C_1108) = k4_zfmisc_1(A_5,B_6,C_7,C_1108) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_5440])).

tff(c_5425,plain,(
    '#skF_5' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_5446,plain,(
    k4_zfmisc_1('#skF_1','#skF_6','#skF_7','#skF_8') = k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5425,c_34])).

tff(c_5580,plain,(
    ! [A_1133,B_1134,C_1135,C_1136] : k3_zfmisc_1(k2_zfmisc_1(A_1133,B_1134),C_1135,C_1136) = k4_zfmisc_1(A_1133,B_1134,C_1135,C_1136) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_5440])).

tff(c_6274,plain,(
    ! [A_1212,B_1213,C_1214,C_1215] :
      ( k4_zfmisc_1(A_1212,B_1213,C_1214,C_1215) != k1_xboole_0
      | k1_xboole_0 = C_1215
      | k1_xboole_0 = C_1214
      | k2_zfmisc_1(A_1212,B_1213) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5580,c_10])).

tff(c_6292,plain,
    ( k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k2_zfmisc_1('#skF_1','#skF_6') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_5446,c_6274])).

tff(c_6317,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_6292])).

tff(c_5652,plain,(
    ! [B_1142,D_1141,C_1140,F_1143,A_1145,E_1144] :
      ( F_1143 = C_1140
      | k3_zfmisc_1(A_1145,B_1142,C_1140) = k1_xboole_0
      | k3_zfmisc_1(D_1141,E_1144,F_1143) != k3_zfmisc_1(A_1145,B_1142,C_1140) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_5658,plain,(
    ! [B_6,C_7,C_1108,A_5,D_1141,F_1143,E_1144] :
      ( F_1143 = C_1108
      | k3_zfmisc_1(k2_zfmisc_1(A_5,B_6),C_7,C_1108) = k1_xboole_0
      | k4_zfmisc_1(A_5,B_6,C_7,C_1108) != k3_zfmisc_1(D_1141,E_1144,F_1143) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5579,c_5652])).

tff(c_6858,plain,(
    ! [C_1301,E_1299,F_1303,D_1304,B_1300,C_1298,A_1302] :
      ( F_1303 = C_1298
      | k4_zfmisc_1(A_1302,B_1300,C_1301,C_1298) = k1_xboole_0
      | k4_zfmisc_1(A_1302,B_1300,C_1301,C_1298) != k3_zfmisc_1(D_1304,E_1299,F_1303) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5579,c_5658])).

tff(c_6885,plain,(
    ! [F_1303,D_1304,E_1299] :
      ( F_1303 = '#skF_8'
      | k4_zfmisc_1('#skF_1','#skF_6','#skF_7','#skF_8') = k1_xboole_0
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k3_zfmisc_1(D_1304,E_1299,F_1303) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5446,c_6858])).

tff(c_6901,plain,(
    ! [F_1303,D_1304,E_1299] :
      ( F_1303 = '#skF_8'
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = k1_xboole_0
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k3_zfmisc_1(D_1304,E_1299,F_1303) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5446,c_6885])).

tff(c_6903,plain,(
    ! [F_1305,D_1306,E_1307] :
      ( F_1305 = '#skF_8'
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k3_zfmisc_1(D_1306,E_1307,F_1305) ) ),
    inference(negUnitSimplification,[status(thm)],[c_6317,c_6901])).

tff(c_6909,plain,(
    ! [C_1108,A_5,B_6,C_7] :
      ( C_1108 = '#skF_8'
      | k4_zfmisc_1(A_5,B_6,C_7,C_1108) != k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5579,c_6903])).

tff(c_6961,plain,(
    '#skF_8' = '#skF_4' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_6909])).

tff(c_6963,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5430,c_6961])).

tff(c_6965,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_6292])).

tff(c_5586,plain,(
    ! [A_1133,B_1134,C_1135,C_1136] :
      ( k4_zfmisc_1(A_1133,B_1134,C_1135,C_1136) != k1_xboole_0
      | k1_xboole_0 = C_1136
      | k1_xboole_0 = C_1135
      | k2_zfmisc_1(A_1133,B_1134) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5580,c_10])).

tff(c_6971,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_6965,c_5586])).

tff(c_6979,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_26,c_6971])).

tff(c_5617,plain,(
    ! [A_1137,B_1138,C_1139] : k4_zfmisc_1(A_1137,B_1138,C_1139,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_5580,c_12])).

tff(c_5451,plain,(
    ! [A_1109,B_1110,C_1111,D_1112] : k2_zfmisc_1(k3_zfmisc_1(A_1109,B_1110,C_1111),D_1112) = k4_zfmisc_1(A_1109,B_1110,C_1111,D_1112) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_5469,plain,(
    ! [B_13,C_14,D_1112] : k4_zfmisc_1(k1_xboole_0,B_13,C_14,D_1112) = k2_zfmisc_1(k1_xboole_0,D_1112) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_5451])).

tff(c_5623,plain,(
    k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_5617,c_5469])).

tff(c_5699,plain,(
    ! [C_7] : k3_zfmisc_1(k1_xboole_0,k1_xboole_0,C_7) = k2_zfmisc_1(k1_xboole_0,C_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_5623,c_6])).

tff(c_5749,plain,(
    ! [C_1152] : k2_zfmisc_1(k1_xboole_0,C_1152) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_5699])).

tff(c_5763,plain,(
    ! [C_1152,B_2,A_1] :
      ( C_1152 = B_2
      | k1_xboole_0 = B_2
      | k1_xboole_0 = A_1
      | k2_zfmisc_1(A_1,B_2) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5749,c_2])).

tff(c_6988,plain,(
    ! [C_1152] :
      ( C_1152 = '#skF_2'
      | k1_xboole_0 = '#skF_2'
      | k1_xboole_0 = '#skF_1' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6979,c_5763])).

tff(c_7021,plain,(
    ! [C_1314] : C_1314 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_30,c_6988])).

tff(c_7047,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_7021,c_6979])).

tff(c_7183,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_7047])).

tff(c_7184,plain,
    ( '#skF_7' != '#skF_3'
    | '#skF_6' != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_5424])).

tff(c_7190,plain,(
    '#skF_6' != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_7184])).

tff(c_7191,plain,(
    ! [A_1648,B_1649,C_1650] : k2_zfmisc_1(k2_zfmisc_1(A_1648,B_1649),C_1650) = k3_zfmisc_1(A_1648,B_1649,C_1650) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_7200,plain,(
    ! [A_5,B_6,C_7,C_1650] : k3_zfmisc_1(k2_zfmisc_1(A_5,B_6),C_7,C_1650) = k2_zfmisc_1(k3_zfmisc_1(A_5,B_6,C_7),C_1650) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_7191])).

tff(c_7339,plain,(
    ! [A_5,B_6,C_7,C_1650] : k3_zfmisc_1(k2_zfmisc_1(A_5,B_6),C_7,C_1650) = k4_zfmisc_1(A_5,B_6,C_7,C_1650) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_7200])).

tff(c_7185,plain,(
    '#skF_8' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_5424])).

tff(c_7206,plain,(
    k4_zfmisc_1('#skF_1','#skF_6','#skF_7','#skF_4') = k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7185,c_5425,c_34])).

tff(c_7340,plain,(
    ! [A_1675,B_1676,C_1677,C_1678] : k3_zfmisc_1(k2_zfmisc_1(A_1675,B_1676),C_1677,C_1678) = k4_zfmisc_1(A_1675,B_1676,C_1677,C_1678) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_7200])).

tff(c_7971,plain,(
    ! [A_1749,B_1750,C_1751,C_1752] :
      ( k4_zfmisc_1(A_1749,B_1750,C_1751,C_1752) != k1_xboole_0
      | k1_xboole_0 = C_1752
      | k1_xboole_0 = C_1751
      | k2_zfmisc_1(A_1749,B_1750) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7340,c_10])).

tff(c_7986,plain,
    ( k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_7'
    | k2_zfmisc_1('#skF_1','#skF_6') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_7206,c_7971])).

tff(c_7995,plain,
    ( k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_7'
    | k2_zfmisc_1('#skF_1','#skF_6') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_7986])).

tff(c_7996,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_7995])).

tff(c_7558,plain,(
    ! [E_1702,C_1698,A_1703,B_1700,F_1701,D_1699] :
      ( E_1702 = B_1700
      | k3_zfmisc_1(A_1703,B_1700,C_1698) = k1_xboole_0
      | k3_zfmisc_1(D_1699,E_1702,F_1701) != k3_zfmisc_1(A_1703,B_1700,C_1698) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_7564,plain,(
    ! [B_6,C_7,E_1702,F_1701,A_5,D_1699,C_1650] :
      ( E_1702 = C_7
      | k3_zfmisc_1(k2_zfmisc_1(A_5,B_6),C_7,C_1650) = k1_xboole_0
      | k4_zfmisc_1(A_5,B_6,C_7,C_1650) != k3_zfmisc_1(D_1699,E_1702,F_1701) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7339,c_7558])).

tff(c_9604,plain,(
    ! [C_1926,B_1925,F_1929,A_1928,C_1924,D_1927,E_1930] :
      ( E_1930 = C_1926
      | k4_zfmisc_1(A_1928,B_1925,C_1926,C_1924) = k1_xboole_0
      | k4_zfmisc_1(A_1928,B_1925,C_1926,C_1924) != k3_zfmisc_1(D_1927,E_1930,F_1929) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7339,c_7564])).

tff(c_9631,plain,(
    ! [E_1930,D_1927,F_1929] :
      ( E_1930 = '#skF_7'
      | k4_zfmisc_1('#skF_1','#skF_6','#skF_7','#skF_4') = k1_xboole_0
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k3_zfmisc_1(D_1927,E_1930,F_1929) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7206,c_9604])).

tff(c_9647,plain,(
    ! [E_1930,D_1927,F_1929] :
      ( E_1930 = '#skF_7'
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = k1_xboole_0
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k3_zfmisc_1(D_1927,E_1930,F_1929) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7206,c_9631])).

tff(c_9649,plain,(
    ! [E_1931,D_1932,F_1933] :
      ( E_1931 = '#skF_7'
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k3_zfmisc_1(D_1932,E_1931,F_1933) ) ),
    inference(negUnitSimplification,[status(thm)],[c_7996,c_9647])).

tff(c_9655,plain,(
    ! [C_7,A_5,B_6,C_1650] :
      ( C_7 = '#skF_7'
      | k4_zfmisc_1(A_5,B_6,C_7,C_1650) != k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7339,c_9649])).

tff(c_9667,plain,(
    '#skF_7' = '#skF_3' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_9655])).

tff(c_7280,plain,(
    ! [D_1664,B_1665,A_1666,C_1667] :
      ( D_1664 = B_1665
      | k1_xboole_0 = B_1665
      | k1_xboole_0 = A_1666
      | k2_zfmisc_1(C_1667,D_1664) != k2_zfmisc_1(A_1666,B_1665) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_8371,plain,(
    ! [C_1806,A_1804,B_1805,C_1807,D_1808,D_1803] :
      ( D_1808 = D_1803
      | k1_xboole_0 = D_1808
      | k3_zfmisc_1(A_1804,B_1805,C_1807) = k1_xboole_0
      | k4_zfmisc_1(A_1804,B_1805,C_1807,D_1808) != k2_zfmisc_1(C_1806,D_1803) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_7280])).

tff(c_8401,plain,(
    ! [D_1803,C_1806] :
      ( D_1803 = '#skF_4'
      | k1_xboole_0 = '#skF_4'
      | k3_zfmisc_1('#skF_1','#skF_6','#skF_7') = k1_xboole_0
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_zfmisc_1(C_1806,D_1803) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7206,c_8371])).

tff(c_8411,plain,(
    ! [D_1803,C_1806] :
      ( D_1803 = '#skF_4'
      | k3_zfmisc_1('#skF_1','#skF_6','#skF_7') = k1_xboole_0
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_zfmisc_1(C_1806,D_1803) ) ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_8401])).

tff(c_8412,plain,(
    k3_zfmisc_1('#skF_1','#skF_6','#skF_7') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_8411])).

tff(c_8465,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_8412,c_10])).

tff(c_8478,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_8465])).

tff(c_8480,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_8478])).

tff(c_8489,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8480,c_7996])).

tff(c_7227,plain,(
    ! [A_1654,B_1655,C_1656,D_1657] : k2_zfmisc_1(k3_zfmisc_1(A_1654,B_1655,C_1656),D_1657) = k4_zfmisc_1(A_1654,B_1655,C_1656,D_1657) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_7242,plain,(
    ! [A_12,C_14,D_1657] : k4_zfmisc_1(A_12,k1_xboole_0,C_14,D_1657) = k2_zfmisc_1(k1_xboole_0,D_1657) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_7227])).

tff(c_7377,plain,(
    ! [A_1679,B_1680,C_1681] : k4_zfmisc_1(A_1679,B_1680,C_1681,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_7340,c_12])).

tff(c_7245,plain,(
    ! [B_13,C_14,D_1657] : k4_zfmisc_1(k1_xboole_0,B_13,C_14,D_1657) = k2_zfmisc_1(k1_xboole_0,D_1657) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_7227])).

tff(c_7383,plain,(
    k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_7377,c_7245])).

tff(c_7411,plain,(
    ! [C_7,C_1650] : k4_zfmisc_1(k1_xboole_0,k1_xboole_0,C_7,C_1650) = k3_zfmisc_1(k1_xboole_0,C_7,C_1650) ),
    inference(superposition,[status(thm),theory(equality)],[c_7383,c_7339])).

tff(c_7429,plain,(
    ! [C_1650] : k2_zfmisc_1(k1_xboole_0,C_1650) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_7242,c_16,c_7411])).

tff(c_8462,plain,(
    ! [D_11] : k4_zfmisc_1('#skF_1','#skF_6','#skF_7',D_11) = k2_zfmisc_1(k1_xboole_0,D_11) ),
    inference(superposition,[status(thm),theory(equality)],[c_8412,c_8])).

tff(c_8475,plain,(
    ! [D_11] : k4_zfmisc_1('#skF_1','#skF_6','#skF_7',D_11) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_7429,c_8462])).

tff(c_8862,plain,(
    ! [D_11] : k4_zfmisc_1('#skF_1','#skF_6','#skF_7',D_11) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8480,c_8475])).

tff(c_8863,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8862,c_7206])).

tff(c_8865,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8489,c_8863])).

tff(c_8866,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_8478])).

tff(c_8876,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8866,c_7996])).

tff(c_7374,plain,(
    ! [A_1675,B_1676,C_14] : k4_zfmisc_1(A_1675,B_1676,k1_xboole_0,C_14) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_7340])).

tff(c_8888,plain,(
    ! [A_1675,B_1676,C_14] : k4_zfmisc_1(A_1675,B_1676,'#skF_7',C_14) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8866,c_8866,c_7374])).

tff(c_9222,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8888,c_7206])).

tff(c_9224,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8876,c_9222])).

tff(c_9226,plain,(
    k3_zfmisc_1('#skF_1','#skF_6','#skF_7') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_8411])).

tff(c_7326,plain,(
    ! [C_1671,A_1672,B_1673,D_1674] :
      ( C_1671 = A_1672
      | k1_xboole_0 = B_1673
      | k1_xboole_0 = A_1672
      | k2_zfmisc_1(C_1671,D_1674) != k2_zfmisc_1(A_1672,B_1673) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_9393,plain,(
    ! [D_1898,B_1896,C_1893,D_1894,C_1897,A_1895] :
      ( k3_zfmisc_1(A_1895,B_1896,C_1897) = C_1893
      | k1_xboole_0 = D_1898
      | k3_zfmisc_1(A_1895,B_1896,C_1897) = k1_xboole_0
      | k4_zfmisc_1(A_1895,B_1896,C_1897,D_1898) != k2_zfmisc_1(C_1893,D_1894) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_7326])).

tff(c_9423,plain,(
    ! [C_1893,D_1894] :
      ( k3_zfmisc_1('#skF_1','#skF_6','#skF_7') = C_1893
      | k1_xboole_0 = '#skF_4'
      | k3_zfmisc_1('#skF_1','#skF_6','#skF_7') = k1_xboole_0
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_zfmisc_1(C_1893,D_1894) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7206,c_9393])).

tff(c_9434,plain,(
    ! [C_1899,D_1900] :
      ( k3_zfmisc_1('#skF_1','#skF_6','#skF_7') = C_1899
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_zfmisc_1(C_1899,D_1900) ) ),
    inference(negUnitSimplification,[status(thm)],[c_9226,c_26,c_9423])).

tff(c_9443,plain,(
    ! [A_8,B_9,C_10,D_11] :
      ( k3_zfmisc_1(A_8,B_9,C_10) = k3_zfmisc_1('#skF_1','#skF_6','#skF_7')
      | k4_zfmisc_1(A_8,B_9,C_10,D_11) != k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_9434])).

tff(c_9694,plain,(
    k3_zfmisc_1('#skF_1','#skF_6','#skF_7') = k3_zfmisc_1('#skF_1','#skF_2','#skF_3') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_9443])).

tff(c_9738,plain,(
    k3_zfmisc_1('#skF_1','#skF_6','#skF_3') = k3_zfmisc_1('#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9667,c_9694])).

tff(c_9789,plain,(
    ! [D_11] : k2_zfmisc_1(k3_zfmisc_1('#skF_1','#skF_2','#skF_3'),D_11) = k4_zfmisc_1('#skF_1','#skF_6','#skF_3',D_11) ),
    inference(superposition,[status(thm),theory(equality)],[c_9738,c_8])).

tff(c_9912,plain,(
    ! [D_1949] : k4_zfmisc_1('#skF_1','#skF_6','#skF_3',D_1949) = k4_zfmisc_1('#skF_1','#skF_2','#skF_3',D_1949) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_9789])).

tff(c_7349,plain,(
    ! [A_1675,B_1676,C_1677,C_1678] :
      ( k4_zfmisc_1(A_1675,B_1676,C_1677,C_1678) != k1_xboole_0
      | k1_xboole_0 = C_1678
      | k1_xboole_0 = C_1677
      | k2_zfmisc_1(A_1675,B_1676) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7340,c_10])).

tff(c_9953,plain,(
    ! [D_1949] :
      ( k4_zfmisc_1('#skF_1','#skF_2','#skF_3',D_1949) != k1_xboole_0
      | k1_xboole_0 = D_1949
      | k1_xboole_0 = '#skF_3'
      | k2_zfmisc_1('#skF_1','#skF_6') = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9912,c_7349])).

tff(c_9980,plain,(
    ! [D_1949] :
      ( k4_zfmisc_1('#skF_1','#skF_2','#skF_3',D_1949) != k1_xboole_0
      | k1_xboole_0 = D_1949
      | k2_zfmisc_1('#skF_1','#skF_6') = k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_9953])).

tff(c_10034,plain,(
    k2_zfmisc_1('#skF_1','#skF_6') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_9980])).

tff(c_7509,plain,(
    ! [C_1694] : k2_zfmisc_1(k1_xboole_0,C_1694) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_7242,c_16,c_7411])).

tff(c_7523,plain,(
    ! [C_1694,B_2,A_1] :
      ( C_1694 = B_2
      | k1_xboole_0 = B_2
      | k1_xboole_0 = A_1
      | k2_zfmisc_1(A_1,B_2) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7509,c_2])).

tff(c_10087,plain,(
    ! [C_1694] :
      ( C_1694 = '#skF_6'
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_1' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10034,c_7523])).

tff(c_10114,plain,(
    ! [C_1694] :
      ( C_1694 = '#skF_6'
      | k1_xboole_0 = '#skF_6' ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_10087])).

tff(c_10120,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_10114])).

tff(c_9732,plain,(
    k3_zfmisc_1('#skF_1','#skF_6','#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_9667,c_9226])).

tff(c_9739,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_9738,c_9732])).

tff(c_10125,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10120,c_9739])).

tff(c_10105,plain,(
    ! [C_7] : k3_zfmisc_1('#skF_1','#skF_6',C_7) = k2_zfmisc_1(k1_xboole_0,C_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_10034,c_6])).

tff(c_10118,plain,(
    ! [C_7] : k3_zfmisc_1('#skF_1','#skF_6',C_7) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_7429,c_10105])).

tff(c_10341,plain,(
    ! [C_7] : k3_zfmisc_1('#skF_1','#skF_6',C_7) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10120,c_10118])).

tff(c_10342,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10341,c_9738])).

tff(c_10440,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10125,c_10342])).

tff(c_10441,plain,(
    ! [C_1694] : C_1694 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_10114])).

tff(c_10442,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_10114])).

tff(c_10738,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_10441,c_10442])).

tff(c_10740,plain,(
    k2_zfmisc_1('#skF_1','#skF_6') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_9980])).

tff(c_7338,plain,(
    ! [B_6,C_7,A_5,C_1671,D_1674] :
      ( k2_zfmisc_1(A_5,B_6) = C_1671
      | k1_xboole_0 = C_7
      | k2_zfmisc_1(A_5,B_6) = k1_xboole_0
      | k3_zfmisc_1(A_5,B_6,C_7) != k2_zfmisc_1(C_1671,D_1674) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_7326])).

tff(c_9754,plain,(
    ! [C_1671,D_1674] :
      ( k2_zfmisc_1('#skF_1','#skF_6') = C_1671
      | k1_xboole_0 = '#skF_3'
      | k2_zfmisc_1('#skF_1','#skF_6') = k1_xboole_0
      | k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != k2_zfmisc_1(C_1671,D_1674) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9738,c_7338])).

tff(c_9798,plain,(
    ! [C_1671,D_1674] :
      ( k2_zfmisc_1('#skF_1','#skF_6') = C_1671
      | k2_zfmisc_1('#skF_1','#skF_6') = k1_xboole_0
      | k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != k2_zfmisc_1(C_1671,D_1674) ) ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_9754])).

tff(c_11044,plain,(
    ! [C_2633,D_2634] :
      ( k2_zfmisc_1('#skF_1','#skF_6') = C_2633
      | k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != k2_zfmisc_1(C_2633,D_2634) ) ),
    inference(negUnitSimplification,[status(thm)],[c_10740,c_9798])).

tff(c_11056,plain,(
    ! [A_5,B_6,C_7] :
      ( k2_zfmisc_1(A_5,B_6) = k2_zfmisc_1('#skF_1','#skF_6')
      | k3_zfmisc_1(A_5,B_6,C_7) != k3_zfmisc_1('#skF_1','#skF_2','#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_11044])).

tff(c_11060,plain,(
    k2_zfmisc_1('#skF_1','#skF_6') = k2_zfmisc_1('#skF_1','#skF_2') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_11056])).

tff(c_11116,plain,(
    ! [C_7] : k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),C_7) = k3_zfmisc_1('#skF_1','#skF_6',C_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_11060,c_6])).

tff(c_11128,plain,(
    ! [C_2638] : k3_zfmisc_1('#skF_1','#skF_6',C_2638) = k3_zfmisc_1('#skF_1','#skF_2',C_2638) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_11116])).

tff(c_11219,plain,(
    ! [C_2638] :
      ( k3_zfmisc_1('#skF_1','#skF_2',C_2638) != k1_xboole_0
      | k1_xboole_0 = C_2638
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_1' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11128,c_10])).

tff(c_11256,plain,(
    ! [C_2638] :
      ( k3_zfmisc_1('#skF_1','#skF_2',C_2638) != k1_xboole_0
      | k1_xboole_0 = C_2638
      | k1_xboole_0 = '#skF_6' ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_11219])).

tff(c_11308,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_11256])).

tff(c_11090,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_11060,c_10740])).

tff(c_11310,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11308,c_11090])).

tff(c_7612,plain,(
    ! [B_1707,A_1708] :
      ( k1_xboole_0 = B_1707
      | k1_xboole_0 = B_1707
      | k1_xboole_0 = A_1708
      | k2_zfmisc_1(A_1708,B_1707) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7383,c_2])).

tff(c_7702,plain,(
    ! [C_1722,A_1723,B_1724] :
      ( k1_xboole_0 = C_1722
      | k1_xboole_0 = C_1722
      | k2_zfmisc_1(A_1723,B_1724) = k1_xboole_0
      | k3_zfmisc_1(A_1723,B_1724,C_1722) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_7612])).

tff(c_7718,plain,(
    ! [C_14,A_12] :
      ( k1_xboole_0 = C_14
      | k2_zfmisc_1(A_12,k1_xboole_0) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_7702])).

tff(c_7721,plain,(
    ! [A_12] : k2_zfmisc_1(A_12,k1_xboole_0) = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_7718])).

tff(c_11341,plain,(
    ! [A_12] : k2_zfmisc_1(A_12,'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11308,c_11308,c_7721])).

tff(c_11392,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11341,c_11060])).

tff(c_11471,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_11310,c_11392])).

tff(c_11473,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_11256])).

tff(c_11113,plain,(
    ! [D_4,C_3] :
      ( D_4 = '#skF_6'
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_1'
      | k2_zfmisc_1(C_3,D_4) != k2_zfmisc_1('#skF_1','#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11060,c_2])).

tff(c_11124,plain,(
    ! [D_4,C_3] :
      ( D_4 = '#skF_6'
      | k1_xboole_0 = '#skF_6'
      | k2_zfmisc_1(C_3,D_4) != k2_zfmisc_1('#skF_1','#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_11113])).

tff(c_11504,plain,(
    ! [D_4,C_3] :
      ( D_4 = '#skF_6'
      | k2_zfmisc_1(C_3,D_4) != k2_zfmisc_1('#skF_1','#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_11473,c_11124])).

tff(c_11507,plain,(
    '#skF_6' = '#skF_2' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_11504])).

tff(c_11509,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7190,c_11507])).

tff(c_11510,plain,
    ( k2_zfmisc_1('#skF_1','#skF_6') = k1_xboole_0
    | k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_7995])).

tff(c_11512,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_11510])).

tff(c_11536,plain,(
    '#skF_7' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11512,c_26])).

tff(c_11518,plain,(
    ! [A_12] : k2_zfmisc_1(A_12,'#skF_7') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11512,c_11512,c_7721])).

tff(c_11537,plain,(
    '#skF_7' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11512,c_28])).

tff(c_11538,plain,(
    '#skF_7' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11512,c_32])).

tff(c_11535,plain,(
    '#skF_7' != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11512,c_30])).

tff(c_11511,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_7995])).

tff(c_11559,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11512,c_11511])).

tff(c_7286,plain,(
    ! [D_11,A_8,C_1667,D_1664,C_10,B_9] :
      ( D_1664 = D_11
      | k1_xboole_0 = D_11
      | k3_zfmisc_1(A_8,B_9,C_10) = k1_xboole_0
      | k4_zfmisc_1(A_8,B_9,C_10,D_11) != k2_zfmisc_1(C_1667,D_1664) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_7280])).

tff(c_11826,plain,(
    ! [B_2687,A_2686,C_2689,D_2690,C_2688,D_2685] :
      ( D_2690 = D_2685
      | D_2690 = '#skF_7'
      | k3_zfmisc_1(A_2686,B_2687,C_2689) = '#skF_7'
      | k4_zfmisc_1(A_2686,B_2687,C_2689,D_2690) != k2_zfmisc_1(C_2688,D_2685) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11512,c_11512,c_7286])).

tff(c_11844,plain,(
    ! [D_2685,C_2688] :
      ( D_2685 = '#skF_4'
      | '#skF_7' = '#skF_4'
      | k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = '#skF_7'
      | k2_zfmisc_1(C_2688,D_2685) != '#skF_7' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11559,c_11826])).

tff(c_11854,plain,(
    ! [D_2685,C_2688] :
      ( D_2685 = '#skF_4'
      | k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = '#skF_7'
      | k2_zfmisc_1(C_2688,D_2685) != '#skF_7' ) ),
    inference(negUnitSimplification,[status(thm)],[c_11536,c_11844])).

tff(c_11858,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_11854])).

tff(c_7292,plain,(
    ! [B_6,C_7,C_1667,D_1664,A_5] :
      ( D_1664 = C_7
      | k1_xboole_0 = C_7
      | k2_zfmisc_1(A_5,B_6) = k1_xboole_0
      | k3_zfmisc_1(A_5,B_6,C_7) != k2_zfmisc_1(C_1667,D_1664) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_7280])).

tff(c_11543,plain,(
    ! [B_6,C_7,C_1667,D_1664,A_5] :
      ( D_1664 = C_7
      | C_7 = '#skF_7'
      | k2_zfmisc_1(A_5,B_6) = '#skF_7'
      | k3_zfmisc_1(A_5,B_6,C_7) != k2_zfmisc_1(C_1667,D_1664) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11512,c_11512,c_7292])).

tff(c_11865,plain,(
    ! [D_1664,C_1667] :
      ( D_1664 = '#skF_3'
      | '#skF_7' = '#skF_3'
      | k2_zfmisc_1('#skF_1','#skF_2') = '#skF_7'
      | k2_zfmisc_1(C_1667,D_1664) != '#skF_7' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11858,c_11543])).

tff(c_11875,plain,(
    ! [D_1664,C_1667] :
      ( D_1664 = '#skF_3'
      | k2_zfmisc_1('#skF_1','#skF_2') = '#skF_7'
      | k2_zfmisc_1(C_1667,D_1664) != '#skF_7' ) ),
    inference(negUnitSimplification,[status(thm)],[c_11537,c_11865])).

tff(c_11978,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_11875])).

tff(c_11532,plain,(
    ! [A_12,B_13] : k3_zfmisc_1(A_12,B_13,'#skF_7') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11512,c_11512,c_12])).

tff(c_11524,plain,(
    ! [A_1675,B_1676,C_14] : k4_zfmisc_1(A_1675,B_1676,'#skF_7',C_14) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11512,c_11512,c_7374])).

tff(c_7329,plain,(
    ! [D_11,A_8,B_1673,C_10,B_9,A_1672] :
      ( k3_zfmisc_1(A_8,B_9,C_10) = A_1672
      | k1_xboole_0 = B_1673
      | k1_xboole_0 = A_1672
      | k4_zfmisc_1(A_8,B_9,C_10,D_11) != k2_zfmisc_1(A_1672,B_1673) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_7326])).

tff(c_11918,plain,(
    ! [A_2694,D_2699,A_2696,B_2695,C_2698,B_2697] :
      ( k3_zfmisc_1(A_2694,B_2697,C_2698) = A_2696
      | B_2695 = '#skF_7'
      | A_2696 = '#skF_7'
      | k4_zfmisc_1(A_2694,B_2697,C_2698,D_2699) != k2_zfmisc_1(A_2696,B_2695) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11512,c_11512,c_7329])).

tff(c_11930,plain,(
    ! [A_1675,B_1676,A_2696,B_2695] :
      ( k3_zfmisc_1(A_1675,B_1676,'#skF_7') = A_2696
      | B_2695 = '#skF_7'
      | A_2696 = '#skF_7'
      | k2_zfmisc_1(A_2696,B_2695) != '#skF_7' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11524,c_11918])).

tff(c_12098,plain,(
    ! [A_2710,B_2711] :
      ( A_2710 = '#skF_7'
      | B_2711 = '#skF_7'
      | A_2710 = '#skF_7'
      | k2_zfmisc_1(A_2710,B_2711) != '#skF_7' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11532,c_11930])).

tff(c_12101,plain,
    ( '#skF_7' = '#skF_2'
    | '#skF_7' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_11978,c_12098])).

tff(c_12117,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_11538,c_11535,c_11538,c_12101])).

tff(c_12154,plain,(
    ! [D_2718,C_2719] :
      ( D_2718 = '#skF_3'
      | k2_zfmisc_1(C_2719,D_2718) != '#skF_7' ) ),
    inference(splitRight,[status(thm)],[c_11875])).

tff(c_12157,plain,(
    '#skF_7' = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_11518,c_12154])).

tff(c_12170,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_11537,c_12157])).

tff(c_12174,plain,(
    ! [D_2720,C_2721] :
      ( D_2720 = '#skF_4'
      | k2_zfmisc_1(C_2721,D_2720) != '#skF_7' ) ),
    inference(splitRight,[status(thm)],[c_11854])).

tff(c_12177,plain,(
    '#skF_7' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_11518,c_12174])).

tff(c_12190,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_11536,c_12177])).

tff(c_12191,plain,(
    k2_zfmisc_1('#skF_1','#skF_6') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_11510])).

tff(c_12197,plain,(
    ! [C_1694] :
      ( C_1694 = '#skF_6'
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_1' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12191,c_7523])).

tff(c_12223,plain,(
    ! [C_1694] :
      ( C_1694 = '#skF_6'
      | k1_xboole_0 = '#skF_6' ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_12197])).

tff(c_12229,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_12223])).

tff(c_12256,plain,(
    '#skF_6' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12229,c_28])).

tff(c_12237,plain,(
    ! [A_12] : k2_zfmisc_1(A_12,'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12229,c_12229,c_7721])).

tff(c_12257,plain,(
    '#skF_6' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12229,c_32])).

tff(c_12255,plain,(
    '#skF_6' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12229,c_26])).

tff(c_12495,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12229,c_11511])).

tff(c_12392,plain,(
    ! [D_11,A_8,C_1667,D_1664,C_10,B_9] :
      ( D_1664 = D_11
      | D_11 = '#skF_6'
      | k3_zfmisc_1(A_8,B_9,C_10) = '#skF_6'
      | k4_zfmisc_1(A_8,B_9,C_10,D_11) != k2_zfmisc_1(C_1667,D_1664) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12229,c_12229,c_7286])).

tff(c_12500,plain,(
    ! [D_1664,C_1667] :
      ( D_1664 = '#skF_4'
      | '#skF_6' = '#skF_4'
      | k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = '#skF_6'
      | k2_zfmisc_1(C_1667,D_1664) != '#skF_6' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12495,c_12392])).

tff(c_12503,plain,(
    ! [D_1664,C_1667] :
      ( D_1664 = '#skF_4'
      | k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = '#skF_6'
      | k2_zfmisc_1(C_1667,D_1664) != '#skF_6' ) ),
    inference(negUnitSimplification,[status(thm)],[c_12255,c_12500])).

tff(c_12694,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_12503])).

tff(c_12262,plain,(
    ! [B_6,C_7,C_1667,D_1664,A_5] :
      ( D_1664 = C_7
      | C_7 = '#skF_6'
      | k2_zfmisc_1(A_5,B_6) = '#skF_6'
      | k3_zfmisc_1(A_5,B_6,C_7) != k2_zfmisc_1(C_1667,D_1664) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12229,c_12229,c_7292])).

tff(c_12701,plain,(
    ! [D_1664,C_1667] :
      ( D_1664 = '#skF_3'
      | '#skF_6' = '#skF_3'
      | k2_zfmisc_1('#skF_1','#skF_2') = '#skF_6'
      | k2_zfmisc_1(C_1667,D_1664) != '#skF_6' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12694,c_12262])).

tff(c_12711,plain,(
    ! [D_1664,C_1667] :
      ( D_1664 = '#skF_3'
      | k2_zfmisc_1('#skF_1','#skF_2') = '#skF_6'
      | k2_zfmisc_1(C_1667,D_1664) != '#skF_6' ) ),
    inference(negUnitSimplification,[status(thm)],[c_12256,c_12701])).

tff(c_12784,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_12711])).

tff(c_12943,plain,(
    ! [C_2782,B_2783,A_2784] :
      ( C_2782 = B_2783
      | B_2783 = '#skF_6'
      | A_2784 = '#skF_6'
      | k2_zfmisc_1(A_2784,B_2783) != '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12229,c_12229,c_12229,c_7523])).

tff(c_12945,plain,(
    ! [C_2782] :
      ( C_2782 = '#skF_2'
      | '#skF_6' = '#skF_2'
      | '#skF_6' = '#skF_1' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12784,c_12943])).

tff(c_12961,plain,(
    ! [C_2785] : C_2785 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_12257,c_7190,c_12945])).

tff(c_12253,plain,(
    ! [B_13,C_14] : k3_zfmisc_1('#skF_6',B_13,C_14) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12229,c_12229,c_16])).

tff(c_12788,plain,(
    ! [C_7,C_1650] : k4_zfmisc_1('#skF_1','#skF_2',C_7,C_1650) = k3_zfmisc_1('#skF_6',C_7,C_1650) ),
    inference(superposition,[status(thm),theory(equality)],[c_12784,c_7339])).

tff(c_12794,plain,(
    ! [C_7,C_1650] : k4_zfmisc_1('#skF_1','#skF_2',C_7,C_1650) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12253,c_12788])).

tff(c_12993,plain,(
    '#skF_6' = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_12961,c_12794])).

tff(c_13122,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7190,c_12993])).

tff(c_13125,plain,(
    ! [D_3083,C_3084] :
      ( D_3083 = '#skF_3'
      | k2_zfmisc_1(C_3084,D_3083) != '#skF_6' ) ),
    inference(splitRight,[status(thm)],[c_12711])).

tff(c_13128,plain,(
    '#skF_6' = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_12237,c_13125])).

tff(c_13141,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12256,c_13128])).

tff(c_13143,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_12503])).

tff(c_12244,plain,(
    ! [C_1650] : k2_zfmisc_1('#skF_6',C_1650) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12229,c_12229,c_7429])).

tff(c_7332,plain,(
    ! [D_11,A_8,C_10,B_9,C_1671,D_1674] :
      ( k3_zfmisc_1(A_8,B_9,C_10) = C_1671
      | k1_xboole_0 = D_11
      | k3_zfmisc_1(A_8,B_9,C_10) = k1_xboole_0
      | k4_zfmisc_1(A_8,B_9,C_10,D_11) != k2_zfmisc_1(C_1671,D_1674) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_7326])).

tff(c_13145,plain,(
    ! [B_3088,D_3090,C_3085,D_3086,A_3087,C_3089] :
      ( k3_zfmisc_1(A_3087,B_3088,C_3089) = C_3085
      | D_3090 = '#skF_6'
      | k3_zfmisc_1(A_3087,B_3088,C_3089) = '#skF_6'
      | k4_zfmisc_1(A_3087,B_3088,C_3089,D_3090) != k2_zfmisc_1(C_3085,D_3086) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12229,c_12229,c_7332])).

tff(c_13160,plain,(
    ! [C_3085,D_3086] :
      ( k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = C_3085
      | '#skF_6' = '#skF_4'
      | k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = '#skF_6'
      | k2_zfmisc_1(C_3085,D_3086) != '#skF_6' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12495,c_13145])).

tff(c_13177,plain,(
    ! [C_3085,D_3086] :
      ( k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = C_3085
      | k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = '#skF_6'
      | k2_zfmisc_1(C_3085,D_3086) != '#skF_6' ) ),
    inference(negUnitSimplification,[status(thm)],[c_12255,c_13160])).

tff(c_13181,plain,(
    ! [C_3091,D_3092] :
      ( k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = C_3091
      | k2_zfmisc_1(C_3091,D_3092) != '#skF_6' ) ),
    inference(negUnitSimplification,[status(thm)],[c_13143,c_13177])).

tff(c_13185,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_12244,c_13181])).

tff(c_13194,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_13143,c_13185])).

tff(c_13195,plain,(
    ! [C_1694] : C_1694 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_12223])).

tff(c_13196,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_12223])).

tff(c_13376,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_13195,c_13196])).

tff(c_13379,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_7718])).

tff(c_13377,plain,(
    ! [C_14] : k1_xboole_0 = C_14 ),
    inference(splitRight,[status(thm)],[c_7718])).

tff(c_13445,plain,(
    ! [C_3563] : C_3563 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_13379,c_13377])).

tff(c_13498,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_13445,c_32])).

tff(c_13499,plain,(
    '#skF_7' != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_7184])).

tff(c_13500,plain,(
    '#skF_6' = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_7184])).

tff(c_13520,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_7','#skF_4') = k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13500,c_5425,c_7185,c_34])).

tff(c_13640,plain,(
    ! [D_3713,B_3714,A_3715,C_3716] :
      ( D_3713 = B_3714
      | k1_xboole_0 = B_3714
      | k1_xboole_0 = A_3715
      | k2_zfmisc_1(C_3716,D_3713) != k2_zfmisc_1(A_3715,B_3714) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_14653,plain,(
    ! [C_3840,A_3842,D_3845,D_3841,B_3843,C_3844] :
      ( D_3845 = D_3841
      | k1_xboole_0 = D_3845
      | k3_zfmisc_1(A_3842,B_3843,C_3844) = k1_xboole_0
      | k4_zfmisc_1(A_3842,B_3843,C_3844,D_3845) != k2_zfmisc_1(C_3840,D_3841) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_13640])).

tff(c_14683,plain,(
    ! [D_3841,C_3840] :
      ( D_3841 = '#skF_4'
      | k1_xboole_0 = '#skF_4'
      | k3_zfmisc_1('#skF_1','#skF_2','#skF_7') = k1_xboole_0
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_zfmisc_1(C_3840,D_3841) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13520,c_14653])).

tff(c_14693,plain,(
    ! [D_3841,C_3840] :
      ( D_3841 = '#skF_4'
      | k3_zfmisc_1('#skF_1','#skF_2','#skF_7') = k1_xboole_0
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_zfmisc_1(C_3840,D_3841) ) ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_14683])).

tff(c_14694,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_7') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_14693])).

tff(c_14741,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_14694,c_10])).

tff(c_14756,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_30,c_14741])).

tff(c_13505,plain,(
    ! [A_3690,B_3691,C_3692] : k2_zfmisc_1(k2_zfmisc_1(A_3690,B_3691),C_3692) = k3_zfmisc_1(A_3690,B_3691,C_3692) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_13514,plain,(
    ! [A_5,B_6,C_7,C_3692] : k3_zfmisc_1(k2_zfmisc_1(A_5,B_6),C_7,C_3692) = k2_zfmisc_1(k3_zfmisc_1(A_5,B_6,C_7),C_3692) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_13505])).

tff(c_13680,plain,(
    ! [A_3723,B_3724,C_3725,C_3726] : k3_zfmisc_1(k2_zfmisc_1(A_3723,B_3724),C_3725,C_3726) = k4_zfmisc_1(A_3723,B_3724,C_3725,C_3726) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_13514])).

tff(c_14309,plain,(
    ! [A_3791,B_3792,C_3793,C_3794] :
      ( k4_zfmisc_1(A_3791,B_3792,C_3793,C_3794) != k1_xboole_0
      | k1_xboole_0 = C_3794
      | k1_xboole_0 = C_3793
      | k2_zfmisc_1(A_3791,B_3792) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13680,c_10])).

tff(c_14327,plain,
    ( k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_7'
    | k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_13520,c_14309])).

tff(c_14337,plain,
    ( k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_7'
    | k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_14327])).

tff(c_14338,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_14337])).

tff(c_14767,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14756,c_14338])).

tff(c_13720,plain,(
    ! [A_3723,B_3724,C_14] : k4_zfmisc_1(A_3723,B_3724,k1_xboole_0,C_14) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_13680])).

tff(c_14777,plain,(
    ! [A_3723,B_3724,C_14] : k4_zfmisc_1(A_3723,B_3724,'#skF_7',C_14) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14756,c_14756,c_13720])).

tff(c_15014,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14777,c_13520])).

tff(c_15016,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14767,c_15014])).

tff(c_15018,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_7') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_14693])).

tff(c_13623,plain,(
    ! [C_3709,A_3710,B_3711,D_3712] :
      ( C_3709 = A_3710
      | k1_xboole_0 = B_3711
      | k1_xboole_0 = A_3710
      | k2_zfmisc_1(C_3709,D_3712) != k2_zfmisc_1(A_3710,B_3711) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_15366,plain,(
    ! [A_3913,B_3914,C_3912,D_3917,D_3916,C_3915] :
      ( k3_zfmisc_1(A_3913,B_3914,C_3915) = C_3912
      | k1_xboole_0 = D_3917
      | k3_zfmisc_1(A_3913,B_3914,C_3915) = k1_xboole_0
      | k4_zfmisc_1(A_3913,B_3914,C_3915,D_3917) != k2_zfmisc_1(C_3912,D_3916) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_13623])).

tff(c_15396,plain,(
    ! [C_3912,D_3916] :
      ( k3_zfmisc_1('#skF_1','#skF_2','#skF_7') = C_3912
      | k1_xboole_0 = '#skF_4'
      | k3_zfmisc_1('#skF_1','#skF_2','#skF_7') = k1_xboole_0
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_zfmisc_1(C_3912,D_3916) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13520,c_15366])).

tff(c_15407,plain,(
    ! [C_3918,D_3919] :
      ( k3_zfmisc_1('#skF_1','#skF_2','#skF_7') = C_3918
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_zfmisc_1(C_3918,D_3919) ) ),
    inference(negUnitSimplification,[status(thm)],[c_15018,c_26,c_15396])).

tff(c_15416,plain,(
    ! [A_8,B_9,C_10,D_11] :
      ( k3_zfmisc_1(A_8,B_9,C_10) = k3_zfmisc_1('#skF_1','#skF_2','#skF_7')
      | k4_zfmisc_1(A_8,B_9,C_10,D_11) != k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_15407])).

tff(c_15445,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_7') = k3_zfmisc_1('#skF_1','#skF_2','#skF_3') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_15416])).

tff(c_15534,plain,(
    ! [D_11] : k2_zfmisc_1(k3_zfmisc_1('#skF_1','#skF_2','#skF_3'),D_11) = k4_zfmisc_1('#skF_1','#skF_2','#skF_7',D_11) ),
    inference(superposition,[status(thm),theory(equality)],[c_15445,c_8])).

tff(c_15546,plain,(
    ! [D_3927] : k4_zfmisc_1('#skF_1','#skF_2','#skF_7',D_3927) = k4_zfmisc_1('#skF_1','#skF_2','#skF_3',D_3927) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_15534])).

tff(c_13692,plain,(
    ! [A_3723,B_3724,C_3725,C_3726] :
      ( k4_zfmisc_1(A_3723,B_3724,C_3725,C_3726) != k1_xboole_0
      | k1_xboole_0 = C_3726
      | k1_xboole_0 = C_3725
      | k2_zfmisc_1(A_3723,B_3724) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13680,c_10])).

tff(c_15581,plain,(
    ! [D_3927] :
      ( k4_zfmisc_1('#skF_1','#skF_2','#skF_3',D_3927) != k1_xboole_0
      | k1_xboole_0 = D_3927
      | k1_xboole_0 = '#skF_7'
      | k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_15546,c_13692])).

tff(c_15763,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_15581])).

tff(c_13724,plain,(
    ! [A_3727,B_3728,C_3729] : k4_zfmisc_1(A_3727,B_3728,C_3729,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_13680,c_12])).

tff(c_13525,plain,(
    ! [A_3693,B_3694,C_3695,D_3696] : k2_zfmisc_1(k3_zfmisc_1(A_3693,B_3694,C_3695),D_3696) = k4_zfmisc_1(A_3693,B_3694,C_3695,D_3696) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_13540,plain,(
    ! [A_12,C_14,D_3696] : k4_zfmisc_1(A_12,k1_xboole_0,C_14,D_3696) = k2_zfmisc_1(k1_xboole_0,D_3696) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_13525])).

tff(c_13730,plain,(
    k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_13724,c_13540])).

tff(c_13773,plain,(
    ! [C_7] : k3_zfmisc_1(k1_xboole_0,k1_xboole_0,C_7) = k2_zfmisc_1(k1_xboole_0,C_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_13730,c_6])).

tff(c_13856,plain,(
    ! [C_3742] : k2_zfmisc_1(k1_xboole_0,C_3742) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_13773])).

tff(c_13864,plain,(
    ! [C_3742,B_2,A_1] :
      ( C_3742 = B_2
      | k1_xboole_0 = B_2
      | k1_xboole_0 = A_1
      | k2_zfmisc_1(A_1,B_2) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13856,c_2])).

tff(c_15816,plain,(
    ! [C_3742] :
      ( C_3742 = '#skF_2'
      | k1_xboole_0 = '#skF_2'
      | k1_xboole_0 = '#skF_1' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_15763,c_13864])).

tff(c_15849,plain,(
    ! [C_3960] : C_3960 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_30,c_15816])).

tff(c_15875,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_15849,c_15763])).

tff(c_16172,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_15875])).

tff(c_16174,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_15581])).

tff(c_16173,plain,(
    ! [D_3927] :
      ( k1_xboole_0 = '#skF_7'
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3',D_3927) != k1_xboole_0
      | k1_xboole_0 = D_3927 ) ),
    inference(splitRight,[status(thm)],[c_15581])).

tff(c_16175,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_16173])).

tff(c_16219,plain,(
    ! [A_12,B_13] : k3_zfmisc_1(A_12,B_13,'#skF_7') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16175,c_16175,c_12])).

tff(c_16364,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16219,c_15445])).

tff(c_15481,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_15445,c_15018])).

tff(c_16183,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16175,c_15481])).

tff(c_16480,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16364,c_16183])).

tff(c_16482,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_16173])).

tff(c_13652,plain,(
    ! [B_6,C_7,A_5,C_3716,D_3713] :
      ( D_3713 = C_7
      | k1_xboole_0 = C_7
      | k2_zfmisc_1(A_5,B_6) = k1_xboole_0
      | k3_zfmisc_1(A_5,B_6,C_7) != k2_zfmisc_1(C_3716,D_3713) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_13640])).

tff(c_15502,plain,(
    ! [D_3713,C_3716] :
      ( D_3713 = '#skF_7'
      | k1_xboole_0 = '#skF_7'
      | k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0
      | k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != k2_zfmisc_1(C_3716,D_3713) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_15445,c_13652])).

tff(c_16602,plain,(
    ! [D_4614,C_4615] :
      ( D_4614 = '#skF_7'
      | k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != k2_zfmisc_1(C_4615,D_4614) ) ),
    inference(negUnitSimplification,[status(thm)],[c_16174,c_16482,c_15502])).

tff(c_16614,plain,(
    ! [C_7,A_5,B_6] :
      ( C_7 = '#skF_7'
      | k3_zfmisc_1(A_5,B_6,C_7) != k3_zfmisc_1('#skF_1','#skF_2','#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_16602])).

tff(c_16618,plain,(
    '#skF_7' = '#skF_3' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_16614])).

tff(c_16620,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_13499,c_16618])).

tff(c_16621,plain,
    ( k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0
    | k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_14337])).

tff(c_16623,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_16621])).

tff(c_16646,plain,(
    '#skF_7' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16623,c_26])).

tff(c_13960,plain,(
    ! [B_3752,A_3753] :
      ( k1_xboole_0 = B_3752
      | k1_xboole_0 = B_3752
      | k1_xboole_0 = A_3753
      | k2_zfmisc_1(A_3753,B_3752) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13730,c_2])).

tff(c_14016,plain,(
    ! [C_3764,A_3765,B_3766] :
      ( k1_xboole_0 = C_3764
      | k1_xboole_0 = C_3764
      | k2_zfmisc_1(A_3765,B_3766) = k1_xboole_0
      | k3_zfmisc_1(A_3765,B_3766,C_3764) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_13960])).

tff(c_14032,plain,(
    ! [C_14,A_12] :
      ( k1_xboole_0 = C_14
      | k2_zfmisc_1(A_12,k1_xboole_0) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_14016])).

tff(c_14035,plain,(
    ! [A_12] : k2_zfmisc_1(A_12,k1_xboole_0) = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_14032])).

tff(c_16628,plain,(
    ! [A_12] : k2_zfmisc_1(A_12,'#skF_7') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16623,c_16623,c_14035])).

tff(c_16648,plain,(
    '#skF_7' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16623,c_32])).

tff(c_16645,plain,(
    '#skF_7' != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16623,c_30])).

tff(c_16622,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_14337])).

tff(c_16669,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16623,c_16622])).

tff(c_13646,plain,(
    ! [D_11,A_8,C_10,B_9,C_3716,D_3713] :
      ( D_3713 = D_11
      | k1_xboole_0 = D_11
      | k3_zfmisc_1(A_8,B_9,C_10) = k1_xboole_0
      | k4_zfmisc_1(A_8,B_9,C_10,D_11) != k2_zfmisc_1(C_3716,D_3713) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_13640])).

tff(c_16941,plain,(
    ! [C_4640,C_4644,B_4643,D_4641,A_4642,D_4645] :
      ( D_4645 = D_4641
      | D_4645 = '#skF_7'
      | k3_zfmisc_1(A_4642,B_4643,C_4644) = '#skF_7'
      | k4_zfmisc_1(A_4642,B_4643,C_4644,D_4645) != k2_zfmisc_1(C_4640,D_4641) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16623,c_16623,c_13646])).

tff(c_16956,plain,(
    ! [D_4641,C_4640] :
      ( D_4641 = '#skF_4'
      | '#skF_7' = '#skF_4'
      | k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = '#skF_7'
      | k2_zfmisc_1(C_4640,D_4641) != '#skF_7' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16669,c_16941])).

tff(c_16968,plain,(
    ! [D_4641,C_4640] :
      ( D_4641 = '#skF_4'
      | k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = '#skF_7'
      | k2_zfmisc_1(C_4640,D_4641) != '#skF_7' ) ),
    inference(negUnitSimplification,[status(thm)],[c_16646,c_16956])).

tff(c_16999,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_16968])).

tff(c_16653,plain,(
    ! [B_6,C_7,A_5,C_3716,D_3713] :
      ( D_3713 = C_7
      | C_7 = '#skF_7'
      | k2_zfmisc_1(A_5,B_6) = '#skF_7'
      | k3_zfmisc_1(A_5,B_6,C_7) != k2_zfmisc_1(C_3716,D_3713) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16623,c_16623,c_13652])).

tff(c_17006,plain,(
    ! [D_3713,C_3716] :
      ( D_3713 = '#skF_3'
      | '#skF_7' = '#skF_3'
      | k2_zfmisc_1('#skF_1','#skF_2') = '#skF_7'
      | k2_zfmisc_1(C_3716,D_3713) != '#skF_7' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16999,c_16653])).

tff(c_17015,plain,(
    ! [D_3713,C_3716] :
      ( D_3713 = '#skF_3'
      | k2_zfmisc_1('#skF_1','#skF_2') = '#skF_7'
      | k2_zfmisc_1(C_3716,D_3713) != '#skF_7' ) ),
    inference(negUnitSimplification,[status(thm)],[c_13499,c_17006])).

tff(c_17127,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_17015])).

tff(c_13632,plain,(
    ! [B_6,C_7,B_3711,A_3710,A_5] :
      ( k2_zfmisc_1(A_5,B_6) = A_3710
      | k1_xboole_0 = B_3711
      | k1_xboole_0 = A_3710
      | k3_zfmisc_1(A_5,B_6,C_7) != k2_zfmisc_1(A_3710,B_3711) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_13623])).

tff(c_16854,plain,(
    ! [B_6,C_7,B_3711,A_3710,A_5] :
      ( k2_zfmisc_1(A_5,B_6) = A_3710
      | B_3711 = '#skF_7'
      | A_3710 = '#skF_7'
      | k3_zfmisc_1(A_5,B_6,C_7) != k2_zfmisc_1(A_3710,B_3711) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16623,c_16623,c_13632])).

tff(c_17003,plain,(
    ! [A_3710,B_3711] :
      ( k2_zfmisc_1('#skF_1','#skF_2') = A_3710
      | B_3711 = '#skF_7'
      | A_3710 = '#skF_7'
      | k2_zfmisc_1(A_3710,B_3711) != '#skF_7' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16999,c_16854])).

tff(c_17300,plain,(
    ! [A_4673,B_4674] :
      ( A_4673 = '#skF_7'
      | B_4674 = '#skF_7'
      | A_4673 = '#skF_7'
      | k2_zfmisc_1(A_4673,B_4674) != '#skF_7' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17127,c_17003])).

tff(c_17303,plain,
    ( '#skF_7' = '#skF_2'
    | '#skF_7' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_17127,c_17300])).

tff(c_17319,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16648,c_16645,c_16648,c_17303])).

tff(c_17322,plain,(
    ! [D_4675,C_4676] :
      ( D_4675 = '#skF_3'
      | k2_zfmisc_1(C_4676,D_4675) != '#skF_7' ) ),
    inference(splitRight,[status(thm)],[c_17015])).

tff(c_17325,plain,(
    '#skF_7' = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_16628,c_17322])).

tff(c_17338,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_13499,c_17325])).

tff(c_17423,plain,(
    ! [D_4685,C_4686] :
      ( D_4685 = '#skF_4'
      | k2_zfmisc_1(C_4686,D_4685) != '#skF_7' ) ),
    inference(splitRight,[status(thm)],[c_16968])).

tff(c_17426,plain,(
    '#skF_7' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_16628,c_17423])).

tff(c_17439,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16646,c_17426])).

tff(c_17440,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_16621])).

tff(c_17463,plain,(
    ! [C_3742] :
      ( C_3742 = '#skF_2'
      | k1_xboole_0 = '#skF_2'
      | k1_xboole_0 = '#skF_1' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_17440,c_13864])).

tff(c_17496,plain,(
    ! [C_4687] : C_4687 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_30,c_17463])).

tff(c_17522,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_17496,c_17440])).

tff(c_17659,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_17522])).

tff(c_17662,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_14032])).

tff(c_17660,plain,(
    ! [C_14] : k1_xboole_0 = C_14 ),
    inference(splitRight,[status(thm)],[c_14032])).

tff(c_17728,plain,(
    ! [C_5157] : C_5157 = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_17662,c_17660])).

tff(c_17801,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_17728,c_30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n009.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:22:26 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.16/3.10  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.35/3.17  
% 9.35/3.17  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.35/3.17  %$ k4_zfmisc_1 > k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4
% 9.35/3.17  
% 9.35/3.17  %Foreground sorts:
% 9.35/3.17  
% 9.35/3.17  
% 9.35/3.17  %Background operators:
% 9.35/3.17  
% 9.35/3.17  
% 9.35/3.17  %Foreground operators:
% 9.35/3.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.35/3.17  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.35/3.17  tff(k4_zfmisc_1, type, k4_zfmisc_1: ($i * $i * $i * $i) > $i).
% 9.35/3.17  tff('#skF_7', type, '#skF_7': $i).
% 9.35/3.17  tff('#skF_5', type, '#skF_5': $i).
% 9.35/3.17  tff('#skF_6', type, '#skF_6': $i).
% 9.35/3.17  tff('#skF_2', type, '#skF_2': $i).
% 9.35/3.17  tff('#skF_3', type, '#skF_3': $i).
% 9.35/3.17  tff('#skF_1', type, '#skF_1': $i).
% 9.35/3.17  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 9.35/3.17  tff('#skF_8', type, '#skF_8': $i).
% 9.35/3.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.35/3.17  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.35/3.17  tff('#skF_4', type, '#skF_4': $i).
% 9.35/3.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.35/3.17  
% 9.35/3.22  tff(f_80, negated_conjecture, ~(![A, B, C, D, E, F, G, H]: ((k4_zfmisc_1(A, B, C, D) = k4_zfmisc_1(E, F, G, H)) => (((((A = k1_xboole_0) | (B = k1_xboole_0)) | (C = k1_xboole_0)) | (D = k1_xboole_0)) | ((((A = E) & (B = F)) & (C = G)) & (D = H))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_mcart_1)).
% 9.35/3.22  tff(f_37, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 9.35/3.22  tff(f_39, axiom, (![A, B, C, D]: (k4_zfmisc_1(A, B, C, D) = k2_zfmisc_1(k3_zfmisc_1(A, B, C), D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_zfmisc_1)).
% 9.35/3.22  tff(f_51, axiom, (![A, B, C]: (((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) <=> ~(k3_zfmisc_1(A, B, C) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_mcart_1)).
% 9.35/3.22  tff(f_35, axiom, (![A, B, C, D]: ((k2_zfmisc_1(A, B) = k2_zfmisc_1(C, D)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | ((A = C) & (B = D))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t134_zfmisc_1)).
% 9.35/3.22  tff(f_61, axiom, (![A, B, C, D, E, F]: ((k3_zfmisc_1(A, B, C) = k3_zfmisc_1(D, E, F)) => ((k3_zfmisc_1(A, B, C) = k1_xboole_0) | (((A = D) & (B = E)) & (C = F))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_mcart_1)).
% 9.35/3.22  tff(c_30, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_80])).
% 9.35/3.22  tff(c_32, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_80])).
% 9.35/3.22  tff(c_28, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_80])).
% 9.35/3.22  tff(c_26, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_80])).
% 9.35/3.22  tff(c_24, plain, ('#skF_8'!='#skF_4' | '#skF_7'!='#skF_3' | '#skF_6'!='#skF_2' | '#skF_5'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_80])).
% 9.35/3.22  tff(c_80, plain, ('#skF_5'!='#skF_1'), inference(splitLeft, [status(thm)], [c_24])).
% 9.35/3.22  tff(c_6, plain, (![A_5, B_6, C_7]: (k2_zfmisc_1(k2_zfmisc_1(A_5, B_6), C_7)=k3_zfmisc_1(A_5, B_6, C_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 9.35/3.22  tff(c_8, plain, (![A_8, B_9, C_10, D_11]: (k2_zfmisc_1(k3_zfmisc_1(A_8, B_9, C_10), D_11)=k4_zfmisc_1(A_8, B_9, C_10, D_11))), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.35/3.22  tff(c_85, plain, (![A_27, B_28, C_29]: (k2_zfmisc_1(k2_zfmisc_1(A_27, B_28), C_29)=k3_zfmisc_1(A_27, B_28, C_29))), inference(cnfTransformation, [status(thm)], [f_37])).
% 9.35/3.22  tff(c_94, plain, (![A_5, B_6, C_7, C_29]: (k3_zfmisc_1(k2_zfmisc_1(A_5, B_6), C_7, C_29)=k2_zfmisc_1(k3_zfmisc_1(A_5, B_6, C_7), C_29))), inference(superposition, [status(thm), theory('equality')], [c_6, c_85])).
% 9.35/3.22  tff(c_228, plain, (![A_5, B_6, C_7, C_29]: (k3_zfmisc_1(k2_zfmisc_1(A_5, B_6), C_7, C_29)=k4_zfmisc_1(A_5, B_6, C_7, C_29))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_94])).
% 9.35/3.22  tff(c_34, plain, (k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_80])).
% 9.35/3.22  tff(c_229, plain, (![A_54, B_55, C_56, C_57]: (k3_zfmisc_1(k2_zfmisc_1(A_54, B_55), C_56, C_57)=k4_zfmisc_1(A_54, B_55, C_56, C_57))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_94])).
% 9.35/3.22  tff(c_10, plain, (![A_12, B_13, C_14]: (k3_zfmisc_1(A_12, B_13, C_14)!=k1_xboole_0 | k1_xboole_0=C_14 | k1_xboole_0=B_13 | k1_xboole_0=A_12)), inference(cnfTransformation, [status(thm)], [f_51])).
% 9.35/3.22  tff(c_922, plain, (![A_133, B_134, C_135, C_136]: (k4_zfmisc_1(A_133, B_134, C_135, C_136)!=k1_xboole_0 | k1_xboole_0=C_136 | k1_xboole_0=C_135 | k2_zfmisc_1(A_133, B_134)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_229, c_10])).
% 9.35/3.22  tff(c_940, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k2_zfmisc_1('#skF_5', '#skF_6')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_34, c_922])).
% 9.35/3.22  tff(c_966, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_940])).
% 9.35/3.22  tff(c_215, plain, (![D_50, B_51, A_52, C_53]: (D_50=B_51 | k1_xboole_0=B_51 | k1_xboole_0=A_52 | k2_zfmisc_1(C_53, D_50)!=k2_zfmisc_1(A_52, B_51))), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.35/3.22  tff(c_1052, plain, (![C_152, C_155, D_151, D_156, A_153, B_154]: (D_156=D_151 | k1_xboole_0=D_156 | k3_zfmisc_1(A_153, B_154, C_155)=k1_xboole_0 | k4_zfmisc_1(A_153, B_154, C_155, D_156)!=k2_zfmisc_1(C_152, D_151))), inference(superposition, [status(thm), theory('equality')], [c_8, c_215])).
% 9.35/3.22  tff(c_1082, plain, (![D_151, C_152]: (D_151='#skF_8' | k1_xboole_0='#skF_8' | k3_zfmisc_1('#skF_5', '#skF_6', '#skF_7')=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_zfmisc_1(C_152, D_151))), inference(superposition, [status(thm), theory('equality')], [c_34, c_1052])).
% 9.35/3.22  tff(c_1110, plain, (k3_zfmisc_1('#skF_5', '#skF_6', '#skF_7')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_1082])).
% 9.35/3.22  tff(c_1162, plain, (k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_1110, c_10])).
% 9.35/3.22  tff(c_1164, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_1162])).
% 9.35/3.22  tff(c_1170, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_1164, c_966])).
% 9.35/3.22  tff(c_16, plain, (![B_13, C_14]: (k3_zfmisc_1(k1_xboole_0, B_13, C_14)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 9.35/3.22  tff(c_12, plain, (![A_12, B_13]: (k3_zfmisc_1(A_12, B_13, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 9.35/3.22  tff(c_299, plain, (![A_64, B_65, C_66]: (k4_zfmisc_1(A_64, B_65, C_66, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_229, c_12])).
% 9.35/3.22  tff(c_116, plain, (![A_33, B_34, C_35, D_36]: (k2_zfmisc_1(k3_zfmisc_1(A_33, B_34, C_35), D_36)=k4_zfmisc_1(A_33, B_34, C_35, D_36))), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.35/3.22  tff(c_134, plain, (![B_13, C_14, D_36]: (k4_zfmisc_1(k1_xboole_0, B_13, C_14, D_36)=k2_zfmisc_1(k1_xboole_0, D_36))), inference(superposition, [status(thm), theory('equality')], [c_16, c_116])).
% 9.35/3.22  tff(c_305, plain, (k2_zfmisc_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_299, c_134])).
% 9.35/3.22  tff(c_348, plain, (![C_7]: (k3_zfmisc_1(k1_xboole_0, k1_xboole_0, C_7)=k2_zfmisc_1(k1_xboole_0, C_7))), inference(superposition, [status(thm), theory('equality')], [c_305, c_6])).
% 9.35/3.22  tff(c_354, plain, (![C_7]: (k2_zfmisc_1(k1_xboole_0, C_7)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_348])).
% 9.35/3.22  tff(c_1149, plain, (![D_11]: (k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', D_11)=k2_zfmisc_1(k1_xboole_0, D_11))), inference(superposition, [status(thm), theory('equality')], [c_1110, c_8])).
% 9.35/3.22  tff(c_1161, plain, (![D_11]: (k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', D_11)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_354, c_1149])).
% 9.35/3.22  tff(c_1505, plain, (![D_11]: (k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', D_11)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1164, c_1161])).
% 9.35/3.22  tff(c_1506, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_1505, c_34])).
% 9.35/3.22  tff(c_1508, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1170, c_1506])).
% 9.35/3.22  tff(c_1509, plain, (k1_xboole_0='#skF_6' | k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_1162])).
% 9.35/3.22  tff(c_1547, plain, (k1_xboole_0='#skF_7'), inference(splitLeft, [status(thm)], [c_1509])).
% 9.35/3.22  tff(c_14, plain, (![A_12, C_14]: (k3_zfmisc_1(A_12, k1_xboole_0, C_14)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 9.35/3.22  tff(c_263, plain, (![A_54, B_55, C_14]: (k4_zfmisc_1(A_54, B_55, k1_xboole_0, C_14)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_14, c_229])).
% 9.35/3.22  tff(c_1567, plain, (![A_54, B_55, C_14]: (k4_zfmisc_1(A_54, B_55, '#skF_7', C_14)='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_1547, c_1547, c_263])).
% 9.35/3.22  tff(c_1837, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_1567, c_34])).
% 9.35/3.22  tff(c_1555, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_1547, c_966])).
% 9.35/3.22  tff(c_1883, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1837, c_1555])).
% 9.35/3.22  tff(c_1884, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_1509])).
% 9.35/3.22  tff(c_1894, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_1884, c_966])).
% 9.35/3.22  tff(c_2253, plain, (![D_11]: (k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', D_11)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1884, c_1161])).
% 9.35/3.22  tff(c_2254, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_2253, c_34])).
% 9.35/3.22  tff(c_2256, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1894, c_2254])).
% 9.35/3.22  tff(c_2257, plain, (![D_151, C_152]: (k1_xboole_0='#skF_8' | D_151='#skF_8' | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_zfmisc_1(C_152, D_151))), inference(splitRight, [status(thm)], [c_1082])).
% 9.35/3.22  tff(c_2259, plain, (k1_xboole_0='#skF_8'), inference(splitLeft, [status(thm)], [c_2257])).
% 9.35/3.22  tff(c_242, plain, (![A_54, B_55, C_56]: (k4_zfmisc_1(A_54, B_55, C_56, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_229, c_12])).
% 9.35/3.22  tff(c_2302, plain, (![A_54, B_55, C_56]: (k4_zfmisc_1(A_54, B_55, C_56, '#skF_8')='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_2259, c_2259, c_242])).
% 9.35/3.22  tff(c_2555, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_2302, c_34])).
% 9.35/3.22  tff(c_2286, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_2259, c_966])).
% 9.35/3.22  tff(c_2648, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2555, c_2286])).
% 9.35/3.22  tff(c_2651, plain, (![D_295, C_296]: (D_295='#skF_8' | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_zfmisc_1(C_296, D_295))), inference(splitRight, [status(thm)], [c_2257])).
% 9.35/3.22  tff(c_2660, plain, (![D_11, A_8, B_9, C_10]: (D_11='#skF_8' | k4_zfmisc_1(A_8, B_9, C_10, D_11)!=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_8, c_2651])).
% 9.35/3.22  tff(c_2705, plain, ('#skF_8'='#skF_4'), inference(reflexivity, [status(thm), theory('equality')], [c_2660])).
% 9.35/3.22  tff(c_2732, plain, (k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_4')=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2705, c_34])).
% 9.35/3.22  tff(c_270, plain, (![E_62, D_59, F_61, A_63, C_58, B_60]: (E_62=B_60 | k3_zfmisc_1(A_63, B_60, C_58)=k1_xboole_0 | k3_zfmisc_1(D_59, E_62, F_61)!=k3_zfmisc_1(A_63, B_60, C_58))), inference(cnfTransformation, [status(thm)], [f_61])).
% 9.35/3.22  tff(c_276, plain, (![B_6, C_29, C_7, E_62, D_59, A_5, F_61]: (E_62=C_7 | k3_zfmisc_1(k2_zfmisc_1(A_5, B_6), C_7, C_29)=k1_xboole_0 | k4_zfmisc_1(A_5, B_6, C_7, C_29)!=k3_zfmisc_1(D_59, E_62, F_61))), inference(superposition, [status(thm), theory('equality')], [c_228, c_270])).
% 9.35/3.22  tff(c_3129, plain, (![A_364, D_366, C_361, E_365, F_360, C_363, B_362]: (E_365=C_363 | k4_zfmisc_1(A_364, B_362, C_363, C_361)=k1_xboole_0 | k4_zfmisc_1(A_364, B_362, C_363, C_361)!=k3_zfmisc_1(D_366, E_365, F_360))), inference(demodulation, [status(thm), theory('equality')], [c_228, c_276])).
% 9.35/3.22  tff(c_3135, plain, (![E_365, D_366, F_360]: (E_365='#skF_7' | k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_4')=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k3_zfmisc_1(D_366, E_365, F_360))), inference(superposition, [status(thm), theory('equality')], [c_2732, c_3129])).
% 9.35/3.22  tff(c_3167, plain, (![E_365, D_366, F_360]: (E_365='#skF_7' | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k3_zfmisc_1(D_366, E_365, F_360))), inference(demodulation, [status(thm), theory('equality')], [c_2732, c_3135])).
% 9.35/3.22  tff(c_3215, plain, (![E_373, D_374, F_375]: (E_373='#skF_7' | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k3_zfmisc_1(D_374, E_373, F_375))), inference(negUnitSimplification, [status(thm)], [c_966, c_3167])).
% 9.35/3.22  tff(c_3221, plain, (![C_7, A_5, B_6, C_29]: (C_7='#skF_7' | k4_zfmisc_1(A_5, B_6, C_7, C_29)!=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_228, c_3215])).
% 9.35/3.22  tff(c_3233, plain, ('#skF_7'='#skF_3'), inference(reflexivity, [status(thm), theory('equality')], [c_3221])).
% 9.35/3.22  tff(c_2258, plain, (k3_zfmisc_1('#skF_5', '#skF_6', '#skF_7')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_1082])).
% 9.35/3.22  tff(c_169, plain, (![C_43, A_44, B_45, D_46]: (C_43=A_44 | k1_xboole_0=B_45 | k1_xboole_0=A_44 | k2_zfmisc_1(C_43, D_46)!=k2_zfmisc_1(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.35/3.22  tff(c_3174, plain, (![C_367, D_372, D_368, C_371, A_369, B_370]: (k3_zfmisc_1(A_369, B_370, C_371)=C_367 | k1_xboole_0=D_372 | k3_zfmisc_1(A_369, B_370, C_371)=k1_xboole_0 | k4_zfmisc_1(A_369, B_370, C_371, D_372)!=k2_zfmisc_1(C_367, D_368))), inference(superposition, [status(thm), theory('equality')], [c_8, c_169])).
% 9.35/3.22  tff(c_3180, plain, (![C_367, D_368]: (k3_zfmisc_1('#skF_5', '#skF_6', '#skF_7')=C_367 | k1_xboole_0='#skF_4' | k3_zfmisc_1('#skF_5', '#skF_6', '#skF_7')=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_zfmisc_1(C_367, D_368))), inference(superposition, [status(thm), theory('equality')], [c_2732, c_3174])).
% 9.35/3.22  tff(c_3209, plain, (![C_367, D_368]: (k3_zfmisc_1('#skF_5', '#skF_6', '#skF_7')=C_367 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_zfmisc_1(C_367, D_368))), inference(negUnitSimplification, [status(thm)], [c_2258, c_26, c_3180])).
% 9.35/3.22  tff(c_3267, plain, (![C_380, D_381]: (k3_zfmisc_1('#skF_5', '#skF_6', '#skF_3')=C_380 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_zfmisc_1(C_380, D_381))), inference(demodulation, [status(thm), theory('equality')], [c_3233, c_3209])).
% 9.35/3.22  tff(c_3276, plain, (![A_8, B_9, C_10, D_11]: (k3_zfmisc_1(A_8, B_9, C_10)=k3_zfmisc_1('#skF_5', '#skF_6', '#skF_3') | k4_zfmisc_1(A_8, B_9, C_10, D_11)!=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_8, c_3267])).
% 9.35/3.22  tff(c_3559, plain, (k3_zfmisc_1('#skF_5', '#skF_6', '#skF_3')=k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')), inference(reflexivity, [status(thm), theory('equality')], [c_3276])).
% 9.35/3.22  tff(c_3261, plain, (k3_zfmisc_1('#skF_5', '#skF_6', '#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_3233, c_2258])).
% 9.35/3.22  tff(c_3594, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_3559, c_3261])).
% 9.35/3.22  tff(c_3645, plain, (![D_11]: (k2_zfmisc_1(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'), D_11)=k4_zfmisc_1('#skF_5', '#skF_6', '#skF_3', D_11))), inference(superposition, [status(thm), theory('equality')], [c_3559, c_8])).
% 9.35/3.22  tff(c_3665, plain, (![D_421]: (k4_zfmisc_1('#skF_5', '#skF_6', '#skF_3', D_421)=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', D_421))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_3645])).
% 9.35/3.22  tff(c_238, plain, (![A_54, B_55, C_56, C_57]: (k4_zfmisc_1(A_54, B_55, C_56, C_57)!=k1_xboole_0 | k1_xboole_0=C_57 | k1_xboole_0=C_56 | k2_zfmisc_1(A_54, B_55)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_229, c_10])).
% 9.35/3.22  tff(c_3709, plain, (![D_421]: (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', D_421)!=k1_xboole_0 | k1_xboole_0=D_421 | k1_xboole_0='#skF_3' | k2_zfmisc_1('#skF_5', '#skF_6')=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_3665, c_238])).
% 9.35/3.22  tff(c_3736, plain, (![D_421]: (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', D_421)!=k1_xboole_0 | k1_xboole_0=D_421 | k2_zfmisc_1('#skF_5', '#skF_6')=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_28, c_3709])).
% 9.35/3.22  tff(c_3746, plain, (k2_zfmisc_1('#skF_5', '#skF_6')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_3736])).
% 9.35/3.22  tff(c_3772, plain, (![C_7]: (k3_zfmisc_1('#skF_5', '#skF_6', C_7)=k2_zfmisc_1(k1_xboole_0, C_7))), inference(superposition, [status(thm), theory('equality')], [c_3746, c_6])).
% 9.35/3.22  tff(c_3779, plain, (![C_7]: (k3_zfmisc_1('#skF_5', '#skF_6', C_7)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_354, c_3772])).
% 9.35/3.22  tff(c_3782, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_3779, c_3559])).
% 9.35/3.22  tff(c_3784, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3594, c_3782])).
% 9.35/3.22  tff(c_3786, plain, (k2_zfmisc_1('#skF_5', '#skF_6')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_3736])).
% 9.35/3.22  tff(c_181, plain, (![B_6, C_7, C_43, A_5, D_46]: (k2_zfmisc_1(A_5, B_6)=C_43 | k1_xboole_0=C_7 | k2_zfmisc_1(A_5, B_6)=k1_xboole_0 | k3_zfmisc_1(A_5, B_6, C_7)!=k2_zfmisc_1(C_43, D_46))), inference(superposition, [status(thm), theory('equality')], [c_6, c_169])).
% 9.35/3.22  tff(c_3610, plain, (![C_43, D_46]: (k2_zfmisc_1('#skF_5', '#skF_6')=C_43 | k1_xboole_0='#skF_3' | k2_zfmisc_1('#skF_5', '#skF_6')=k1_xboole_0 | k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')!=k2_zfmisc_1(C_43, D_46))), inference(superposition, [status(thm), theory('equality')], [c_3559, c_181])).
% 9.35/3.22  tff(c_3654, plain, (![C_43, D_46]: (k2_zfmisc_1('#skF_5', '#skF_6')=C_43 | k2_zfmisc_1('#skF_5', '#skF_6')=k1_xboole_0 | k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')!=k2_zfmisc_1(C_43, D_46))), inference(negUnitSimplification, [status(thm)], [c_28, c_3610])).
% 9.35/3.22  tff(c_4055, plain, (![C_465, D_466]: (k2_zfmisc_1('#skF_5', '#skF_6')=C_465 | k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')!=k2_zfmisc_1(C_465, D_466))), inference(negUnitSimplification, [status(thm)], [c_3786, c_3654])).
% 9.35/3.22  tff(c_4067, plain, (![A_5, B_6, C_7]: (k2_zfmisc_1(A_5, B_6)=k2_zfmisc_1('#skF_5', '#skF_6') | k3_zfmisc_1(A_5, B_6, C_7)!=k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_6, c_4055])).
% 9.35/3.22  tff(c_4071, plain, (k2_zfmisc_1('#skF_5', '#skF_6')=k2_zfmisc_1('#skF_1', '#skF_2')), inference(reflexivity, [status(thm), theory('equality')], [c_4067])).
% 9.35/3.22  tff(c_4127, plain, (![C_7]: (k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), C_7)=k3_zfmisc_1('#skF_5', '#skF_6', C_7))), inference(superposition, [status(thm), theory('equality')], [c_4071, c_6])).
% 9.35/3.22  tff(c_4135, plain, (![C_470]: (k3_zfmisc_1('#skF_5', '#skF_6', C_470)=k3_zfmisc_1('#skF_1', '#skF_2', C_470))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_4127])).
% 9.35/3.22  tff(c_4223, plain, (![C_470]: (k3_zfmisc_1('#skF_1', '#skF_2', C_470)!=k1_xboole_0 | k1_xboole_0=C_470 | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_4135, c_10])).
% 9.35/3.22  tff(c_4391, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_4223])).
% 9.35/3.22  tff(c_4101, plain, (k2_zfmisc_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_4071, c_3786])).
% 9.35/3.22  tff(c_4394, plain, (k2_zfmisc_1('#skF_1', '#skF_2')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_4391, c_4101])).
% 9.35/3.22  tff(c_4431, plain, (![C_7]: (k2_zfmisc_1('#skF_5', C_7)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_4391, c_4391, c_354])).
% 9.35/3.22  tff(c_4471, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_4431, c_4071])).
% 9.35/3.22  tff(c_4563, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4394, c_4471])).
% 9.35/3.22  tff(c_4565, plain, (k1_xboole_0!='#skF_5'), inference(splitRight, [status(thm)], [c_4223])).
% 9.35/3.22  tff(c_4564, plain, (![C_470]: (k1_xboole_0='#skF_6' | k3_zfmisc_1('#skF_1', '#skF_2', C_470)!=k1_xboole_0 | k1_xboole_0=C_470)), inference(splitRight, [status(thm)], [c_4223])).
% 9.35/3.22  tff(c_4566, plain, (k1_xboole_0='#skF_6'), inference(splitLeft, [status(thm)], [c_4564])).
% 9.35/3.22  tff(c_4570, plain, (k2_zfmisc_1('#skF_1', '#skF_2')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_4566, c_4101])).
% 9.35/3.22  tff(c_2, plain, (![D_4, B_2, A_1, C_3]: (D_4=B_2 | k1_xboole_0=B_2 | k1_xboole_0=A_1 | k2_zfmisc_1(C_3, D_4)!=k2_zfmisc_1(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.35/3.22  tff(c_547, plain, (![B_91, A_92]: (k1_xboole_0=B_91 | k1_xboole_0=B_91 | k1_xboole_0=A_92 | k2_zfmisc_1(A_92, B_91)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_305, c_2])).
% 9.35/3.22  tff(c_591, plain, (![C_101, A_102, B_103]: (k1_xboole_0=C_101 | k1_xboole_0=C_101 | k2_zfmisc_1(A_102, B_103)=k1_xboole_0 | k3_zfmisc_1(A_102, B_103, C_101)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_6, c_547])).
% 9.35/3.22  tff(c_607, plain, (![C_14, A_12]: (k1_xboole_0=C_14 | k2_zfmisc_1(A_12, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_14, c_591])).
% 9.35/3.22  tff(c_695, plain, (![A_12]: (k2_zfmisc_1(A_12, k1_xboole_0)=k1_xboole_0)), inference(splitLeft, [status(thm)], [c_607])).
% 9.35/3.22  tff(c_4600, plain, (![A_12]: (k2_zfmisc_1(A_12, '#skF_6')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_4566, c_4566, c_695])).
% 9.35/3.22  tff(c_4676, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_4600, c_4071])).
% 9.35/3.22  tff(c_4678, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4570, c_4676])).
% 9.35/3.22  tff(c_4680, plain, (k1_xboole_0!='#skF_6'), inference(splitRight, [status(thm)], [c_4564])).
% 9.35/3.22  tff(c_4118, plain, (![D_4, C_3]: (D_4='#skF_6' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k2_zfmisc_1(C_3, D_4)!=k2_zfmisc_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_4071, c_2])).
% 9.35/3.22  tff(c_4791, plain, (![D_4, C_3]: (D_4='#skF_6' | k2_zfmisc_1(C_3, D_4)!=k2_zfmisc_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_4565, c_4680, c_4118])).
% 9.35/3.22  tff(c_4794, plain, ('#skF_6'='#skF_2'), inference(reflexivity, [status(thm), theory('equality')], [c_4791])).
% 9.35/3.22  tff(c_4818, plain, (k2_zfmisc_1('#skF_5', '#skF_2')=k2_zfmisc_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4794, c_4071])).
% 9.35/3.22  tff(c_4, plain, (![C_3, A_1, B_2, D_4]: (C_3=A_1 | k1_xboole_0=B_2 | k1_xboole_0=A_1 | k2_zfmisc_1(C_3, D_4)!=k2_zfmisc_1(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.35/3.22  tff(c_4845, plain, (![C_3, D_4]: (C_3='#skF_5' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_5' | k2_zfmisc_1(C_3, D_4)!=k2_zfmisc_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_4818, c_4])).
% 9.35/3.22  tff(c_4856, plain, (![C_3, D_4]: (C_3='#skF_5' | k2_zfmisc_1(C_3, D_4)!=k2_zfmisc_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_4565, c_30, c_4845])).
% 9.35/3.22  tff(c_5062, plain, ('#skF_5'='#skF_1'), inference(reflexivity, [status(thm), theory('equality')], [c_4856])).
% 9.35/3.22  tff(c_5064, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_5062])).
% 9.35/3.22  tff(c_5066, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_940])).
% 9.35/3.22  tff(c_5072, plain, (k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_5066, c_238])).
% 9.35/3.22  tff(c_5080, plain, (k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_28, c_26, c_5072])).
% 9.35/3.22  tff(c_398, plain, (![C_73]: (k2_zfmisc_1(k1_xboole_0, C_73)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_348])).
% 9.35/3.22  tff(c_406, plain, (![C_73, B_2, A_1]: (C_73=B_2 | k1_xboole_0=B_2 | k1_xboole_0=A_1 | k2_zfmisc_1(A_1, B_2)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_398, c_2])).
% 9.35/3.22  tff(c_5089, plain, (![C_73]: (C_73='#skF_2' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_5080, c_406])).
% 9.35/3.22  tff(c_5122, plain, (![C_527]: (C_527='#skF_2')), inference(negUnitSimplification, [status(thm)], [c_32, c_30, c_5089])).
% 9.35/3.22  tff(c_5148, plain, (k1_xboole_0='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_5122, c_5080])).
% 9.35/3.22  tff(c_5284, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_5148])).
% 9.35/3.22  tff(c_5287, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_607])).
% 9.35/3.22  tff(c_5285, plain, (![C_14]: (k1_xboole_0=C_14)), inference(splitRight, [status(thm)], [c_607])).
% 9.35/3.22  tff(c_5357, plain, (![C_979]: (C_979='#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_5287, c_5285])).
% 9.35/3.22  tff(c_5423, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_5357, c_30])).
% 9.35/3.22  tff(c_5424, plain, ('#skF_6'!='#skF_2' | '#skF_7'!='#skF_3' | '#skF_8'!='#skF_4'), inference(splitRight, [status(thm)], [c_24])).
% 9.35/3.22  tff(c_5430, plain, ('#skF_8'!='#skF_4'), inference(splitLeft, [status(thm)], [c_5424])).
% 9.35/3.22  tff(c_5431, plain, (![A_1106, B_1107, C_1108]: (k2_zfmisc_1(k2_zfmisc_1(A_1106, B_1107), C_1108)=k3_zfmisc_1(A_1106, B_1107, C_1108))), inference(cnfTransformation, [status(thm)], [f_37])).
% 9.35/3.22  tff(c_5440, plain, (![A_5, B_6, C_7, C_1108]: (k3_zfmisc_1(k2_zfmisc_1(A_5, B_6), C_7, C_1108)=k2_zfmisc_1(k3_zfmisc_1(A_5, B_6, C_7), C_1108))), inference(superposition, [status(thm), theory('equality')], [c_6, c_5431])).
% 9.35/3.22  tff(c_5579, plain, (![A_5, B_6, C_7, C_1108]: (k3_zfmisc_1(k2_zfmisc_1(A_5, B_6), C_7, C_1108)=k4_zfmisc_1(A_5, B_6, C_7, C_1108))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_5440])).
% 9.35/3.22  tff(c_5425, plain, ('#skF_5'='#skF_1'), inference(splitRight, [status(thm)], [c_24])).
% 9.35/3.22  tff(c_5446, plain, (k4_zfmisc_1('#skF_1', '#skF_6', '#skF_7', '#skF_8')=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5425, c_34])).
% 9.35/3.22  tff(c_5580, plain, (![A_1133, B_1134, C_1135, C_1136]: (k3_zfmisc_1(k2_zfmisc_1(A_1133, B_1134), C_1135, C_1136)=k4_zfmisc_1(A_1133, B_1134, C_1135, C_1136))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_5440])).
% 9.35/3.22  tff(c_6274, plain, (![A_1212, B_1213, C_1214, C_1215]: (k4_zfmisc_1(A_1212, B_1213, C_1214, C_1215)!=k1_xboole_0 | k1_xboole_0=C_1215 | k1_xboole_0=C_1214 | k2_zfmisc_1(A_1212, B_1213)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_5580, c_10])).
% 9.35/3.22  tff(c_6292, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k2_zfmisc_1('#skF_1', '#skF_6')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_5446, c_6274])).
% 9.35/3.22  tff(c_6317, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_6292])).
% 9.35/3.22  tff(c_5652, plain, (![B_1142, D_1141, C_1140, F_1143, A_1145, E_1144]: (F_1143=C_1140 | k3_zfmisc_1(A_1145, B_1142, C_1140)=k1_xboole_0 | k3_zfmisc_1(D_1141, E_1144, F_1143)!=k3_zfmisc_1(A_1145, B_1142, C_1140))), inference(cnfTransformation, [status(thm)], [f_61])).
% 9.35/3.22  tff(c_5658, plain, (![B_6, C_7, C_1108, A_5, D_1141, F_1143, E_1144]: (F_1143=C_1108 | k3_zfmisc_1(k2_zfmisc_1(A_5, B_6), C_7, C_1108)=k1_xboole_0 | k4_zfmisc_1(A_5, B_6, C_7, C_1108)!=k3_zfmisc_1(D_1141, E_1144, F_1143))), inference(superposition, [status(thm), theory('equality')], [c_5579, c_5652])).
% 9.35/3.22  tff(c_6858, plain, (![C_1301, E_1299, F_1303, D_1304, B_1300, C_1298, A_1302]: (F_1303=C_1298 | k4_zfmisc_1(A_1302, B_1300, C_1301, C_1298)=k1_xboole_0 | k4_zfmisc_1(A_1302, B_1300, C_1301, C_1298)!=k3_zfmisc_1(D_1304, E_1299, F_1303))), inference(demodulation, [status(thm), theory('equality')], [c_5579, c_5658])).
% 9.35/3.22  tff(c_6885, plain, (![F_1303, D_1304, E_1299]: (F_1303='#skF_8' | k4_zfmisc_1('#skF_1', '#skF_6', '#skF_7', '#skF_8')=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k3_zfmisc_1(D_1304, E_1299, F_1303))), inference(superposition, [status(thm), theory('equality')], [c_5446, c_6858])).
% 9.35/3.22  tff(c_6901, plain, (![F_1303, D_1304, E_1299]: (F_1303='#skF_8' | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k3_zfmisc_1(D_1304, E_1299, F_1303))), inference(demodulation, [status(thm), theory('equality')], [c_5446, c_6885])).
% 9.35/3.22  tff(c_6903, plain, (![F_1305, D_1306, E_1307]: (F_1305='#skF_8' | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k3_zfmisc_1(D_1306, E_1307, F_1305))), inference(negUnitSimplification, [status(thm)], [c_6317, c_6901])).
% 9.35/3.22  tff(c_6909, plain, (![C_1108, A_5, B_6, C_7]: (C_1108='#skF_8' | k4_zfmisc_1(A_5, B_6, C_7, C_1108)!=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_5579, c_6903])).
% 9.35/3.22  tff(c_6961, plain, ('#skF_8'='#skF_4'), inference(reflexivity, [status(thm), theory('equality')], [c_6909])).
% 9.35/3.22  tff(c_6963, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5430, c_6961])).
% 9.35/3.22  tff(c_6965, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_6292])).
% 9.35/3.22  tff(c_5586, plain, (![A_1133, B_1134, C_1135, C_1136]: (k4_zfmisc_1(A_1133, B_1134, C_1135, C_1136)!=k1_xboole_0 | k1_xboole_0=C_1136 | k1_xboole_0=C_1135 | k2_zfmisc_1(A_1133, B_1134)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_5580, c_10])).
% 9.35/3.22  tff(c_6971, plain, (k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_6965, c_5586])).
% 9.35/3.22  tff(c_6979, plain, (k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_28, c_26, c_6971])).
% 9.35/3.22  tff(c_5617, plain, (![A_1137, B_1138, C_1139]: (k4_zfmisc_1(A_1137, B_1138, C_1139, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_5580, c_12])).
% 9.35/3.22  tff(c_5451, plain, (![A_1109, B_1110, C_1111, D_1112]: (k2_zfmisc_1(k3_zfmisc_1(A_1109, B_1110, C_1111), D_1112)=k4_zfmisc_1(A_1109, B_1110, C_1111, D_1112))), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.35/3.22  tff(c_5469, plain, (![B_13, C_14, D_1112]: (k4_zfmisc_1(k1_xboole_0, B_13, C_14, D_1112)=k2_zfmisc_1(k1_xboole_0, D_1112))), inference(superposition, [status(thm), theory('equality')], [c_16, c_5451])).
% 9.35/3.22  tff(c_5623, plain, (k2_zfmisc_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_5617, c_5469])).
% 9.35/3.22  tff(c_5699, plain, (![C_7]: (k3_zfmisc_1(k1_xboole_0, k1_xboole_0, C_7)=k2_zfmisc_1(k1_xboole_0, C_7))), inference(superposition, [status(thm), theory('equality')], [c_5623, c_6])).
% 9.35/3.22  tff(c_5749, plain, (![C_1152]: (k2_zfmisc_1(k1_xboole_0, C_1152)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_5699])).
% 9.35/3.22  tff(c_5763, plain, (![C_1152, B_2, A_1]: (C_1152=B_2 | k1_xboole_0=B_2 | k1_xboole_0=A_1 | k2_zfmisc_1(A_1, B_2)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_5749, c_2])).
% 9.35/3.22  tff(c_6988, plain, (![C_1152]: (C_1152='#skF_2' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_6979, c_5763])).
% 9.35/3.22  tff(c_7021, plain, (![C_1314]: (C_1314='#skF_2')), inference(negUnitSimplification, [status(thm)], [c_32, c_30, c_6988])).
% 9.35/3.22  tff(c_7047, plain, (k1_xboole_0='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_7021, c_6979])).
% 9.35/3.22  tff(c_7183, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_7047])).
% 9.35/3.22  tff(c_7184, plain, ('#skF_7'!='#skF_3' | '#skF_6'!='#skF_2'), inference(splitRight, [status(thm)], [c_5424])).
% 9.35/3.22  tff(c_7190, plain, ('#skF_6'!='#skF_2'), inference(splitLeft, [status(thm)], [c_7184])).
% 9.35/3.22  tff(c_7191, plain, (![A_1648, B_1649, C_1650]: (k2_zfmisc_1(k2_zfmisc_1(A_1648, B_1649), C_1650)=k3_zfmisc_1(A_1648, B_1649, C_1650))), inference(cnfTransformation, [status(thm)], [f_37])).
% 9.35/3.22  tff(c_7200, plain, (![A_5, B_6, C_7, C_1650]: (k3_zfmisc_1(k2_zfmisc_1(A_5, B_6), C_7, C_1650)=k2_zfmisc_1(k3_zfmisc_1(A_5, B_6, C_7), C_1650))), inference(superposition, [status(thm), theory('equality')], [c_6, c_7191])).
% 9.35/3.22  tff(c_7339, plain, (![A_5, B_6, C_7, C_1650]: (k3_zfmisc_1(k2_zfmisc_1(A_5, B_6), C_7, C_1650)=k4_zfmisc_1(A_5, B_6, C_7, C_1650))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_7200])).
% 9.35/3.22  tff(c_7185, plain, ('#skF_8'='#skF_4'), inference(splitRight, [status(thm)], [c_5424])).
% 9.35/3.22  tff(c_7206, plain, (k4_zfmisc_1('#skF_1', '#skF_6', '#skF_7', '#skF_4')=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_7185, c_5425, c_34])).
% 9.35/3.22  tff(c_7340, plain, (![A_1675, B_1676, C_1677, C_1678]: (k3_zfmisc_1(k2_zfmisc_1(A_1675, B_1676), C_1677, C_1678)=k4_zfmisc_1(A_1675, B_1676, C_1677, C_1678))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_7200])).
% 9.35/3.22  tff(c_7971, plain, (![A_1749, B_1750, C_1751, C_1752]: (k4_zfmisc_1(A_1749, B_1750, C_1751, C_1752)!=k1_xboole_0 | k1_xboole_0=C_1752 | k1_xboole_0=C_1751 | k2_zfmisc_1(A_1749, B_1750)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_7340, c_10])).
% 9.35/3.22  tff(c_7986, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_7' | k2_zfmisc_1('#skF_1', '#skF_6')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_7206, c_7971])).
% 9.35/3.22  tff(c_7995, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_7' | k2_zfmisc_1('#skF_1', '#skF_6')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_26, c_7986])).
% 9.35/3.22  tff(c_7996, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_7995])).
% 9.35/3.22  tff(c_7558, plain, (![E_1702, C_1698, A_1703, B_1700, F_1701, D_1699]: (E_1702=B_1700 | k3_zfmisc_1(A_1703, B_1700, C_1698)=k1_xboole_0 | k3_zfmisc_1(D_1699, E_1702, F_1701)!=k3_zfmisc_1(A_1703, B_1700, C_1698))), inference(cnfTransformation, [status(thm)], [f_61])).
% 9.35/3.22  tff(c_7564, plain, (![B_6, C_7, E_1702, F_1701, A_5, D_1699, C_1650]: (E_1702=C_7 | k3_zfmisc_1(k2_zfmisc_1(A_5, B_6), C_7, C_1650)=k1_xboole_0 | k4_zfmisc_1(A_5, B_6, C_7, C_1650)!=k3_zfmisc_1(D_1699, E_1702, F_1701))), inference(superposition, [status(thm), theory('equality')], [c_7339, c_7558])).
% 9.35/3.22  tff(c_9604, plain, (![C_1926, B_1925, F_1929, A_1928, C_1924, D_1927, E_1930]: (E_1930=C_1926 | k4_zfmisc_1(A_1928, B_1925, C_1926, C_1924)=k1_xboole_0 | k4_zfmisc_1(A_1928, B_1925, C_1926, C_1924)!=k3_zfmisc_1(D_1927, E_1930, F_1929))), inference(demodulation, [status(thm), theory('equality')], [c_7339, c_7564])).
% 9.35/3.22  tff(c_9631, plain, (![E_1930, D_1927, F_1929]: (E_1930='#skF_7' | k4_zfmisc_1('#skF_1', '#skF_6', '#skF_7', '#skF_4')=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k3_zfmisc_1(D_1927, E_1930, F_1929))), inference(superposition, [status(thm), theory('equality')], [c_7206, c_9604])).
% 9.35/3.22  tff(c_9647, plain, (![E_1930, D_1927, F_1929]: (E_1930='#skF_7' | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k3_zfmisc_1(D_1927, E_1930, F_1929))), inference(demodulation, [status(thm), theory('equality')], [c_7206, c_9631])).
% 9.35/3.22  tff(c_9649, plain, (![E_1931, D_1932, F_1933]: (E_1931='#skF_7' | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k3_zfmisc_1(D_1932, E_1931, F_1933))), inference(negUnitSimplification, [status(thm)], [c_7996, c_9647])).
% 9.35/3.22  tff(c_9655, plain, (![C_7, A_5, B_6, C_1650]: (C_7='#skF_7' | k4_zfmisc_1(A_5, B_6, C_7, C_1650)!=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_7339, c_9649])).
% 9.35/3.22  tff(c_9667, plain, ('#skF_7'='#skF_3'), inference(reflexivity, [status(thm), theory('equality')], [c_9655])).
% 9.35/3.22  tff(c_7280, plain, (![D_1664, B_1665, A_1666, C_1667]: (D_1664=B_1665 | k1_xboole_0=B_1665 | k1_xboole_0=A_1666 | k2_zfmisc_1(C_1667, D_1664)!=k2_zfmisc_1(A_1666, B_1665))), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.35/3.22  tff(c_8371, plain, (![C_1806, A_1804, B_1805, C_1807, D_1808, D_1803]: (D_1808=D_1803 | k1_xboole_0=D_1808 | k3_zfmisc_1(A_1804, B_1805, C_1807)=k1_xboole_0 | k4_zfmisc_1(A_1804, B_1805, C_1807, D_1808)!=k2_zfmisc_1(C_1806, D_1803))), inference(superposition, [status(thm), theory('equality')], [c_8, c_7280])).
% 9.35/3.22  tff(c_8401, plain, (![D_1803, C_1806]: (D_1803='#skF_4' | k1_xboole_0='#skF_4' | k3_zfmisc_1('#skF_1', '#skF_6', '#skF_7')=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_zfmisc_1(C_1806, D_1803))), inference(superposition, [status(thm), theory('equality')], [c_7206, c_8371])).
% 9.35/3.22  tff(c_8411, plain, (![D_1803, C_1806]: (D_1803='#skF_4' | k3_zfmisc_1('#skF_1', '#skF_6', '#skF_7')=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_zfmisc_1(C_1806, D_1803))), inference(negUnitSimplification, [status(thm)], [c_26, c_8401])).
% 9.35/3.22  tff(c_8412, plain, (k3_zfmisc_1('#skF_1', '#skF_6', '#skF_7')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_8411])).
% 9.35/3.22  tff(c_8465, plain, (k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_8412, c_10])).
% 9.35/3.22  tff(c_8478, plain, (k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_32, c_8465])).
% 9.35/3.22  tff(c_8480, plain, (k1_xboole_0='#skF_6'), inference(splitLeft, [status(thm)], [c_8478])).
% 9.35/3.22  tff(c_8489, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_8480, c_7996])).
% 9.35/3.22  tff(c_7227, plain, (![A_1654, B_1655, C_1656, D_1657]: (k2_zfmisc_1(k3_zfmisc_1(A_1654, B_1655, C_1656), D_1657)=k4_zfmisc_1(A_1654, B_1655, C_1656, D_1657))), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.35/3.22  tff(c_7242, plain, (![A_12, C_14, D_1657]: (k4_zfmisc_1(A_12, k1_xboole_0, C_14, D_1657)=k2_zfmisc_1(k1_xboole_0, D_1657))), inference(superposition, [status(thm), theory('equality')], [c_14, c_7227])).
% 9.35/3.22  tff(c_7377, plain, (![A_1679, B_1680, C_1681]: (k4_zfmisc_1(A_1679, B_1680, C_1681, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_7340, c_12])).
% 9.35/3.22  tff(c_7245, plain, (![B_13, C_14, D_1657]: (k4_zfmisc_1(k1_xboole_0, B_13, C_14, D_1657)=k2_zfmisc_1(k1_xboole_0, D_1657))), inference(superposition, [status(thm), theory('equality')], [c_16, c_7227])).
% 9.35/3.22  tff(c_7383, plain, (k2_zfmisc_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_7377, c_7245])).
% 9.35/3.22  tff(c_7411, plain, (![C_7, C_1650]: (k4_zfmisc_1(k1_xboole_0, k1_xboole_0, C_7, C_1650)=k3_zfmisc_1(k1_xboole_0, C_7, C_1650))), inference(superposition, [status(thm), theory('equality')], [c_7383, c_7339])).
% 9.35/3.22  tff(c_7429, plain, (![C_1650]: (k2_zfmisc_1(k1_xboole_0, C_1650)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_7242, c_16, c_7411])).
% 9.35/3.22  tff(c_8462, plain, (![D_11]: (k4_zfmisc_1('#skF_1', '#skF_6', '#skF_7', D_11)=k2_zfmisc_1(k1_xboole_0, D_11))), inference(superposition, [status(thm), theory('equality')], [c_8412, c_8])).
% 9.35/3.22  tff(c_8475, plain, (![D_11]: (k4_zfmisc_1('#skF_1', '#skF_6', '#skF_7', D_11)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_7429, c_8462])).
% 9.35/3.22  tff(c_8862, plain, (![D_11]: (k4_zfmisc_1('#skF_1', '#skF_6', '#skF_7', D_11)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_8480, c_8475])).
% 9.35/3.22  tff(c_8863, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_8862, c_7206])).
% 9.35/3.22  tff(c_8865, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8489, c_8863])).
% 9.35/3.22  tff(c_8866, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_8478])).
% 9.35/3.22  tff(c_8876, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_8866, c_7996])).
% 9.35/3.22  tff(c_7374, plain, (![A_1675, B_1676, C_14]: (k4_zfmisc_1(A_1675, B_1676, k1_xboole_0, C_14)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_14, c_7340])).
% 9.35/3.22  tff(c_8888, plain, (![A_1675, B_1676, C_14]: (k4_zfmisc_1(A_1675, B_1676, '#skF_7', C_14)='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_8866, c_8866, c_7374])).
% 9.35/3.22  tff(c_9222, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_8888, c_7206])).
% 9.35/3.22  tff(c_9224, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8876, c_9222])).
% 9.35/3.22  tff(c_9226, plain, (k3_zfmisc_1('#skF_1', '#skF_6', '#skF_7')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_8411])).
% 9.35/3.22  tff(c_7326, plain, (![C_1671, A_1672, B_1673, D_1674]: (C_1671=A_1672 | k1_xboole_0=B_1673 | k1_xboole_0=A_1672 | k2_zfmisc_1(C_1671, D_1674)!=k2_zfmisc_1(A_1672, B_1673))), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.35/3.22  tff(c_9393, plain, (![D_1898, B_1896, C_1893, D_1894, C_1897, A_1895]: (k3_zfmisc_1(A_1895, B_1896, C_1897)=C_1893 | k1_xboole_0=D_1898 | k3_zfmisc_1(A_1895, B_1896, C_1897)=k1_xboole_0 | k4_zfmisc_1(A_1895, B_1896, C_1897, D_1898)!=k2_zfmisc_1(C_1893, D_1894))), inference(superposition, [status(thm), theory('equality')], [c_8, c_7326])).
% 9.35/3.22  tff(c_9423, plain, (![C_1893, D_1894]: (k3_zfmisc_1('#skF_1', '#skF_6', '#skF_7')=C_1893 | k1_xboole_0='#skF_4' | k3_zfmisc_1('#skF_1', '#skF_6', '#skF_7')=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_zfmisc_1(C_1893, D_1894))), inference(superposition, [status(thm), theory('equality')], [c_7206, c_9393])).
% 9.35/3.22  tff(c_9434, plain, (![C_1899, D_1900]: (k3_zfmisc_1('#skF_1', '#skF_6', '#skF_7')=C_1899 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_zfmisc_1(C_1899, D_1900))), inference(negUnitSimplification, [status(thm)], [c_9226, c_26, c_9423])).
% 9.35/3.22  tff(c_9443, plain, (![A_8, B_9, C_10, D_11]: (k3_zfmisc_1(A_8, B_9, C_10)=k3_zfmisc_1('#skF_1', '#skF_6', '#skF_7') | k4_zfmisc_1(A_8, B_9, C_10, D_11)!=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_8, c_9434])).
% 9.35/3.22  tff(c_9694, plain, (k3_zfmisc_1('#skF_1', '#skF_6', '#skF_7')=k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')), inference(reflexivity, [status(thm), theory('equality')], [c_9443])).
% 9.35/3.22  tff(c_9738, plain, (k3_zfmisc_1('#skF_1', '#skF_6', '#skF_3')=k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_9667, c_9694])).
% 9.35/3.22  tff(c_9789, plain, (![D_11]: (k2_zfmisc_1(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'), D_11)=k4_zfmisc_1('#skF_1', '#skF_6', '#skF_3', D_11))), inference(superposition, [status(thm), theory('equality')], [c_9738, c_8])).
% 9.35/3.22  tff(c_9912, plain, (![D_1949]: (k4_zfmisc_1('#skF_1', '#skF_6', '#skF_3', D_1949)=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', D_1949))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_9789])).
% 9.35/3.22  tff(c_7349, plain, (![A_1675, B_1676, C_1677, C_1678]: (k4_zfmisc_1(A_1675, B_1676, C_1677, C_1678)!=k1_xboole_0 | k1_xboole_0=C_1678 | k1_xboole_0=C_1677 | k2_zfmisc_1(A_1675, B_1676)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_7340, c_10])).
% 9.35/3.22  tff(c_9953, plain, (![D_1949]: (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', D_1949)!=k1_xboole_0 | k1_xboole_0=D_1949 | k1_xboole_0='#skF_3' | k2_zfmisc_1('#skF_1', '#skF_6')=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_9912, c_7349])).
% 9.35/3.22  tff(c_9980, plain, (![D_1949]: (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', D_1949)!=k1_xboole_0 | k1_xboole_0=D_1949 | k2_zfmisc_1('#skF_1', '#skF_6')=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_28, c_9953])).
% 9.35/3.22  tff(c_10034, plain, (k2_zfmisc_1('#skF_1', '#skF_6')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_9980])).
% 9.35/3.22  tff(c_7509, plain, (![C_1694]: (k2_zfmisc_1(k1_xboole_0, C_1694)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_7242, c_16, c_7411])).
% 9.35/3.22  tff(c_7523, plain, (![C_1694, B_2, A_1]: (C_1694=B_2 | k1_xboole_0=B_2 | k1_xboole_0=A_1 | k2_zfmisc_1(A_1, B_2)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_7509, c_2])).
% 9.35/3.22  tff(c_10087, plain, (![C_1694]: (C_1694='#skF_6' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_10034, c_7523])).
% 9.35/3.22  tff(c_10114, plain, (![C_1694]: (C_1694='#skF_6' | k1_xboole_0='#skF_6')), inference(negUnitSimplification, [status(thm)], [c_32, c_10087])).
% 9.35/3.22  tff(c_10120, plain, (k1_xboole_0='#skF_6'), inference(splitLeft, [status(thm)], [c_10114])).
% 9.35/3.22  tff(c_9732, plain, (k3_zfmisc_1('#skF_1', '#skF_6', '#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_9667, c_9226])).
% 9.35/3.22  tff(c_9739, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_9738, c_9732])).
% 9.35/3.22  tff(c_10125, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_10120, c_9739])).
% 9.35/3.22  tff(c_10105, plain, (![C_7]: (k3_zfmisc_1('#skF_1', '#skF_6', C_7)=k2_zfmisc_1(k1_xboole_0, C_7))), inference(superposition, [status(thm), theory('equality')], [c_10034, c_6])).
% 9.35/3.22  tff(c_10118, plain, (![C_7]: (k3_zfmisc_1('#skF_1', '#skF_6', C_7)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_7429, c_10105])).
% 9.35/3.22  tff(c_10341, plain, (![C_7]: (k3_zfmisc_1('#skF_1', '#skF_6', C_7)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_10120, c_10118])).
% 9.35/3.22  tff(c_10342, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_10341, c_9738])).
% 9.35/3.22  tff(c_10440, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10125, c_10342])).
% 9.35/3.22  tff(c_10441, plain, (![C_1694]: (C_1694='#skF_6')), inference(splitRight, [status(thm)], [c_10114])).
% 9.35/3.22  tff(c_10442, plain, (k1_xboole_0!='#skF_6'), inference(splitRight, [status(thm)], [c_10114])).
% 9.35/3.22  tff(c_10738, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_10441, c_10442])).
% 9.35/3.22  tff(c_10740, plain, (k2_zfmisc_1('#skF_1', '#skF_6')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_9980])).
% 9.35/3.22  tff(c_7338, plain, (![B_6, C_7, A_5, C_1671, D_1674]: (k2_zfmisc_1(A_5, B_6)=C_1671 | k1_xboole_0=C_7 | k2_zfmisc_1(A_5, B_6)=k1_xboole_0 | k3_zfmisc_1(A_5, B_6, C_7)!=k2_zfmisc_1(C_1671, D_1674))), inference(superposition, [status(thm), theory('equality')], [c_6, c_7326])).
% 9.35/3.22  tff(c_9754, plain, (![C_1671, D_1674]: (k2_zfmisc_1('#skF_1', '#skF_6')=C_1671 | k1_xboole_0='#skF_3' | k2_zfmisc_1('#skF_1', '#skF_6')=k1_xboole_0 | k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')!=k2_zfmisc_1(C_1671, D_1674))), inference(superposition, [status(thm), theory('equality')], [c_9738, c_7338])).
% 9.35/3.22  tff(c_9798, plain, (![C_1671, D_1674]: (k2_zfmisc_1('#skF_1', '#skF_6')=C_1671 | k2_zfmisc_1('#skF_1', '#skF_6')=k1_xboole_0 | k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')!=k2_zfmisc_1(C_1671, D_1674))), inference(negUnitSimplification, [status(thm)], [c_28, c_9754])).
% 9.35/3.22  tff(c_11044, plain, (![C_2633, D_2634]: (k2_zfmisc_1('#skF_1', '#skF_6')=C_2633 | k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')!=k2_zfmisc_1(C_2633, D_2634))), inference(negUnitSimplification, [status(thm)], [c_10740, c_9798])).
% 9.35/3.22  tff(c_11056, plain, (![A_5, B_6, C_7]: (k2_zfmisc_1(A_5, B_6)=k2_zfmisc_1('#skF_1', '#skF_6') | k3_zfmisc_1(A_5, B_6, C_7)!=k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_6, c_11044])).
% 9.35/3.22  tff(c_11060, plain, (k2_zfmisc_1('#skF_1', '#skF_6')=k2_zfmisc_1('#skF_1', '#skF_2')), inference(reflexivity, [status(thm), theory('equality')], [c_11056])).
% 9.35/3.22  tff(c_11116, plain, (![C_7]: (k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), C_7)=k3_zfmisc_1('#skF_1', '#skF_6', C_7))), inference(superposition, [status(thm), theory('equality')], [c_11060, c_6])).
% 9.35/3.22  tff(c_11128, plain, (![C_2638]: (k3_zfmisc_1('#skF_1', '#skF_6', C_2638)=k3_zfmisc_1('#skF_1', '#skF_2', C_2638))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_11116])).
% 9.35/3.22  tff(c_11219, plain, (![C_2638]: (k3_zfmisc_1('#skF_1', '#skF_2', C_2638)!=k1_xboole_0 | k1_xboole_0=C_2638 | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_11128, c_10])).
% 9.35/3.22  tff(c_11256, plain, (![C_2638]: (k3_zfmisc_1('#skF_1', '#skF_2', C_2638)!=k1_xboole_0 | k1_xboole_0=C_2638 | k1_xboole_0='#skF_6')), inference(negUnitSimplification, [status(thm)], [c_32, c_11219])).
% 9.35/3.22  tff(c_11308, plain, (k1_xboole_0='#skF_6'), inference(splitLeft, [status(thm)], [c_11256])).
% 9.35/3.22  tff(c_11090, plain, (k2_zfmisc_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_11060, c_10740])).
% 9.35/3.22  tff(c_11310, plain, (k2_zfmisc_1('#skF_1', '#skF_2')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_11308, c_11090])).
% 9.35/3.22  tff(c_7612, plain, (![B_1707, A_1708]: (k1_xboole_0=B_1707 | k1_xboole_0=B_1707 | k1_xboole_0=A_1708 | k2_zfmisc_1(A_1708, B_1707)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_7383, c_2])).
% 9.35/3.22  tff(c_7702, plain, (![C_1722, A_1723, B_1724]: (k1_xboole_0=C_1722 | k1_xboole_0=C_1722 | k2_zfmisc_1(A_1723, B_1724)=k1_xboole_0 | k3_zfmisc_1(A_1723, B_1724, C_1722)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_6, c_7612])).
% 9.35/3.22  tff(c_7718, plain, (![C_14, A_12]: (k1_xboole_0=C_14 | k2_zfmisc_1(A_12, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_14, c_7702])).
% 9.35/3.22  tff(c_7721, plain, (![A_12]: (k2_zfmisc_1(A_12, k1_xboole_0)=k1_xboole_0)), inference(splitLeft, [status(thm)], [c_7718])).
% 9.35/3.22  tff(c_11341, plain, (![A_12]: (k2_zfmisc_1(A_12, '#skF_6')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_11308, c_11308, c_7721])).
% 9.35/3.22  tff(c_11392, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_11341, c_11060])).
% 9.35/3.22  tff(c_11471, plain, $false, inference(negUnitSimplification, [status(thm)], [c_11310, c_11392])).
% 9.35/3.22  tff(c_11473, plain, (k1_xboole_0!='#skF_6'), inference(splitRight, [status(thm)], [c_11256])).
% 9.35/3.22  tff(c_11113, plain, (![D_4, C_3]: (D_4='#skF_6' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_1' | k2_zfmisc_1(C_3, D_4)!=k2_zfmisc_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_11060, c_2])).
% 9.35/3.22  tff(c_11124, plain, (![D_4, C_3]: (D_4='#skF_6' | k1_xboole_0='#skF_6' | k2_zfmisc_1(C_3, D_4)!=k2_zfmisc_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_32, c_11113])).
% 9.35/3.22  tff(c_11504, plain, (![D_4, C_3]: (D_4='#skF_6' | k2_zfmisc_1(C_3, D_4)!=k2_zfmisc_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_11473, c_11124])).
% 9.35/3.22  tff(c_11507, plain, ('#skF_6'='#skF_2'), inference(reflexivity, [status(thm), theory('equality')], [c_11504])).
% 9.35/3.22  tff(c_11509, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7190, c_11507])).
% 9.35/3.22  tff(c_11510, plain, (k2_zfmisc_1('#skF_1', '#skF_6')=k1_xboole_0 | k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_7995])).
% 9.35/3.22  tff(c_11512, plain, (k1_xboole_0='#skF_7'), inference(splitLeft, [status(thm)], [c_11510])).
% 9.35/3.22  tff(c_11536, plain, ('#skF_7'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_11512, c_26])).
% 9.35/3.22  tff(c_11518, plain, (![A_12]: (k2_zfmisc_1(A_12, '#skF_7')='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_11512, c_11512, c_7721])).
% 9.35/3.22  tff(c_11537, plain, ('#skF_7'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_11512, c_28])).
% 9.35/3.22  tff(c_11538, plain, ('#skF_7'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_11512, c_32])).
% 9.35/3.22  tff(c_11535, plain, ('#skF_7'!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_11512, c_30])).
% 9.35/3.22  tff(c_11511, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_7995])).
% 9.35/3.22  tff(c_11559, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_11512, c_11511])).
% 9.35/3.22  tff(c_7286, plain, (![D_11, A_8, C_1667, D_1664, C_10, B_9]: (D_1664=D_11 | k1_xboole_0=D_11 | k3_zfmisc_1(A_8, B_9, C_10)=k1_xboole_0 | k4_zfmisc_1(A_8, B_9, C_10, D_11)!=k2_zfmisc_1(C_1667, D_1664))), inference(superposition, [status(thm), theory('equality')], [c_8, c_7280])).
% 9.35/3.22  tff(c_11826, plain, (![B_2687, A_2686, C_2689, D_2690, C_2688, D_2685]: (D_2690=D_2685 | D_2690='#skF_7' | k3_zfmisc_1(A_2686, B_2687, C_2689)='#skF_7' | k4_zfmisc_1(A_2686, B_2687, C_2689, D_2690)!=k2_zfmisc_1(C_2688, D_2685))), inference(demodulation, [status(thm), theory('equality')], [c_11512, c_11512, c_7286])).
% 9.35/3.22  tff(c_11844, plain, (![D_2685, C_2688]: (D_2685='#skF_4' | '#skF_7'='#skF_4' | k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')='#skF_7' | k2_zfmisc_1(C_2688, D_2685)!='#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_11559, c_11826])).
% 9.35/3.22  tff(c_11854, plain, (![D_2685, C_2688]: (D_2685='#skF_4' | k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')='#skF_7' | k2_zfmisc_1(C_2688, D_2685)!='#skF_7')), inference(negUnitSimplification, [status(thm)], [c_11536, c_11844])).
% 9.35/3.22  tff(c_11858, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')='#skF_7'), inference(splitLeft, [status(thm)], [c_11854])).
% 9.35/3.22  tff(c_7292, plain, (![B_6, C_7, C_1667, D_1664, A_5]: (D_1664=C_7 | k1_xboole_0=C_7 | k2_zfmisc_1(A_5, B_6)=k1_xboole_0 | k3_zfmisc_1(A_5, B_6, C_7)!=k2_zfmisc_1(C_1667, D_1664))), inference(superposition, [status(thm), theory('equality')], [c_6, c_7280])).
% 9.35/3.22  tff(c_11543, plain, (![B_6, C_7, C_1667, D_1664, A_5]: (D_1664=C_7 | C_7='#skF_7' | k2_zfmisc_1(A_5, B_6)='#skF_7' | k3_zfmisc_1(A_5, B_6, C_7)!=k2_zfmisc_1(C_1667, D_1664))), inference(demodulation, [status(thm), theory('equality')], [c_11512, c_11512, c_7292])).
% 9.35/3.22  tff(c_11865, plain, (![D_1664, C_1667]: (D_1664='#skF_3' | '#skF_7'='#skF_3' | k2_zfmisc_1('#skF_1', '#skF_2')='#skF_7' | k2_zfmisc_1(C_1667, D_1664)!='#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_11858, c_11543])).
% 9.35/3.22  tff(c_11875, plain, (![D_1664, C_1667]: (D_1664='#skF_3' | k2_zfmisc_1('#skF_1', '#skF_2')='#skF_7' | k2_zfmisc_1(C_1667, D_1664)!='#skF_7')), inference(negUnitSimplification, [status(thm)], [c_11537, c_11865])).
% 9.35/3.22  tff(c_11978, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_7'), inference(splitLeft, [status(thm)], [c_11875])).
% 9.35/3.22  tff(c_11532, plain, (![A_12, B_13]: (k3_zfmisc_1(A_12, B_13, '#skF_7')='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_11512, c_11512, c_12])).
% 9.35/3.22  tff(c_11524, plain, (![A_1675, B_1676, C_14]: (k4_zfmisc_1(A_1675, B_1676, '#skF_7', C_14)='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_11512, c_11512, c_7374])).
% 9.35/3.22  tff(c_7329, plain, (![D_11, A_8, B_1673, C_10, B_9, A_1672]: (k3_zfmisc_1(A_8, B_9, C_10)=A_1672 | k1_xboole_0=B_1673 | k1_xboole_0=A_1672 | k4_zfmisc_1(A_8, B_9, C_10, D_11)!=k2_zfmisc_1(A_1672, B_1673))), inference(superposition, [status(thm), theory('equality')], [c_8, c_7326])).
% 9.35/3.22  tff(c_11918, plain, (![A_2694, D_2699, A_2696, B_2695, C_2698, B_2697]: (k3_zfmisc_1(A_2694, B_2697, C_2698)=A_2696 | B_2695='#skF_7' | A_2696='#skF_7' | k4_zfmisc_1(A_2694, B_2697, C_2698, D_2699)!=k2_zfmisc_1(A_2696, B_2695))), inference(demodulation, [status(thm), theory('equality')], [c_11512, c_11512, c_7329])).
% 9.35/3.22  tff(c_11930, plain, (![A_1675, B_1676, A_2696, B_2695]: (k3_zfmisc_1(A_1675, B_1676, '#skF_7')=A_2696 | B_2695='#skF_7' | A_2696='#skF_7' | k2_zfmisc_1(A_2696, B_2695)!='#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_11524, c_11918])).
% 9.35/3.22  tff(c_12098, plain, (![A_2710, B_2711]: (A_2710='#skF_7' | B_2711='#skF_7' | A_2710='#skF_7' | k2_zfmisc_1(A_2710, B_2711)!='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_11532, c_11930])).
% 9.35/3.22  tff(c_12101, plain, ('#skF_7'='#skF_2' | '#skF_7'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_11978, c_12098])).
% 9.35/3.22  tff(c_12117, plain, $false, inference(negUnitSimplification, [status(thm)], [c_11538, c_11535, c_11538, c_12101])).
% 9.35/3.22  tff(c_12154, plain, (![D_2718, C_2719]: (D_2718='#skF_3' | k2_zfmisc_1(C_2719, D_2718)!='#skF_7')), inference(splitRight, [status(thm)], [c_11875])).
% 9.35/3.22  tff(c_12157, plain, ('#skF_7'='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_11518, c_12154])).
% 9.35/3.22  tff(c_12170, plain, $false, inference(negUnitSimplification, [status(thm)], [c_11537, c_12157])).
% 9.35/3.22  tff(c_12174, plain, (![D_2720, C_2721]: (D_2720='#skF_4' | k2_zfmisc_1(C_2721, D_2720)!='#skF_7')), inference(splitRight, [status(thm)], [c_11854])).
% 9.35/3.22  tff(c_12177, plain, ('#skF_7'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_11518, c_12174])).
% 9.35/3.22  tff(c_12190, plain, $false, inference(negUnitSimplification, [status(thm)], [c_11536, c_12177])).
% 9.35/3.22  tff(c_12191, plain, (k2_zfmisc_1('#skF_1', '#skF_6')=k1_xboole_0), inference(splitRight, [status(thm)], [c_11510])).
% 9.35/3.22  tff(c_12197, plain, (![C_1694]: (C_1694='#skF_6' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_12191, c_7523])).
% 9.35/3.22  tff(c_12223, plain, (![C_1694]: (C_1694='#skF_6' | k1_xboole_0='#skF_6')), inference(negUnitSimplification, [status(thm)], [c_32, c_12197])).
% 9.35/3.22  tff(c_12229, plain, (k1_xboole_0='#skF_6'), inference(splitLeft, [status(thm)], [c_12223])).
% 9.35/3.22  tff(c_12256, plain, ('#skF_6'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_12229, c_28])).
% 9.35/3.22  tff(c_12237, plain, (![A_12]: (k2_zfmisc_1(A_12, '#skF_6')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_12229, c_12229, c_7721])).
% 9.35/3.22  tff(c_12257, plain, ('#skF_6'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_12229, c_32])).
% 9.35/3.22  tff(c_12255, plain, ('#skF_6'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_12229, c_26])).
% 9.35/3.22  tff(c_12495, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_12229, c_11511])).
% 9.35/3.22  tff(c_12392, plain, (![D_11, A_8, C_1667, D_1664, C_10, B_9]: (D_1664=D_11 | D_11='#skF_6' | k3_zfmisc_1(A_8, B_9, C_10)='#skF_6' | k4_zfmisc_1(A_8, B_9, C_10, D_11)!=k2_zfmisc_1(C_1667, D_1664))), inference(demodulation, [status(thm), theory('equality')], [c_12229, c_12229, c_7286])).
% 9.35/3.22  tff(c_12500, plain, (![D_1664, C_1667]: (D_1664='#skF_4' | '#skF_6'='#skF_4' | k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')='#skF_6' | k2_zfmisc_1(C_1667, D_1664)!='#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_12495, c_12392])).
% 9.35/3.22  tff(c_12503, plain, (![D_1664, C_1667]: (D_1664='#skF_4' | k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')='#skF_6' | k2_zfmisc_1(C_1667, D_1664)!='#skF_6')), inference(negUnitSimplification, [status(thm)], [c_12255, c_12500])).
% 9.35/3.22  tff(c_12694, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')='#skF_6'), inference(splitLeft, [status(thm)], [c_12503])).
% 9.35/3.22  tff(c_12262, plain, (![B_6, C_7, C_1667, D_1664, A_5]: (D_1664=C_7 | C_7='#skF_6' | k2_zfmisc_1(A_5, B_6)='#skF_6' | k3_zfmisc_1(A_5, B_6, C_7)!=k2_zfmisc_1(C_1667, D_1664))), inference(demodulation, [status(thm), theory('equality')], [c_12229, c_12229, c_7292])).
% 9.35/3.22  tff(c_12701, plain, (![D_1664, C_1667]: (D_1664='#skF_3' | '#skF_6'='#skF_3' | k2_zfmisc_1('#skF_1', '#skF_2')='#skF_6' | k2_zfmisc_1(C_1667, D_1664)!='#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_12694, c_12262])).
% 9.35/3.22  tff(c_12711, plain, (![D_1664, C_1667]: (D_1664='#skF_3' | k2_zfmisc_1('#skF_1', '#skF_2')='#skF_6' | k2_zfmisc_1(C_1667, D_1664)!='#skF_6')), inference(negUnitSimplification, [status(thm)], [c_12256, c_12701])).
% 9.35/3.22  tff(c_12784, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_6'), inference(splitLeft, [status(thm)], [c_12711])).
% 9.35/3.22  tff(c_12943, plain, (![C_2782, B_2783, A_2784]: (C_2782=B_2783 | B_2783='#skF_6' | A_2784='#skF_6' | k2_zfmisc_1(A_2784, B_2783)!='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_12229, c_12229, c_12229, c_7523])).
% 9.35/3.22  tff(c_12945, plain, (![C_2782]: (C_2782='#skF_2' | '#skF_6'='#skF_2' | '#skF_6'='#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_12784, c_12943])).
% 9.35/3.22  tff(c_12961, plain, (![C_2785]: (C_2785='#skF_2')), inference(negUnitSimplification, [status(thm)], [c_12257, c_7190, c_12945])).
% 9.35/3.22  tff(c_12253, plain, (![B_13, C_14]: (k3_zfmisc_1('#skF_6', B_13, C_14)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_12229, c_12229, c_16])).
% 9.35/3.22  tff(c_12788, plain, (![C_7, C_1650]: (k4_zfmisc_1('#skF_1', '#skF_2', C_7, C_1650)=k3_zfmisc_1('#skF_6', C_7, C_1650))), inference(superposition, [status(thm), theory('equality')], [c_12784, c_7339])).
% 9.35/3.22  tff(c_12794, plain, (![C_7, C_1650]: (k4_zfmisc_1('#skF_1', '#skF_2', C_7, C_1650)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_12253, c_12788])).
% 9.35/3.22  tff(c_12993, plain, ('#skF_6'='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_12961, c_12794])).
% 9.35/3.22  tff(c_13122, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7190, c_12993])).
% 9.35/3.22  tff(c_13125, plain, (![D_3083, C_3084]: (D_3083='#skF_3' | k2_zfmisc_1(C_3084, D_3083)!='#skF_6')), inference(splitRight, [status(thm)], [c_12711])).
% 9.35/3.22  tff(c_13128, plain, ('#skF_6'='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_12237, c_13125])).
% 9.35/3.22  tff(c_13141, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12256, c_13128])).
% 9.35/3.22  tff(c_13143, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')!='#skF_6'), inference(splitRight, [status(thm)], [c_12503])).
% 9.35/3.22  tff(c_12244, plain, (![C_1650]: (k2_zfmisc_1('#skF_6', C_1650)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_12229, c_12229, c_7429])).
% 9.35/3.22  tff(c_7332, plain, (![D_11, A_8, C_10, B_9, C_1671, D_1674]: (k3_zfmisc_1(A_8, B_9, C_10)=C_1671 | k1_xboole_0=D_11 | k3_zfmisc_1(A_8, B_9, C_10)=k1_xboole_0 | k4_zfmisc_1(A_8, B_9, C_10, D_11)!=k2_zfmisc_1(C_1671, D_1674))), inference(superposition, [status(thm), theory('equality')], [c_8, c_7326])).
% 9.35/3.22  tff(c_13145, plain, (![B_3088, D_3090, C_3085, D_3086, A_3087, C_3089]: (k3_zfmisc_1(A_3087, B_3088, C_3089)=C_3085 | D_3090='#skF_6' | k3_zfmisc_1(A_3087, B_3088, C_3089)='#skF_6' | k4_zfmisc_1(A_3087, B_3088, C_3089, D_3090)!=k2_zfmisc_1(C_3085, D_3086))), inference(demodulation, [status(thm), theory('equality')], [c_12229, c_12229, c_7332])).
% 9.35/3.22  tff(c_13160, plain, (![C_3085, D_3086]: (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')=C_3085 | '#skF_6'='#skF_4' | k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')='#skF_6' | k2_zfmisc_1(C_3085, D_3086)!='#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_12495, c_13145])).
% 9.35/3.22  tff(c_13177, plain, (![C_3085, D_3086]: (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')=C_3085 | k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')='#skF_6' | k2_zfmisc_1(C_3085, D_3086)!='#skF_6')), inference(negUnitSimplification, [status(thm)], [c_12255, c_13160])).
% 9.35/3.22  tff(c_13181, plain, (![C_3091, D_3092]: (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')=C_3091 | k2_zfmisc_1(C_3091, D_3092)!='#skF_6')), inference(negUnitSimplification, [status(thm)], [c_13143, c_13177])).
% 9.35/3.22  tff(c_13185, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_12244, c_13181])).
% 9.35/3.22  tff(c_13194, plain, $false, inference(negUnitSimplification, [status(thm)], [c_13143, c_13185])).
% 9.35/3.22  tff(c_13195, plain, (![C_1694]: (C_1694='#skF_6')), inference(splitRight, [status(thm)], [c_12223])).
% 9.35/3.22  tff(c_13196, plain, (k1_xboole_0!='#skF_6'), inference(splitRight, [status(thm)], [c_12223])).
% 9.35/3.22  tff(c_13376, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_13195, c_13196])).
% 9.35/3.22  tff(c_13379, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_7718])).
% 9.35/3.22  tff(c_13377, plain, (![C_14]: (k1_xboole_0=C_14)), inference(splitRight, [status(thm)], [c_7718])).
% 9.35/3.22  tff(c_13445, plain, (![C_3563]: (C_3563='#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_13379, c_13377])).
% 9.35/3.22  tff(c_13498, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_13445, c_32])).
% 9.35/3.22  tff(c_13499, plain, ('#skF_7'!='#skF_3'), inference(splitRight, [status(thm)], [c_7184])).
% 9.35/3.22  tff(c_13500, plain, ('#skF_6'='#skF_2'), inference(splitRight, [status(thm)], [c_7184])).
% 9.35/3.22  tff(c_13520, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_7', '#skF_4')=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_13500, c_5425, c_7185, c_34])).
% 9.35/3.22  tff(c_13640, plain, (![D_3713, B_3714, A_3715, C_3716]: (D_3713=B_3714 | k1_xboole_0=B_3714 | k1_xboole_0=A_3715 | k2_zfmisc_1(C_3716, D_3713)!=k2_zfmisc_1(A_3715, B_3714))), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.35/3.22  tff(c_14653, plain, (![C_3840, A_3842, D_3845, D_3841, B_3843, C_3844]: (D_3845=D_3841 | k1_xboole_0=D_3845 | k3_zfmisc_1(A_3842, B_3843, C_3844)=k1_xboole_0 | k4_zfmisc_1(A_3842, B_3843, C_3844, D_3845)!=k2_zfmisc_1(C_3840, D_3841))), inference(superposition, [status(thm), theory('equality')], [c_8, c_13640])).
% 9.35/3.22  tff(c_14683, plain, (![D_3841, C_3840]: (D_3841='#skF_4' | k1_xboole_0='#skF_4' | k3_zfmisc_1('#skF_1', '#skF_2', '#skF_7')=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_zfmisc_1(C_3840, D_3841))), inference(superposition, [status(thm), theory('equality')], [c_13520, c_14653])).
% 9.35/3.22  tff(c_14693, plain, (![D_3841, C_3840]: (D_3841='#skF_4' | k3_zfmisc_1('#skF_1', '#skF_2', '#skF_7')=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_zfmisc_1(C_3840, D_3841))), inference(negUnitSimplification, [status(thm)], [c_26, c_14683])).
% 9.35/3.22  tff(c_14694, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_7')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_14693])).
% 9.35/3.22  tff(c_14741, plain, (k1_xboole_0='#skF_7' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_14694, c_10])).
% 9.35/3.22  tff(c_14756, plain, (k1_xboole_0='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_32, c_30, c_14741])).
% 9.35/3.22  tff(c_13505, plain, (![A_3690, B_3691, C_3692]: (k2_zfmisc_1(k2_zfmisc_1(A_3690, B_3691), C_3692)=k3_zfmisc_1(A_3690, B_3691, C_3692))), inference(cnfTransformation, [status(thm)], [f_37])).
% 9.35/3.22  tff(c_13514, plain, (![A_5, B_6, C_7, C_3692]: (k3_zfmisc_1(k2_zfmisc_1(A_5, B_6), C_7, C_3692)=k2_zfmisc_1(k3_zfmisc_1(A_5, B_6, C_7), C_3692))), inference(superposition, [status(thm), theory('equality')], [c_6, c_13505])).
% 9.35/3.22  tff(c_13680, plain, (![A_3723, B_3724, C_3725, C_3726]: (k3_zfmisc_1(k2_zfmisc_1(A_3723, B_3724), C_3725, C_3726)=k4_zfmisc_1(A_3723, B_3724, C_3725, C_3726))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_13514])).
% 9.35/3.22  tff(c_14309, plain, (![A_3791, B_3792, C_3793, C_3794]: (k4_zfmisc_1(A_3791, B_3792, C_3793, C_3794)!=k1_xboole_0 | k1_xboole_0=C_3794 | k1_xboole_0=C_3793 | k2_zfmisc_1(A_3791, B_3792)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_13680, c_10])).
% 9.35/3.22  tff(c_14327, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_7' | k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_13520, c_14309])).
% 9.35/3.22  tff(c_14337, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_7' | k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_26, c_14327])).
% 9.35/3.22  tff(c_14338, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_14337])).
% 9.35/3.22  tff(c_14767, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_14756, c_14338])).
% 9.35/3.22  tff(c_13720, plain, (![A_3723, B_3724, C_14]: (k4_zfmisc_1(A_3723, B_3724, k1_xboole_0, C_14)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_14, c_13680])).
% 9.35/3.22  tff(c_14777, plain, (![A_3723, B_3724, C_14]: (k4_zfmisc_1(A_3723, B_3724, '#skF_7', C_14)='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_14756, c_14756, c_13720])).
% 9.35/3.22  tff(c_15014, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_14777, c_13520])).
% 9.35/3.22  tff(c_15016, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14767, c_15014])).
% 9.35/3.22  tff(c_15018, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_7')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_14693])).
% 9.35/3.22  tff(c_13623, plain, (![C_3709, A_3710, B_3711, D_3712]: (C_3709=A_3710 | k1_xboole_0=B_3711 | k1_xboole_0=A_3710 | k2_zfmisc_1(C_3709, D_3712)!=k2_zfmisc_1(A_3710, B_3711))), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.35/3.22  tff(c_15366, plain, (![A_3913, B_3914, C_3912, D_3917, D_3916, C_3915]: (k3_zfmisc_1(A_3913, B_3914, C_3915)=C_3912 | k1_xboole_0=D_3917 | k3_zfmisc_1(A_3913, B_3914, C_3915)=k1_xboole_0 | k4_zfmisc_1(A_3913, B_3914, C_3915, D_3917)!=k2_zfmisc_1(C_3912, D_3916))), inference(superposition, [status(thm), theory('equality')], [c_8, c_13623])).
% 9.35/3.22  tff(c_15396, plain, (![C_3912, D_3916]: (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_7')=C_3912 | k1_xboole_0='#skF_4' | k3_zfmisc_1('#skF_1', '#skF_2', '#skF_7')=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_zfmisc_1(C_3912, D_3916))), inference(superposition, [status(thm), theory('equality')], [c_13520, c_15366])).
% 9.35/3.22  tff(c_15407, plain, (![C_3918, D_3919]: (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_7')=C_3918 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_zfmisc_1(C_3918, D_3919))), inference(negUnitSimplification, [status(thm)], [c_15018, c_26, c_15396])).
% 9.35/3.22  tff(c_15416, plain, (![A_8, B_9, C_10, D_11]: (k3_zfmisc_1(A_8, B_9, C_10)=k3_zfmisc_1('#skF_1', '#skF_2', '#skF_7') | k4_zfmisc_1(A_8, B_9, C_10, D_11)!=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_8, c_15407])).
% 9.35/3.22  tff(c_15445, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_7')=k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')), inference(reflexivity, [status(thm), theory('equality')], [c_15416])).
% 9.35/3.22  tff(c_15534, plain, (![D_11]: (k2_zfmisc_1(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'), D_11)=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_7', D_11))), inference(superposition, [status(thm), theory('equality')], [c_15445, c_8])).
% 9.35/3.22  tff(c_15546, plain, (![D_3927]: (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_7', D_3927)=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', D_3927))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_15534])).
% 9.35/3.22  tff(c_13692, plain, (![A_3723, B_3724, C_3725, C_3726]: (k4_zfmisc_1(A_3723, B_3724, C_3725, C_3726)!=k1_xboole_0 | k1_xboole_0=C_3726 | k1_xboole_0=C_3725 | k2_zfmisc_1(A_3723, B_3724)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_13680, c_10])).
% 9.35/3.22  tff(c_15581, plain, (![D_3927]: (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', D_3927)!=k1_xboole_0 | k1_xboole_0=D_3927 | k1_xboole_0='#skF_7' | k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_15546, c_13692])).
% 9.35/3.22  tff(c_15763, plain, (k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_15581])).
% 9.35/3.22  tff(c_13724, plain, (![A_3727, B_3728, C_3729]: (k4_zfmisc_1(A_3727, B_3728, C_3729, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_13680, c_12])).
% 9.35/3.22  tff(c_13525, plain, (![A_3693, B_3694, C_3695, D_3696]: (k2_zfmisc_1(k3_zfmisc_1(A_3693, B_3694, C_3695), D_3696)=k4_zfmisc_1(A_3693, B_3694, C_3695, D_3696))), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.35/3.22  tff(c_13540, plain, (![A_12, C_14, D_3696]: (k4_zfmisc_1(A_12, k1_xboole_0, C_14, D_3696)=k2_zfmisc_1(k1_xboole_0, D_3696))), inference(superposition, [status(thm), theory('equality')], [c_14, c_13525])).
% 9.35/3.22  tff(c_13730, plain, (k2_zfmisc_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_13724, c_13540])).
% 9.35/3.22  tff(c_13773, plain, (![C_7]: (k3_zfmisc_1(k1_xboole_0, k1_xboole_0, C_7)=k2_zfmisc_1(k1_xboole_0, C_7))), inference(superposition, [status(thm), theory('equality')], [c_13730, c_6])).
% 9.35/3.22  tff(c_13856, plain, (![C_3742]: (k2_zfmisc_1(k1_xboole_0, C_3742)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_13773])).
% 9.35/3.22  tff(c_13864, plain, (![C_3742, B_2, A_1]: (C_3742=B_2 | k1_xboole_0=B_2 | k1_xboole_0=A_1 | k2_zfmisc_1(A_1, B_2)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_13856, c_2])).
% 9.35/3.22  tff(c_15816, plain, (![C_3742]: (C_3742='#skF_2' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_15763, c_13864])).
% 9.35/3.22  tff(c_15849, plain, (![C_3960]: (C_3960='#skF_2')), inference(negUnitSimplification, [status(thm)], [c_32, c_30, c_15816])).
% 9.35/3.22  tff(c_15875, plain, (k1_xboole_0='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_15849, c_15763])).
% 9.35/3.23  tff(c_16172, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_15875])).
% 9.35/3.23  tff(c_16174, plain, (k2_zfmisc_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_15581])).
% 9.35/3.23  tff(c_16173, plain, (![D_3927]: (k1_xboole_0='#skF_7' | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', D_3927)!=k1_xboole_0 | k1_xboole_0=D_3927)), inference(splitRight, [status(thm)], [c_15581])).
% 9.35/3.23  tff(c_16175, plain, (k1_xboole_0='#skF_7'), inference(splitLeft, [status(thm)], [c_16173])).
% 9.35/3.23  tff(c_16219, plain, (![A_12, B_13]: (k3_zfmisc_1(A_12, B_13, '#skF_7')='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_16175, c_16175, c_12])).
% 9.35/3.23  tff(c_16364, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_16219, c_15445])).
% 9.35/3.23  tff(c_15481, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_15445, c_15018])).
% 9.35/3.23  tff(c_16183, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_16175, c_15481])).
% 9.35/3.23  tff(c_16480, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16364, c_16183])).
% 9.35/3.23  tff(c_16482, plain, (k1_xboole_0!='#skF_7'), inference(splitRight, [status(thm)], [c_16173])).
% 9.35/3.23  tff(c_13652, plain, (![B_6, C_7, A_5, C_3716, D_3713]: (D_3713=C_7 | k1_xboole_0=C_7 | k2_zfmisc_1(A_5, B_6)=k1_xboole_0 | k3_zfmisc_1(A_5, B_6, C_7)!=k2_zfmisc_1(C_3716, D_3713))), inference(superposition, [status(thm), theory('equality')], [c_6, c_13640])).
% 9.35/3.23  tff(c_15502, plain, (![D_3713, C_3716]: (D_3713='#skF_7' | k1_xboole_0='#skF_7' | k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0 | k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')!=k2_zfmisc_1(C_3716, D_3713))), inference(superposition, [status(thm), theory('equality')], [c_15445, c_13652])).
% 9.35/3.23  tff(c_16602, plain, (![D_4614, C_4615]: (D_4614='#skF_7' | k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')!=k2_zfmisc_1(C_4615, D_4614))), inference(negUnitSimplification, [status(thm)], [c_16174, c_16482, c_15502])).
% 9.35/3.23  tff(c_16614, plain, (![C_7, A_5, B_6]: (C_7='#skF_7' | k3_zfmisc_1(A_5, B_6, C_7)!=k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_6, c_16602])).
% 9.35/3.23  tff(c_16618, plain, ('#skF_7'='#skF_3'), inference(reflexivity, [status(thm), theory('equality')], [c_16614])).
% 9.35/3.23  tff(c_16620, plain, $false, inference(negUnitSimplification, [status(thm)], [c_13499, c_16618])).
% 9.35/3.23  tff(c_16621, plain, (k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0 | k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_14337])).
% 9.35/3.23  tff(c_16623, plain, (k1_xboole_0='#skF_7'), inference(splitLeft, [status(thm)], [c_16621])).
% 9.35/3.23  tff(c_16646, plain, ('#skF_7'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_16623, c_26])).
% 9.35/3.23  tff(c_13960, plain, (![B_3752, A_3753]: (k1_xboole_0=B_3752 | k1_xboole_0=B_3752 | k1_xboole_0=A_3753 | k2_zfmisc_1(A_3753, B_3752)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_13730, c_2])).
% 9.35/3.23  tff(c_14016, plain, (![C_3764, A_3765, B_3766]: (k1_xboole_0=C_3764 | k1_xboole_0=C_3764 | k2_zfmisc_1(A_3765, B_3766)=k1_xboole_0 | k3_zfmisc_1(A_3765, B_3766, C_3764)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_6, c_13960])).
% 9.35/3.23  tff(c_14032, plain, (![C_14, A_12]: (k1_xboole_0=C_14 | k2_zfmisc_1(A_12, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_14, c_14016])).
% 9.35/3.23  tff(c_14035, plain, (![A_12]: (k2_zfmisc_1(A_12, k1_xboole_0)=k1_xboole_0)), inference(splitLeft, [status(thm)], [c_14032])).
% 9.35/3.23  tff(c_16628, plain, (![A_12]: (k2_zfmisc_1(A_12, '#skF_7')='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_16623, c_16623, c_14035])).
% 9.35/3.23  tff(c_16648, plain, ('#skF_7'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_16623, c_32])).
% 9.35/3.23  tff(c_16645, plain, ('#skF_7'!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_16623, c_30])).
% 9.35/3.23  tff(c_16622, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_14337])).
% 9.35/3.23  tff(c_16669, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_16623, c_16622])).
% 9.35/3.23  tff(c_13646, plain, (![D_11, A_8, C_10, B_9, C_3716, D_3713]: (D_3713=D_11 | k1_xboole_0=D_11 | k3_zfmisc_1(A_8, B_9, C_10)=k1_xboole_0 | k4_zfmisc_1(A_8, B_9, C_10, D_11)!=k2_zfmisc_1(C_3716, D_3713))), inference(superposition, [status(thm), theory('equality')], [c_8, c_13640])).
% 9.35/3.23  tff(c_16941, plain, (![C_4640, C_4644, B_4643, D_4641, A_4642, D_4645]: (D_4645=D_4641 | D_4645='#skF_7' | k3_zfmisc_1(A_4642, B_4643, C_4644)='#skF_7' | k4_zfmisc_1(A_4642, B_4643, C_4644, D_4645)!=k2_zfmisc_1(C_4640, D_4641))), inference(demodulation, [status(thm), theory('equality')], [c_16623, c_16623, c_13646])).
% 9.35/3.23  tff(c_16956, plain, (![D_4641, C_4640]: (D_4641='#skF_4' | '#skF_7'='#skF_4' | k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')='#skF_7' | k2_zfmisc_1(C_4640, D_4641)!='#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_16669, c_16941])).
% 9.35/3.23  tff(c_16968, plain, (![D_4641, C_4640]: (D_4641='#skF_4' | k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')='#skF_7' | k2_zfmisc_1(C_4640, D_4641)!='#skF_7')), inference(negUnitSimplification, [status(thm)], [c_16646, c_16956])).
% 9.35/3.23  tff(c_16999, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')='#skF_7'), inference(splitLeft, [status(thm)], [c_16968])).
% 9.35/3.23  tff(c_16653, plain, (![B_6, C_7, A_5, C_3716, D_3713]: (D_3713=C_7 | C_7='#skF_7' | k2_zfmisc_1(A_5, B_6)='#skF_7' | k3_zfmisc_1(A_5, B_6, C_7)!=k2_zfmisc_1(C_3716, D_3713))), inference(demodulation, [status(thm), theory('equality')], [c_16623, c_16623, c_13652])).
% 9.35/3.23  tff(c_17006, plain, (![D_3713, C_3716]: (D_3713='#skF_3' | '#skF_7'='#skF_3' | k2_zfmisc_1('#skF_1', '#skF_2')='#skF_7' | k2_zfmisc_1(C_3716, D_3713)!='#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_16999, c_16653])).
% 9.35/3.23  tff(c_17015, plain, (![D_3713, C_3716]: (D_3713='#skF_3' | k2_zfmisc_1('#skF_1', '#skF_2')='#skF_7' | k2_zfmisc_1(C_3716, D_3713)!='#skF_7')), inference(negUnitSimplification, [status(thm)], [c_13499, c_17006])).
% 9.35/3.23  tff(c_17127, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_7'), inference(splitLeft, [status(thm)], [c_17015])).
% 9.35/3.23  tff(c_13632, plain, (![B_6, C_7, B_3711, A_3710, A_5]: (k2_zfmisc_1(A_5, B_6)=A_3710 | k1_xboole_0=B_3711 | k1_xboole_0=A_3710 | k3_zfmisc_1(A_5, B_6, C_7)!=k2_zfmisc_1(A_3710, B_3711))), inference(superposition, [status(thm), theory('equality')], [c_6, c_13623])).
% 9.35/3.23  tff(c_16854, plain, (![B_6, C_7, B_3711, A_3710, A_5]: (k2_zfmisc_1(A_5, B_6)=A_3710 | B_3711='#skF_7' | A_3710='#skF_7' | k3_zfmisc_1(A_5, B_6, C_7)!=k2_zfmisc_1(A_3710, B_3711))), inference(demodulation, [status(thm), theory('equality')], [c_16623, c_16623, c_13632])).
% 9.35/3.23  tff(c_17003, plain, (![A_3710, B_3711]: (k2_zfmisc_1('#skF_1', '#skF_2')=A_3710 | B_3711='#skF_7' | A_3710='#skF_7' | k2_zfmisc_1(A_3710, B_3711)!='#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_16999, c_16854])).
% 9.35/3.23  tff(c_17300, plain, (![A_4673, B_4674]: (A_4673='#skF_7' | B_4674='#skF_7' | A_4673='#skF_7' | k2_zfmisc_1(A_4673, B_4674)!='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_17127, c_17003])).
% 9.35/3.23  tff(c_17303, plain, ('#skF_7'='#skF_2' | '#skF_7'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_17127, c_17300])).
% 9.35/3.23  tff(c_17319, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16648, c_16645, c_16648, c_17303])).
% 9.35/3.23  tff(c_17322, plain, (![D_4675, C_4676]: (D_4675='#skF_3' | k2_zfmisc_1(C_4676, D_4675)!='#skF_7')), inference(splitRight, [status(thm)], [c_17015])).
% 9.35/3.23  tff(c_17325, plain, ('#skF_7'='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_16628, c_17322])).
% 9.35/3.23  tff(c_17338, plain, $false, inference(negUnitSimplification, [status(thm)], [c_13499, c_17325])).
% 9.35/3.23  tff(c_17423, plain, (![D_4685, C_4686]: (D_4685='#skF_4' | k2_zfmisc_1(C_4686, D_4685)!='#skF_7')), inference(splitRight, [status(thm)], [c_16968])).
% 9.35/3.23  tff(c_17426, plain, ('#skF_7'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_16628, c_17423])).
% 9.35/3.23  tff(c_17439, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16646, c_17426])).
% 9.35/3.23  tff(c_17440, plain, (k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_16621])).
% 9.35/3.23  tff(c_17463, plain, (![C_3742]: (C_3742='#skF_2' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_17440, c_13864])).
% 9.35/3.23  tff(c_17496, plain, (![C_4687]: (C_4687='#skF_2')), inference(negUnitSimplification, [status(thm)], [c_32, c_30, c_17463])).
% 9.35/3.23  tff(c_17522, plain, (k1_xboole_0='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_17496, c_17440])).
% 9.35/3.23  tff(c_17659, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_17522])).
% 9.35/3.23  tff(c_17662, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_14032])).
% 9.35/3.23  tff(c_17660, plain, (![C_14]: (k1_xboole_0=C_14)), inference(splitRight, [status(thm)], [c_14032])).
% 9.35/3.23  tff(c_17728, plain, (![C_5157]: (C_5157='#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_17662, c_17660])).
% 9.35/3.23  tff(c_17801, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_17728, c_30])).
% 9.35/3.23  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.35/3.23  
% 9.35/3.23  Inference rules
% 9.35/3.23  ----------------------
% 9.35/3.23  #Ref     : 50
% 9.35/3.23  #Sup     : 4698
% 9.35/3.23  #Fact    : 0
% 9.35/3.23  #Define  : 0
% 9.35/3.23  #Split   : 36
% 9.35/3.23  #Chain   : 0
% 9.35/3.23  #Close   : 0
% 9.35/3.23  
% 9.35/3.23  Ordering : KBO
% 9.35/3.23  
% 9.76/3.23  Simplification rules
% 9.76/3.23  ----------------------
% 9.76/3.23  #Subsume      : 1006
% 9.76/3.23  #Demod        : 3195
% 9.76/3.23  #Tautology    : 1948
% 9.76/3.23  #SimpNegUnit  : 257
% 9.76/3.23  #BackRed      : 651
% 9.76/3.23  
% 9.76/3.23  #Partial instantiations: 1852
% 9.76/3.23  #Strategies tried      : 1
% 9.76/3.23  
% 9.76/3.23  Timing (in seconds)
% 9.76/3.23  ----------------------
% 9.76/3.23  Preprocessing        : 0.29
% 9.76/3.23  Parsing              : 0.15
% 9.76/3.23  CNF conversion       : 0.02
% 9.76/3.23  Main loop            : 2.09
% 9.76/3.23  Inferencing          : 0.69
% 9.76/3.23  Reduction            : 0.64
% 9.76/3.23  Demodulation         : 0.45
% 9.76/3.23  BG Simplification    : 0.07
% 9.76/3.23  Subsumption          : 0.55
% 9.76/3.23  Abstraction          : 0.11
% 9.76/3.23  MUC search           : 0.00
% 9.76/3.23  Cooper               : 0.00
% 9.76/3.23  Total                : 2.52
% 9.76/3.23  Index Insertion      : 0.00
% 9.76/3.23  Index Deletion       : 0.00
% 9.76/3.23  Index Matching       : 0.00
% 9.76/3.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
