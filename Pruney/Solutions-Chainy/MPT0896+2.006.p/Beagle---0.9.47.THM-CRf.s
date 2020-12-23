%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:46 EST 2020

% Result     : Theorem 8.64s
% Output     : CNFRefutation 9.28s
% Verified   : 
% Statistics : Number of formulae       :  358 (53995 expanded)
%              Number of leaves         :   22 (17176 expanded)
%              Depth                    :   34
%              Number of atoms          :  630 (115967 expanded)
%              Number of equality atoms :  608 (115945 expanded)
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

tff(f_90,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_mcart_1)).

tff(f_33,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B,C,D] : k4_zfmisc_1(A,B,C,D) = k2_zfmisc_1(k3_zfmisc_1(A,B,C),D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_71,axiom,(
    ! [A,B,C,D,E,F] :
      ( k3_zfmisc_1(A,B,C) = k3_zfmisc_1(D,E,F)
     => ( k3_zfmisc_1(A,B,C) = k1_xboole_0
        | ( A = D
          & B = E
          & C = F ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_mcart_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0 )
    <=> k3_zfmisc_1(A,B,C) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_mcart_1)).

tff(f_61,axiom,(
    ! [A,B,C,D,E,F] :
      ( k3_zfmisc_1(A,B,C) = k3_zfmisc_1(D,E,F)
     => ( A = k1_xboole_0
        | B = k1_xboole_0
        | C = k1_xboole_0
        | ( A = D
          & B = E
          & C = F ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_mcart_1)).

tff(c_40,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_38,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_36,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_34,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_32,plain,
    ( '#skF_8' != '#skF_4'
    | '#skF_7' != '#skF_3'
    | '#skF_6' != '#skF_2'
    | '#skF_5' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_110,plain,(
    '#skF_5' != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_8,plain,(
    ! [A_3,B_4,C_5] : k2_zfmisc_1(k2_zfmisc_1(A_3,B_4),C_5) = k3_zfmisc_1(A_3,B_4,C_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [A_6,B_7,C_8,D_9] : k2_zfmisc_1(k3_zfmisc_1(A_6,B_7,C_8),D_9) = k4_zfmisc_1(A_6,B_7,C_8,D_9) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_122,plain,(
    ! [A_35,B_36,C_37] : k2_zfmisc_1(k2_zfmisc_1(A_35,B_36),C_37) = k3_zfmisc_1(A_35,B_36,C_37) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_138,plain,(
    ! [A_3,B_4,C_5,C_37] : k3_zfmisc_1(k2_zfmisc_1(A_3,B_4),C_5,C_37) = k2_zfmisc_1(k3_zfmisc_1(A_3,B_4,C_5),C_37) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_122])).

tff(c_332,plain,(
    ! [A_3,B_4,C_5,C_37] : k3_zfmisc_1(k2_zfmisc_1(A_3,B_4),C_5,C_37) = k4_zfmisc_1(A_3,B_4,C_5,C_37) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_138])).

tff(c_42,plain,(
    k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8') = k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_178,plain,(
    ! [A_41,B_42,C_43,D_44] : k2_zfmisc_1(k3_zfmisc_1(A_41,B_42,C_43),D_44) = k4_zfmisc_1(A_41,B_42,C_43,D_44) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( k1_xboole_0 = B_2
      | k1_xboole_0 = A_1
      | k2_zfmisc_1(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_427,plain,(
    ! [D_76,A_77,B_78,C_79] :
      ( k1_xboole_0 = D_76
      | k3_zfmisc_1(A_77,B_78,C_79) = k1_xboole_0
      | k4_zfmisc_1(A_77,B_78,C_79,D_76) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_178,c_2])).

tff(c_442,plain,
    ( k1_xboole_0 = '#skF_8'
    | k3_zfmisc_1('#skF_5','#skF_6','#skF_7') = k1_xboole_0
    | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_427])).

tff(c_451,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_442])).

tff(c_398,plain,(
    ! [C_70,F_74,B_72,D_75,A_73,E_71] :
      ( E_71 = B_72
      | k3_zfmisc_1(A_73,B_72,C_70) = k1_xboole_0
      | k3_zfmisc_1(D_75,E_71,F_74) != k3_zfmisc_1(A_73,B_72,C_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_404,plain,(
    ! [A_3,F_74,C_37,D_75,C_5,E_71,B_4] :
      ( E_71 = C_5
      | k3_zfmisc_1(k2_zfmisc_1(A_3,B_4),C_5,C_37) = k1_xboole_0
      | k4_zfmisc_1(A_3,B_4,C_5,C_37) != k3_zfmisc_1(D_75,E_71,F_74) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_332,c_398])).

tff(c_965,plain,(
    ! [B_150,C_148,D_149,E_144,F_145,A_147,C_146] :
      ( E_144 = C_148
      | k4_zfmisc_1(A_147,B_150,C_148,C_146) = k1_xboole_0
      | k4_zfmisc_1(A_147,B_150,C_148,C_146) != k3_zfmisc_1(D_149,E_144,F_145) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_332,c_404])).

tff(c_992,plain,(
    ! [E_144,D_149,F_145] :
      ( E_144 = '#skF_7'
      | k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8') = k1_xboole_0
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k3_zfmisc_1(D_149,E_144,F_145) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_965])).

tff(c_1008,plain,(
    ! [E_144,D_149,F_145] :
      ( E_144 = '#skF_7'
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = k1_xboole_0
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k3_zfmisc_1(D_149,E_144,F_145) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_992])).

tff(c_1010,plain,(
    ! [E_151,D_152,F_153] :
      ( E_151 = '#skF_7'
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k3_zfmisc_1(D_152,E_151,F_153) ) ),
    inference(negUnitSimplification,[status(thm)],[c_451,c_1008])).

tff(c_1016,plain,(
    ! [C_5,A_3,B_4,C_37] :
      ( C_5 = '#skF_7'
      | k4_zfmisc_1(A_3,B_4,C_5,C_37) != k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_332,c_1010])).

tff(c_1028,plain,(
    '#skF_7' = '#skF_3' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_1016])).

tff(c_1055,plain,(
    k4_zfmisc_1('#skF_5','#skF_6','#skF_3','#skF_8') = k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1028,c_42])).

tff(c_620,plain,(
    ! [D_99,E_95,C_94,B_96,F_98,A_97] :
      ( F_98 = C_94
      | k3_zfmisc_1(A_97,B_96,C_94) = k1_xboole_0
      | k3_zfmisc_1(D_99,E_95,F_98) != k3_zfmisc_1(A_97,B_96,C_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_632,plain,(
    ! [A_3,D_99,E_95,C_37,C_5,F_98,B_4] :
      ( F_98 = C_37
      | k3_zfmisc_1(k2_zfmisc_1(A_3,B_4),C_5,C_37) = k1_xboole_0
      | k4_zfmisc_1(A_3,B_4,C_5,C_37) != k3_zfmisc_1(D_99,E_95,F_98) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_332,c_620])).

tff(c_1301,plain,(
    ! [A_195,B_199,C_194,C_198,E_196,F_193,D_197] :
      ( F_193 = C_194
      | k4_zfmisc_1(A_195,B_199,C_198,C_194) = k1_xboole_0
      | k4_zfmisc_1(A_195,B_199,C_198,C_194) != k3_zfmisc_1(D_197,E_196,F_193) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_332,c_632])).

tff(c_1304,plain,(
    ! [F_193,D_197,E_196] :
      ( F_193 = '#skF_8'
      | k4_zfmisc_1('#skF_5','#skF_6','#skF_3','#skF_8') = k1_xboole_0
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k3_zfmisc_1(D_197,E_196,F_193) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1055,c_1301])).

tff(c_1338,plain,(
    ! [F_193,D_197,E_196] :
      ( F_193 = '#skF_8'
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = k1_xboole_0
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k3_zfmisc_1(D_197,E_196,F_193) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1055,c_1304])).

tff(c_1347,plain,(
    ! [F_200,D_201,E_202] :
      ( F_200 = '#skF_8'
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k3_zfmisc_1(D_201,E_202,F_200) ) ),
    inference(negUnitSimplification,[status(thm)],[c_451,c_1338])).

tff(c_1353,plain,(
    ! [C_37,A_3,B_4,C_5] :
      ( C_37 = '#skF_8'
      | k4_zfmisc_1(A_3,B_4,C_5,C_37) != k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_332,c_1347])).

tff(c_1365,plain,(
    '#skF_8' = '#skF_4' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_1353])).

tff(c_1392,plain,(
    k4_zfmisc_1('#skF_5','#skF_6','#skF_3','#skF_4') = k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1365,c_1055])).

tff(c_333,plain,(
    ! [A_66,B_67,C_68,C_69] : k3_zfmisc_1(k2_zfmisc_1(A_66,B_67),C_68,C_69) = k4_zfmisc_1(A_66,B_67,C_68,C_69) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_138])).

tff(c_30,plain,(
    ! [A_19,C_21,D_22,B_20,F_24,E_23] :
      ( D_22 = A_19
      | k3_zfmisc_1(A_19,B_20,C_21) = k1_xboole_0
      | k3_zfmisc_1(D_22,E_23,F_24) != k3_zfmisc_1(A_19,B_20,C_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_345,plain,(
    ! [B_67,A_66,C_68,D_22,C_69,F_24,E_23] :
      ( k2_zfmisc_1(A_66,B_67) = D_22
      | k3_zfmisc_1(k2_zfmisc_1(A_66,B_67),C_68,C_69) = k1_xboole_0
      | k4_zfmisc_1(A_66,B_67,C_68,C_69) != k3_zfmisc_1(D_22,E_23,F_24) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_333,c_30])).

tff(c_3168,plain,(
    ! [D_376,C_375,C_378,A_373,E_372,B_377,F_374] :
      ( k2_zfmisc_1(A_373,B_377) = D_376
      | k4_zfmisc_1(A_373,B_377,C_378,C_375) = k1_xboole_0
      | k4_zfmisc_1(A_373,B_377,C_378,C_375) != k3_zfmisc_1(D_376,E_372,F_374) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_332,c_345])).

tff(c_3171,plain,(
    ! [D_376,E_372,F_374] :
      ( k2_zfmisc_1('#skF_5','#skF_6') = D_376
      | k4_zfmisc_1('#skF_5','#skF_6','#skF_3','#skF_4') = k1_xboole_0
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k3_zfmisc_1(D_376,E_372,F_374) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1392,c_3168])).

tff(c_3205,plain,(
    ! [D_376,E_372,F_374] :
      ( k2_zfmisc_1('#skF_5','#skF_6') = D_376
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = k1_xboole_0
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k3_zfmisc_1(D_376,E_372,F_374) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1392,c_3171])).

tff(c_3213,plain,(
    ! [D_379,E_380,F_381] :
      ( k2_zfmisc_1('#skF_5','#skF_6') = D_379
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k3_zfmisc_1(D_379,E_380,F_381) ) ),
    inference(negUnitSimplification,[status(thm)],[c_451,c_3205])).

tff(c_3219,plain,(
    ! [A_3,B_4,C_5,C_37] :
      ( k2_zfmisc_1(A_3,B_4) = k2_zfmisc_1('#skF_5','#skF_6')
      | k4_zfmisc_1(A_3,B_4,C_5,C_37) != k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_332,c_3213])).

tff(c_3231,plain,(
    k2_zfmisc_1('#skF_5','#skF_6') = k2_zfmisc_1('#skF_1','#skF_2') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_3219])).

tff(c_3318,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k2_zfmisc_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_3231,c_2])).

tff(c_3460,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_3318])).

tff(c_3315,plain,(
    ! [C_5] : k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),C_5) = k3_zfmisc_1('#skF_5','#skF_6',C_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_3231,c_8])).

tff(c_3326,plain,(
    ! [C_393] : k3_zfmisc_1('#skF_5','#skF_6',C_393) = k3_zfmisc_1('#skF_1','#skF_2',C_393) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_3315])).

tff(c_12,plain,(
    ! [A_10,B_11,C_12] :
      ( k3_zfmisc_1(A_10,B_11,C_12) != k1_xboole_0
      | k1_xboole_0 = C_12
      | k1_xboole_0 = B_11
      | k1_xboole_0 = A_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_3431,plain,(
    ! [C_393] :
      ( k3_zfmisc_1('#skF_1','#skF_2',C_393) != k1_xboole_0
      | k1_xboole_0 = C_393
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_5' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3326,c_12])).

tff(c_3598,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_3431])).

tff(c_3601,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3598,c_3460])).

tff(c_6,plain,(
    ! [B_2] : k2_zfmisc_1(k1_xboole_0,B_2) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_3642,plain,(
    ! [B_2] : k2_zfmisc_1('#skF_5',B_2) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3598,c_3598,c_6])).

tff(c_3723,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3642,c_3231])).

tff(c_3749,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3601,c_3723])).

tff(c_3751,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_3431])).

tff(c_28,plain,(
    ! [A_19,C_21,D_22,B_20,F_24,E_23] :
      ( E_23 = B_20
      | k3_zfmisc_1(A_19,B_20,C_21) = k1_xboole_0
      | k3_zfmisc_1(D_22,E_23,F_24) != k3_zfmisc_1(A_19,B_20,C_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_3413,plain,(
    ! [B_20,A_19,C_21,C_393] :
      ( B_20 = '#skF_6'
      | k3_zfmisc_1(A_19,B_20,C_21) = k1_xboole_0
      | k3_zfmisc_1(A_19,B_20,C_21) != k3_zfmisc_1('#skF_1','#skF_2',C_393) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3326,c_28])).

tff(c_3987,plain,(
    ! [C_393] :
      ( '#skF_6' = '#skF_2'
      | k3_zfmisc_1('#skF_1','#skF_2',C_393) = k1_xboole_0 ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_3413])).

tff(c_4018,plain,(
    '#skF_6' = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_3987])).

tff(c_3323,plain,(
    ! [C_5] : k3_zfmisc_1('#skF_5','#skF_6',C_5) = k3_zfmisc_1('#skF_1','#skF_2',C_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_3315])).

tff(c_4093,plain,(
    ! [C_442] : k3_zfmisc_1('#skF_5','#skF_2',C_442) = k3_zfmisc_1('#skF_1','#skF_2',C_442) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4018,c_3323])).

tff(c_24,plain,(
    ! [E_17,F_18,A_13,B_14,C_15,D_16] :
      ( D_16 = A_13
      | k1_xboole_0 = C_15
      | k1_xboole_0 = B_14
      | k1_xboole_0 = A_13
      | k3_zfmisc_1(D_16,E_17,F_18) != k3_zfmisc_1(A_13,B_14,C_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_4171,plain,(
    ! [D_16,C_442,E_17,F_18] :
      ( D_16 = '#skF_5'
      | k1_xboole_0 = C_442
      | k1_xboole_0 = '#skF_2'
      | k1_xboole_0 = '#skF_5'
      | k3_zfmisc_1(D_16,E_17,F_18) != k3_zfmisc_1('#skF_1','#skF_2',C_442) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4093,c_24])).

tff(c_4232,plain,(
    ! [D_16,C_442,E_17,F_18] :
      ( D_16 = '#skF_5'
      | k1_xboole_0 = C_442
      | k3_zfmisc_1(D_16,E_17,F_18) != k3_zfmisc_1('#skF_1','#skF_2',C_442) ) ),
    inference(negUnitSimplification,[status(thm)],[c_3751,c_38,c_4171])).

tff(c_4435,plain,(
    ! [C_442] :
      ( '#skF_5' = '#skF_1'
      | k1_xboole_0 = C_442 ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_4232])).

tff(c_4463,plain,(
    ! [C_457] : k1_xboole_0 = C_457 ),
    inference(negUnitSimplification,[status(thm)],[c_110,c_4435])).

tff(c_4023,plain,(
    k2_zfmisc_1('#skF_5','#skF_2') = k2_zfmisc_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4018,c_3231])).

tff(c_4493,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4463,c_4023])).

tff(c_4590,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3460,c_4493])).

tff(c_4591,plain,(
    ! [C_393] : k3_zfmisc_1('#skF_1','#skF_2',C_393) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_3987])).

tff(c_452,plain,(
    ! [C_81,B_83,C_84,A_80,D_82] : k3_zfmisc_1(k3_zfmisc_1(A_80,B_83,C_81),D_82,C_84) = k2_zfmisc_1(k4_zfmisc_1(A_80,B_83,C_81,D_82),C_84) ),
    inference(superposition,[status(thm),theory(equality)],[c_178,c_8])).

tff(c_479,plain,(
    ! [C_81,B_83,C_84,A_80,D_82] :
      ( k2_zfmisc_1(k4_zfmisc_1(A_80,B_83,C_81,D_82),C_84) != k1_xboole_0
      | k1_xboole_0 = C_84
      | k1_xboole_0 = D_82
      | k3_zfmisc_1(A_80,B_83,C_81) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_452,c_12])).

tff(c_1406,plain,(
    ! [C_84] :
      ( k2_zfmisc_1(k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4'),C_84) != k1_xboole_0
      | k1_xboole_0 = C_84
      | k1_xboole_0 = '#skF_4'
      | k3_zfmisc_1('#skF_5','#skF_6','#skF_3') = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1392,c_479])).

tff(c_1435,plain,(
    ! [C_84] :
      ( k2_zfmisc_1(k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4'),C_84) != k1_xboole_0
      | k1_xboole_0 = C_84
      | k3_zfmisc_1('#skF_5','#skF_6','#skF_3') = k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_1406])).

tff(c_1560,plain,(
    k3_zfmisc_1('#skF_5','#skF_6','#skF_3') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_1435])).

tff(c_1612,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_1560,c_12])).

tff(c_1629,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_1612])).

tff(c_1651,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_1629])).

tff(c_1667,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1651,c_451])).

tff(c_18,plain,(
    ! [B_11,C_12] : k3_zfmisc_1(k1_xboole_0,B_11,C_12) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_197,plain,(
    ! [B_11,C_12,D_44] : k4_zfmisc_1(k1_xboole_0,B_11,C_12,D_44) = k2_zfmisc_1(k1_xboole_0,D_44) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_178])).

tff(c_210,plain,(
    ! [B_11,C_12,D_44] : k4_zfmisc_1(k1_xboole_0,B_11,C_12,D_44) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_197])).

tff(c_1672,plain,(
    ! [B_11,C_12,D_44] : k4_zfmisc_1('#skF_5',B_11,C_12,D_44) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1651,c_1651,c_210])).

tff(c_2054,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1672,c_1392])).

tff(c_2238,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1667,c_2054])).

tff(c_2239,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_1629])).

tff(c_2272,plain,(
    ! [B_2] : k2_zfmisc_1('#skF_6',B_2) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2239,c_2239,c_6])).

tff(c_1609,plain,(
    ! [D_9] : k4_zfmisc_1('#skF_5','#skF_6','#skF_3',D_9) = k2_zfmisc_1(k1_xboole_0,D_9) ),
    inference(superposition,[status(thm),theory(equality)],[c_1560,c_10])).

tff(c_1626,plain,(
    ! [D_9] : k4_zfmisc_1('#skF_5','#skF_6','#skF_3',D_9) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1609])).

tff(c_2621,plain,(
    ! [D_9] : k4_zfmisc_1('#skF_5','#skF_6','#skF_3',D_9) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2239,c_1626])).

tff(c_2622,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2621,c_1392])).

tff(c_184,plain,(
    ! [D_44,C_43,A_41,B_42,C_5] : k3_zfmisc_1(k3_zfmisc_1(A_41,B_42,C_43),D_44,C_5) = k2_zfmisc_1(k4_zfmisc_1(A_41,B_42,C_43,D_44),C_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_178,c_8])).

tff(c_1013,plain,(
    ! [D_44,C_43,A_41,B_42,C_5] :
      ( D_44 = '#skF_7'
      | k2_zfmisc_1(k4_zfmisc_1(A_41,B_42,C_43,D_44),C_5) != k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_184,c_1010])).

tff(c_1128,plain,(
    ! [C_169,C_166,A_165,D_167,B_168] :
      ( D_167 = '#skF_3'
      | k2_zfmisc_1(k4_zfmisc_1(A_165,B_168,C_166,D_167),C_169) != k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1028,c_1013])).

tff(c_1131,plain,(
    ! [C_169] :
      ( '#skF_3' = '#skF_8'
      | k2_zfmisc_1(k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4'),C_169) != k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1055,c_1128])).

tff(c_1201,plain,(
    ! [C_169] : k2_zfmisc_1(k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4'),C_169) != k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1131])).

tff(c_2723,plain,(
    ! [C_169] : k2_zfmisc_1('#skF_6',C_169) != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2622,c_2622,c_1201])).

tff(c_2729,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2272,c_2723])).

tff(c_2731,plain,(
    k3_zfmisc_1('#skF_5','#skF_6','#skF_3') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1435])).

tff(c_3325,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3323,c_2731])).

tff(c_4652,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4591,c_3325])).

tff(c_4653,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_3318])).

tff(c_4655,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_4653])).

tff(c_16,plain,(
    ! [A_10,C_12] : k3_zfmisc_1(A_10,k1_xboole_0,C_12) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_4694,plain,(
    ! [A_10,C_12] : k3_zfmisc_1(A_10,'#skF_6',C_12) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4655,c_4655,c_16])).

tff(c_4815,plain,(
    ! [C_5] : k3_zfmisc_1('#skF_1','#skF_2',C_5) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4694,c_3323])).

tff(c_4657,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4655,c_3325])).

tff(c_4998,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4815,c_4657])).

tff(c_4999,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_4653])).

tff(c_5038,plain,(
    ! [B_11,C_12] : k3_zfmisc_1('#skF_5',B_11,C_12) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4999,c_4999,c_18])).

tff(c_5190,plain,(
    ! [C_5] : k3_zfmisc_1('#skF_1','#skF_2',C_5) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5038,c_3323])).

tff(c_5002,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4999,c_3325])).

tff(c_5282,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5190,c_5002])).

tff(c_5283,plain,(
    '#skF_3' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_1131])).

tff(c_5290,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_8','#skF_4') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_5283,c_451])).

tff(c_5287,plain,(
    k4_zfmisc_1('#skF_5','#skF_6','#skF_8','#skF_8') = k4_zfmisc_1('#skF_1','#skF_2','#skF_8','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5283,c_5283,c_1055])).

tff(c_652,plain,(
    ! [A_3,D_99,E_95,C_37,C_5,F_98,B_4] :
      ( F_98 = C_37
      | k4_zfmisc_1(A_3,B_4,C_5,C_37) = k1_xboole_0
      | k4_zfmisc_1(A_3,B_4,C_5,C_37) != k3_zfmisc_1(D_99,E_95,F_98) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_332,c_632])).

tff(c_5343,plain,(
    ! [F_98,D_99,E_95] :
      ( F_98 = '#skF_8'
      | k4_zfmisc_1('#skF_5','#skF_6','#skF_8','#skF_8') = k1_xboole_0
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_8','#skF_4') != k3_zfmisc_1(D_99,E_95,F_98) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5287,c_652])).

tff(c_5364,plain,(
    ! [F_98,D_99,E_95] :
      ( F_98 = '#skF_8'
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_8','#skF_4') = k1_xboole_0
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_8','#skF_4') != k3_zfmisc_1(D_99,E_95,F_98) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5287,c_5343])).

tff(c_5388,plain,(
    ! [F_807,D_808,E_809] :
      ( F_807 = '#skF_8'
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_8','#skF_4') != k3_zfmisc_1(D_808,E_809,F_807) ) ),
    inference(negUnitSimplification,[status(thm)],[c_5290,c_5364])).

tff(c_5394,plain,(
    ! [C_37,A_3,B_4,C_5] :
      ( C_37 = '#skF_8'
      | k4_zfmisc_1(A_3,B_4,C_5,C_37) != k4_zfmisc_1('#skF_1','#skF_2','#skF_8','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_332,c_5388])).

tff(c_5475,plain,(
    '#skF_8' = '#skF_4' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_5394])).

tff(c_5505,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_4','#skF_4') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_5475,c_5290])).

tff(c_5504,plain,(
    k4_zfmisc_1('#skF_5','#skF_6','#skF_4','#skF_4') = k4_zfmisc_1('#skF_1','#skF_2','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5475,c_5475,c_5475,c_5287])).

tff(c_7708,plain,(
    ! [D_1063,A_1060,C_1062,B_1064,C_1065,F_1061,E_1059] :
      ( k2_zfmisc_1(A_1060,B_1064) = D_1063
      | k4_zfmisc_1(A_1060,B_1064,C_1065,C_1062) = k1_xboole_0
      | k4_zfmisc_1(A_1060,B_1064,C_1065,C_1062) != k3_zfmisc_1(D_1063,E_1059,F_1061) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_332,c_345])).

tff(c_7711,plain,(
    ! [D_1063,E_1059,F_1061] :
      ( k2_zfmisc_1('#skF_5','#skF_6') = D_1063
      | k4_zfmisc_1('#skF_5','#skF_6','#skF_4','#skF_4') = k1_xboole_0
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_4','#skF_4') != k3_zfmisc_1(D_1063,E_1059,F_1061) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5504,c_7708])).

tff(c_7745,plain,(
    ! [D_1063,E_1059,F_1061] :
      ( k2_zfmisc_1('#skF_5','#skF_6') = D_1063
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_4','#skF_4') = k1_xboole_0
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_4','#skF_4') != k3_zfmisc_1(D_1063,E_1059,F_1061) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5504,c_7711])).

tff(c_7753,plain,(
    ! [D_1066,E_1067,F_1068] :
      ( k2_zfmisc_1('#skF_5','#skF_6') = D_1066
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_4','#skF_4') != k3_zfmisc_1(D_1066,E_1067,F_1068) ) ),
    inference(negUnitSimplification,[status(thm)],[c_5505,c_7745])).

tff(c_7759,plain,(
    ! [A_3,B_4,C_5,C_37] :
      ( k2_zfmisc_1(A_3,B_4) = k2_zfmisc_1('#skF_5','#skF_6')
      | k4_zfmisc_1(A_3,B_4,C_5,C_37) != k4_zfmisc_1('#skF_1','#skF_2','#skF_4','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_332,c_7753])).

tff(c_7771,plain,(
    k2_zfmisc_1('#skF_5','#skF_6') = k2_zfmisc_1('#skF_1','#skF_2') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_7759])).

tff(c_7812,plain,(
    ! [C_5] : k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),C_5) = k3_zfmisc_1('#skF_5','#skF_6',C_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_7771,c_8])).

tff(c_7823,plain,(
    ! [C_1073] : k3_zfmisc_1('#skF_5','#skF_6',C_1073) = k3_zfmisc_1('#skF_1','#skF_2',C_1073) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_7812])).

tff(c_7919,plain,(
    ! [A_19,B_20,C_21,C_1073] :
      ( A_19 = '#skF_5'
      | k3_zfmisc_1(A_19,B_20,C_21) = k1_xboole_0
      | k3_zfmisc_1(A_19,B_20,C_21) != k3_zfmisc_1('#skF_1','#skF_2',C_1073) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7823,c_30])).

tff(c_8526,plain,(
    ! [C_1073] :
      ( '#skF_5' = '#skF_1'
      | k3_zfmisc_1('#skF_1','#skF_2',C_1073) = k1_xboole_0 ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_7919])).

tff(c_8527,plain,(
    ! [C_1073] : k3_zfmisc_1('#skF_1','#skF_2',C_1073) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_110,c_8526])).

tff(c_7820,plain,(
    ! [C_5] : k3_zfmisc_1('#skF_5','#skF_6',C_5) = k3_zfmisc_1('#skF_1','#skF_2',C_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_7812])).

tff(c_5291,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5283,c_36])).

tff(c_5433,plain,(
    ! [B_818,C_817,D_815,A_814,C_816] :
      ( k2_zfmisc_1(k4_zfmisc_1(A_814,B_818,C_816,D_815),C_817) != k1_xboole_0
      | k1_xboole_0 = C_817
      | k1_xboole_0 = D_815
      | k3_zfmisc_1(A_814,B_818,C_816) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_452,c_12])).

tff(c_5436,plain,(
    ! [C_817] :
      ( k2_zfmisc_1(k4_zfmisc_1('#skF_1','#skF_2','#skF_8','#skF_4'),C_817) != k1_xboole_0
      | k1_xboole_0 = C_817
      | k1_xboole_0 = '#skF_8'
      | k3_zfmisc_1('#skF_5','#skF_6','#skF_8') = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5287,c_5433])).

tff(c_5459,plain,(
    ! [C_817] :
      ( k2_zfmisc_1(k4_zfmisc_1('#skF_1','#skF_2','#skF_8','#skF_4'),C_817) != k1_xboole_0
      | k1_xboole_0 = C_817
      | k3_zfmisc_1('#skF_5','#skF_6','#skF_8') = k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_5291,c_5436])).

tff(c_5517,plain,(
    ! [C_817] :
      ( k2_zfmisc_1(k4_zfmisc_1('#skF_1','#skF_2','#skF_4','#skF_4'),C_817) != k1_xboole_0
      | k1_xboole_0 = C_817
      | k3_zfmisc_1('#skF_5','#skF_6','#skF_4') = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5475,c_5475,c_5459])).

tff(c_5518,plain,(
    k3_zfmisc_1('#skF_5','#skF_6','#skF_4') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_5517])).

tff(c_5574,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_5518,c_12])).

tff(c_5591,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_5574])).

tff(c_5613,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_5591])).

tff(c_5856,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_4','#skF_4') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5613,c_5505])).

tff(c_5631,plain,(
    ! [B_11,C_12,D_44] : k4_zfmisc_1('#skF_5',B_11,C_12,D_44) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5613,c_5613,c_210])).

tff(c_6245,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_4','#skF_4') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5631,c_5504])).

tff(c_6246,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5856,c_6245])).

tff(c_6247,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_5591])).

tff(c_6571,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_4','#skF_4') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6247,c_5505])).

tff(c_200,plain,(
    ! [A_10,C_12,D_44] : k4_zfmisc_1(A_10,k1_xboole_0,C_12,D_44) = k2_zfmisc_1(k1_xboole_0,D_44) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_178])).

tff(c_211,plain,(
    ! [A_10,C_12,D_44] : k4_zfmisc_1(A_10,k1_xboole_0,C_12,D_44) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_200])).

tff(c_6344,plain,(
    ! [A_10,C_12,D_44] : k4_zfmisc_1(A_10,'#skF_6',C_12,D_44) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6247,c_6247,c_211])).

tff(c_6957,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_4','#skF_4') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6344,c_5504])).

tff(c_6958,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6571,c_6957])).

tff(c_6960,plain,(
    k3_zfmisc_1('#skF_5','#skF_6','#skF_4') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_5517])).

tff(c_7822,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_4') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_7820,c_6960])).

tff(c_8565,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8527,c_7822])).

tff(c_8567,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_442])).

tff(c_187,plain,(
    ! [D_44,A_41,B_42,C_43] :
      ( k1_xboole_0 = D_44
      | k3_zfmisc_1(A_41,B_42,C_43) = k1_xboole_0
      | k4_zfmisc_1(A_41,B_42,C_43,D_44) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_178,c_2])).

tff(c_8572,plain,
    ( k1_xboole_0 = '#skF_4'
    | k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_8567,c_187])).

tff(c_8577,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_8572])).

tff(c_8600,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_8577,c_12])).

tff(c_8612,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_38,c_36,c_8600])).

tff(c_8614,plain,(
    '#skF_5' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_8667,plain,(
    k4_zfmisc_1('#skF_1','#skF_6','#skF_7','#skF_8') = k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8614,c_42])).

tff(c_8688,plain,(
    ! [A_1130,B_1131,C_1132,D_1133] : k2_zfmisc_1(k3_zfmisc_1(A_1130,B_1131,C_1132),D_1133) = k4_zfmisc_1(A_1130,B_1131,C_1132,D_1133) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_8937,plain,(
    ! [D_1165,A_1166,B_1167,C_1168] :
      ( k1_xboole_0 = D_1165
      | k3_zfmisc_1(A_1166,B_1167,C_1168) = k1_xboole_0
      | k4_zfmisc_1(A_1166,B_1167,C_1168,D_1165) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8688,c_2])).

tff(c_8952,plain,
    ( k1_xboole_0 = '#skF_8'
    | k3_zfmisc_1('#skF_1','#skF_6','#skF_7') = k1_xboole_0
    | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_8667,c_8937])).

tff(c_8961,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_8952])).

tff(c_8613,plain,
    ( '#skF_6' != '#skF_2'
    | '#skF_7' != '#skF_3'
    | '#skF_8' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_8619,plain,(
    '#skF_8' != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_8613])).

tff(c_8631,plain,(
    ! [A_1124,B_1125,C_1126] : k2_zfmisc_1(k2_zfmisc_1(A_1124,B_1125),C_1126) = k3_zfmisc_1(A_1124,B_1125,C_1126) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_8634,plain,(
    ! [A_1124,B_1125,C_1126,C_5] : k3_zfmisc_1(k2_zfmisc_1(A_1124,B_1125),C_1126,C_5) = k2_zfmisc_1(k3_zfmisc_1(A_1124,B_1125,C_1126),C_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_8631,c_8])).

tff(c_8842,plain,(
    ! [A_1124,B_1125,C_1126,C_5] : k3_zfmisc_1(k2_zfmisc_1(A_1124,B_1125),C_1126,C_5) = k4_zfmisc_1(A_1124,B_1125,C_1126,C_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_8634])).

tff(c_9043,plain,(
    ! [D_1179,B_1176,F_1178,A_1177,E_1175,C_1174] :
      ( F_1178 = C_1174
      | k3_zfmisc_1(A_1177,B_1176,C_1174) = k1_xboole_0
      | k3_zfmisc_1(D_1179,E_1175,F_1178) != k3_zfmisc_1(A_1177,B_1176,C_1174) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_9348,plain,(
    ! [C_1216,B_1217,A_1214,C_1219,C_1218,A_1215,B_1213] :
      ( C_1219 = C_1216
      | k3_zfmisc_1(A_1215,B_1217,C_1216) = k1_xboole_0
      | k4_zfmisc_1(A_1214,B_1213,C_1218,C_1219) != k3_zfmisc_1(A_1215,B_1217,C_1216) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8842,c_9043])).

tff(c_9433,plain,(
    ! [C_1227,A_1228,B_1229] :
      ( C_1227 = '#skF_8'
      | k3_zfmisc_1(A_1228,B_1229,C_1227) = k1_xboole_0
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k3_zfmisc_1(A_1228,B_1229,C_1227) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8667,c_9348])).

tff(c_9439,plain,(
    ! [C_5,A_1124,B_1125,C_1126] :
      ( C_5 = '#skF_8'
      | k3_zfmisc_1(k2_zfmisc_1(A_1124,B_1125),C_1126,C_5) = k1_xboole_0
      | k4_zfmisc_1(A_1124,B_1125,C_1126,C_5) != k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8842,c_9433])).

tff(c_9450,plain,(
    ! [C_5,A_1124,B_1125,C_1126] :
      ( C_5 = '#skF_8'
      | k4_zfmisc_1(A_1124,B_1125,C_1126,C_5) = k1_xboole_0
      | k4_zfmisc_1(A_1124,B_1125,C_1126,C_5) != k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8842,c_9439])).

tff(c_9478,plain,
    ( '#skF_8' = '#skF_4'
    | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = k1_xboole_0 ),
    inference(reflexivity,[status(thm),theory(equality)],[c_9450])).

tff(c_9480,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8961,c_8619,c_9478])).

tff(c_9482,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_8952])).

tff(c_8697,plain,(
    ! [D_1133,A_1130,B_1131,C_1132] :
      ( k1_xboole_0 = D_1133
      | k3_zfmisc_1(A_1130,B_1131,C_1132) = k1_xboole_0
      | k4_zfmisc_1(A_1130,B_1131,C_1132,D_1133) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8688,c_2])).

tff(c_9487,plain,
    ( k1_xboole_0 = '#skF_4'
    | k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_9482,c_8697])).

tff(c_9492,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_9487])).

tff(c_9515,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_9492,c_12])).

tff(c_9527,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_38,c_36,c_9515])).

tff(c_9528,plain,
    ( '#skF_7' != '#skF_3'
    | '#skF_6' != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_8613])).

tff(c_9534,plain,(
    '#skF_6' != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_9528])).

tff(c_9546,plain,(
    ! [A_1235,B_1236,C_1237] : k2_zfmisc_1(k2_zfmisc_1(A_1235,B_1236),C_1237) = k3_zfmisc_1(A_1235,B_1236,C_1237) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_9549,plain,(
    ! [A_1235,B_1236,C_1237,C_5] : k3_zfmisc_1(k2_zfmisc_1(A_1235,B_1236),C_1237,C_5) = k2_zfmisc_1(k3_zfmisc_1(A_1235,B_1236,C_1237),C_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_9546,c_8])).

tff(c_9757,plain,(
    ! [A_1235,B_1236,C_1237,C_5] : k3_zfmisc_1(k2_zfmisc_1(A_1235,B_1236),C_1237,C_5) = k4_zfmisc_1(A_1235,B_1236,C_1237,C_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_9549])).

tff(c_9529,plain,(
    '#skF_8' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_8613])).

tff(c_9582,plain,(
    k4_zfmisc_1('#skF_1','#skF_6','#skF_7','#skF_4') = k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9529,c_8614,c_42])).

tff(c_9603,plain,(
    ! [A_1241,B_1242,C_1243,D_1244] : k2_zfmisc_1(k3_zfmisc_1(A_1241,B_1242,C_1243),D_1244) = k4_zfmisc_1(A_1241,B_1242,C_1243,D_1244) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_9852,plain,(
    ! [D_1276,A_1277,B_1278,C_1279] :
      ( k1_xboole_0 = D_1276
      | k3_zfmisc_1(A_1277,B_1278,C_1279) = k1_xboole_0
      | k4_zfmisc_1(A_1277,B_1278,C_1279,D_1276) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9603,c_2])).

tff(c_9867,plain,
    ( k1_xboole_0 = '#skF_4'
    | k3_zfmisc_1('#skF_1','#skF_6','#skF_7') = k1_xboole_0
    | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_9582,c_9852])).

tff(c_9876,plain,
    ( k3_zfmisc_1('#skF_1','#skF_6','#skF_7') = k1_xboole_0
    | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_9867])).

tff(c_9877,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_9876])).

tff(c_9823,plain,(
    ! [A_1273,B_1272,E_1271,D_1275,C_1270,F_1274] :
      ( E_1271 = B_1272
      | k3_zfmisc_1(A_1273,B_1272,C_1270) = k1_xboole_0
      | k3_zfmisc_1(D_1275,E_1271,F_1274) != k3_zfmisc_1(A_1273,B_1272,C_1270) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_9829,plain,(
    ! [A_1235,E_1271,B_1236,C_1237,C_5,D_1275,F_1274] :
      ( E_1271 = C_1237
      | k3_zfmisc_1(k2_zfmisc_1(A_1235,B_1236),C_1237,C_5) = k1_xboole_0
      | k4_zfmisc_1(A_1235,B_1236,C_1237,C_5) != k3_zfmisc_1(D_1275,E_1271,F_1274) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9757,c_9823])).

tff(c_11648,plain,(
    ! [A_1453,D_1452,C_1458,C_1456,E_1457,F_1455,B_1454] :
      ( E_1457 = C_1458
      | k4_zfmisc_1(A_1453,B_1454,C_1458,C_1456) = k1_xboole_0
      | k4_zfmisc_1(A_1453,B_1454,C_1458,C_1456) != k3_zfmisc_1(D_1452,E_1457,F_1455) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9757,c_9829])).

tff(c_11675,plain,(
    ! [E_1457,D_1452,F_1455] :
      ( E_1457 = '#skF_7'
      | k4_zfmisc_1('#skF_1','#skF_6','#skF_7','#skF_4') = k1_xboole_0
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k3_zfmisc_1(D_1452,E_1457,F_1455) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9582,c_11648])).

tff(c_11691,plain,(
    ! [E_1457,D_1452,F_1455] :
      ( E_1457 = '#skF_7'
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = k1_xboole_0
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k3_zfmisc_1(D_1452,E_1457,F_1455) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9582,c_11675])).

tff(c_11693,plain,(
    ! [E_1459,D_1460,F_1461] :
      ( E_1459 = '#skF_7'
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k3_zfmisc_1(D_1460,E_1459,F_1461) ) ),
    inference(negUnitSimplification,[status(thm)],[c_9877,c_11691])).

tff(c_11699,plain,(
    ! [C_1237,A_1235,B_1236,C_5] :
      ( C_1237 = '#skF_7'
      | k4_zfmisc_1(A_1235,B_1236,C_1237,C_5) != k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9757,c_11693])).

tff(c_11711,plain,(
    '#skF_7' = '#skF_3' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_11699])).

tff(c_11739,plain,(
    k4_zfmisc_1('#skF_1','#skF_6','#skF_3','#skF_4') = k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11711,c_9582])).

tff(c_9758,plain,(
    ! [A_1266,B_1267,C_1268,C_1269] : k3_zfmisc_1(k2_zfmisc_1(A_1266,B_1267),C_1268,C_1269) = k4_zfmisc_1(A_1266,B_1267,C_1268,C_1269) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_9549])).

tff(c_9770,plain,(
    ! [C_1268,B_1267,A_1266,C_1269,D_22,F_24,E_23] :
      ( k2_zfmisc_1(A_1266,B_1267) = D_22
      | k3_zfmisc_1(k2_zfmisc_1(A_1266,B_1267),C_1268,C_1269) = k1_xboole_0
      | k4_zfmisc_1(A_1266,B_1267,C_1268,C_1269) != k3_zfmisc_1(D_22,E_23,F_24) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9758,c_30])).

tff(c_12010,plain,(
    ! [D_1506,C_1505,F_1504,E_1501,A_1503,C_1502,B_1507] :
      ( k2_zfmisc_1(A_1503,B_1507) = D_1506
      | k4_zfmisc_1(A_1503,B_1507,C_1502,C_1505) = k1_xboole_0
      | k4_zfmisc_1(A_1503,B_1507,C_1502,C_1505) != k3_zfmisc_1(D_1506,E_1501,F_1504) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9757,c_9770])).

tff(c_12013,plain,(
    ! [D_1506,E_1501,F_1504] :
      ( k2_zfmisc_1('#skF_1','#skF_6') = D_1506
      | k4_zfmisc_1('#skF_1','#skF_6','#skF_3','#skF_4') = k1_xboole_0
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k3_zfmisc_1(D_1506,E_1501,F_1504) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11739,c_12010])).

tff(c_12047,plain,(
    ! [D_1506,E_1501,F_1504] :
      ( k2_zfmisc_1('#skF_1','#skF_6') = D_1506
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = k1_xboole_0
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k3_zfmisc_1(D_1506,E_1501,F_1504) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11739,c_12013])).

tff(c_12055,plain,(
    ! [D_1508,E_1509,F_1510] :
      ( k2_zfmisc_1('#skF_1','#skF_6') = D_1508
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k3_zfmisc_1(D_1508,E_1509,F_1510) ) ),
    inference(negUnitSimplification,[status(thm)],[c_9877,c_12047])).

tff(c_12061,plain,(
    ! [A_1235,B_1236,C_1237,C_5] :
      ( k2_zfmisc_1(A_1235,B_1236) = k2_zfmisc_1('#skF_1','#skF_6')
      | k4_zfmisc_1(A_1235,B_1236,C_1237,C_5) != k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9757,c_12055])).

tff(c_12073,plain,(
    k2_zfmisc_1('#skF_1','#skF_6') = k2_zfmisc_1('#skF_1','#skF_2') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_12061])).

tff(c_12113,plain,(
    ! [C_5] : k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'),C_5) = k3_zfmisc_1('#skF_1','#skF_6',C_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_12073,c_8])).

tff(c_12126,plain,(
    ! [C_1515] : k3_zfmisc_1('#skF_1','#skF_6',C_1515) = k3_zfmisc_1('#skF_1','#skF_2',C_1515) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_12113])).

tff(c_12180,plain,(
    ! [D_16,C_1515,E_17,F_18] :
      ( D_16 = '#skF_1'
      | k1_xboole_0 = C_1515
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_1'
      | k3_zfmisc_1(D_16,E_17,F_18) != k3_zfmisc_1('#skF_1','#skF_2',C_1515) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12126,c_24])).

tff(c_12238,plain,(
    ! [D_16,C_1515,E_17,F_18] :
      ( D_16 = '#skF_1'
      | k1_xboole_0 = C_1515
      | k1_xboole_0 = '#skF_6'
      | k3_zfmisc_1(D_16,E_17,F_18) != k3_zfmisc_1('#skF_1','#skF_2',C_1515) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_12180])).

tff(c_12408,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_12238])).

tff(c_4,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12445,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12408,c_12408,c_4])).

tff(c_12455,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12445,c_12073])).

tff(c_12116,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_1'
    | k2_zfmisc_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_12073,c_2])).

tff(c_12122,plain,
    ( k1_xboole_0 = '#skF_6'
    | k2_zfmisc_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_12116])).

tff(c_12124,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_12122])).

tff(c_12413,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12408,c_12124])).

tff(c_12559,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12455,c_12413])).

tff(c_12561,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_12238])).

tff(c_22,plain,(
    ! [E_17,F_18,A_13,B_14,C_15,D_16] :
      ( E_17 = B_14
      | k1_xboole_0 = C_15
      | k1_xboole_0 = B_14
      | k1_xboole_0 = A_13
      | k3_zfmisc_1(D_16,E_17,F_18) != k3_zfmisc_1(A_13,B_14,C_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_12186,plain,(
    ! [E_17,C_1515,D_16,F_18] :
      ( E_17 = '#skF_6'
      | k1_xboole_0 = C_1515
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_1'
      | k3_zfmisc_1(D_16,E_17,F_18) != k3_zfmisc_1('#skF_1','#skF_2',C_1515) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12126,c_22])).

tff(c_12239,plain,(
    ! [E_17,C_1515,D_16,F_18] :
      ( E_17 = '#skF_6'
      | k1_xboole_0 = C_1515
      | k1_xboole_0 = '#skF_6'
      | k3_zfmisc_1(D_16,E_17,F_18) != k3_zfmisc_1('#skF_1','#skF_2',C_1515) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_12186])).

tff(c_12667,plain,(
    ! [E_17,C_1515,D_16,F_18] :
      ( E_17 = '#skF_6'
      | k1_xboole_0 = C_1515
      | k3_zfmisc_1(D_16,E_17,F_18) != k3_zfmisc_1('#skF_1','#skF_2',C_1515) ) ),
    inference(negUnitSimplification,[status(thm)],[c_12561,c_12239])).

tff(c_12670,plain,(
    ! [C_1515] :
      ( '#skF_6' = '#skF_2'
      | k1_xboole_0 = C_1515 ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_12667])).

tff(c_12698,plain,(
    ! [C_1550] : k1_xboole_0 = C_1550 ),
    inference(negUnitSimplification,[status(thm)],[c_9534,c_12670])).

tff(c_12121,plain,(
    ! [C_5] : k3_zfmisc_1('#skF_1','#skF_6',C_5) = k3_zfmisc_1('#skF_1','#skF_2',C_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_12113])).

tff(c_9878,plain,(
    ! [B_1282,A_1280,C_1281,D_1283,C_1284] : k3_zfmisc_1(k3_zfmisc_1(A_1280,B_1282,C_1281),D_1283,C_1284) = k2_zfmisc_1(k4_zfmisc_1(A_1280,B_1282,C_1281,D_1283),C_1284) ),
    inference(superposition,[status(thm),theory(equality)],[c_9603,c_8])).

tff(c_10489,plain,(
    ! [C_1363,D_1362,A_1361,C_1360,B_1364] :
      ( k2_zfmisc_1(k4_zfmisc_1(A_1361,B_1364,C_1363,D_1362),C_1360) != k1_xboole_0
      | k1_xboole_0 = C_1360
      | k1_xboole_0 = D_1362
      | k3_zfmisc_1(A_1361,B_1364,C_1363) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9878,c_12])).

tff(c_10510,plain,(
    ! [C_1360] :
      ( k2_zfmisc_1(k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4'),C_1360) != k1_xboole_0
      | k1_xboole_0 = C_1360
      | k1_xboole_0 = '#skF_4'
      | k3_zfmisc_1('#skF_1','#skF_6','#skF_7') = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9582,c_10489])).

tff(c_10526,plain,(
    ! [C_1360] :
      ( k2_zfmisc_1(k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4'),C_1360) != k1_xboole_0
      | k1_xboole_0 = C_1360
      | k3_zfmisc_1('#skF_1','#skF_6','#skF_7') = k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_10510])).

tff(c_10569,plain,(
    k3_zfmisc_1('#skF_1','#skF_6','#skF_7') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_10526])).

tff(c_10621,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_10569,c_12])).

tff(c_10636,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_10621])).

tff(c_10638,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_10636])).

tff(c_10652,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10638,c_9877])).

tff(c_10618,plain,(
    ! [D_9] : k4_zfmisc_1('#skF_1','#skF_6','#skF_7',D_9) = k2_zfmisc_1(k1_xboole_0,D_9) ),
    inference(superposition,[status(thm),theory(equality)],[c_10569,c_10])).

tff(c_10633,plain,(
    ! [D_9] : k4_zfmisc_1('#skF_1','#skF_6','#skF_7',D_9) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_10618])).

tff(c_10923,plain,(
    ! [D_9] : k4_zfmisc_1('#skF_1','#skF_6','#skF_7',D_9) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10638,c_10633])).

tff(c_10924,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10923,c_9582])).

tff(c_11191,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10652,c_10924])).

tff(c_11192,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_10636])).

tff(c_11495,plain,(
    ! [D_9] : k4_zfmisc_1('#skF_1','#skF_6','#skF_7',D_9) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11192,c_10633])).

tff(c_11496,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11495,c_9582])).

tff(c_11206,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11192,c_9877])).

tff(c_11598,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_11496,c_11206])).

tff(c_11600,plain,(
    k3_zfmisc_1('#skF_1','#skF_6','#skF_7') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_10526])).

tff(c_11738,plain,(
    k3_zfmisc_1('#skF_1','#skF_6','#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_11711,c_11600])).

tff(c_12125,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12121,c_11738])).

tff(c_12813,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_12698,c_12125])).

tff(c_12814,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_12122])).

tff(c_12846,plain,(
    ! [A_10,C_12] : k3_zfmisc_1(A_10,'#skF_6',C_12) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12814,c_12814,c_16])).

tff(c_12820,plain,(
    k3_zfmisc_1('#skF_1','#skF_6','#skF_3') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12814,c_11738])).

tff(c_12961,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12846,c_12820])).

tff(c_12962,plain,(
    k3_zfmisc_1('#skF_1','#skF_6','#skF_7') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_9876])).

tff(c_12985,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_12962,c_12])).

tff(c_12994,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_12985])).

tff(c_12996,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_12994])).

tff(c_13057,plain,(
    '#skF_6' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12996,c_40])).

tff(c_13056,plain,(
    '#skF_6' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12996,c_36])).

tff(c_13055,plain,(
    '#skF_6' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12996,c_34])).

tff(c_12963,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_9876])).

tff(c_13223,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12996,c_12963])).

tff(c_9555,plain,(
    ! [C_1237,A_1235,B_1236] :
      ( k1_xboole_0 = C_1237
      | k2_zfmisc_1(A_1235,B_1236) = k1_xboole_0
      | k3_zfmisc_1(A_1235,B_1236,C_1237) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9546,c_2])).

tff(c_9764,plain,(
    ! [C_1269,A_1266,B_1267,C_1268] :
      ( k1_xboole_0 = C_1269
      | k2_zfmisc_1(k2_zfmisc_1(A_1266,B_1267),C_1268) = k1_xboole_0
      | k4_zfmisc_1(A_1266,B_1267,C_1268,C_1269) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9758,c_9555])).

tff(c_9809,plain,(
    ! [C_1269,A_1266,B_1267,C_1268] :
      ( k1_xboole_0 = C_1269
      | k3_zfmisc_1(A_1266,B_1267,C_1268) = k1_xboole_0
      | k4_zfmisc_1(A_1266,B_1267,C_1268,C_1269) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_9764])).

tff(c_13533,plain,(
    ! [C_1880,A_1881,B_1882,C_1883] :
      ( C_1880 = '#skF_6'
      | k3_zfmisc_1(A_1881,B_1882,C_1883) = '#skF_6'
      | k4_zfmisc_1(A_1881,B_1882,C_1883,C_1880) != '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12996,c_12996,c_12996,c_9809])).

tff(c_13548,plain,
    ( '#skF_6' = '#skF_4'
    | k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_13223,c_13533])).

tff(c_13559,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_13055,c_13548])).

tff(c_13047,plain,(
    ! [A_10,B_11,C_12] :
      ( k3_zfmisc_1(A_10,B_11,C_12) != '#skF_6'
      | C_12 = '#skF_6'
      | B_11 = '#skF_6'
      | A_10 = '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12996,c_12996,c_12996,c_12996,c_12])).

tff(c_13569,plain,
    ( '#skF_6' = '#skF_3'
    | '#skF_6' = '#skF_2'
    | '#skF_6' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_13559,c_13047])).

tff(c_13600,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_13057,c_9534,c_13056,c_13569])).

tff(c_13601,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_12994])).

tff(c_13622,plain,(
    '#skF_7' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13601,c_40])).

tff(c_13619,plain,(
    '#skF_7' != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13601,c_38])).

tff(c_13621,plain,(
    '#skF_7' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13601,c_36])).

tff(c_13620,plain,(
    '#skF_7' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13601,c_34])).

tff(c_13719,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13601,c_12963])).

tff(c_14076,plain,(
    ! [C_1937,A_1938,B_1939,C_1940] :
      ( C_1937 = '#skF_7'
      | k3_zfmisc_1(A_1938,B_1939,C_1940) = '#skF_7'
      | k4_zfmisc_1(A_1938,B_1939,C_1940,C_1937) != '#skF_7' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13601,c_13601,c_13601,c_9809])).

tff(c_14091,plain,
    ( '#skF_7' = '#skF_4'
    | k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_13719,c_14076])).

tff(c_14102,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_13620,c_14091])).

tff(c_13612,plain,(
    ! [A_10,B_11,C_12] :
      ( k3_zfmisc_1(A_10,B_11,C_12) != '#skF_7'
      | C_12 = '#skF_7'
      | B_11 = '#skF_7'
      | A_10 = '#skF_7' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13601,c_13601,c_13601,c_13601,c_12])).

tff(c_14109,plain,
    ( '#skF_7' = '#skF_3'
    | '#skF_7' = '#skF_2'
    | '#skF_7' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_14102,c_13612])).

tff(c_14145,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_13622,c_13619,c_13621,c_14109])).

tff(c_14146,plain,(
    '#skF_7' != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_9528])).

tff(c_14163,plain,(
    ! [A_1943,B_1944,C_1945] : k2_zfmisc_1(k2_zfmisc_1(A_1943,B_1944),C_1945) = k3_zfmisc_1(A_1943,B_1944,C_1945) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_14179,plain,(
    ! [A_3,B_4,C_5,C_1945] : k3_zfmisc_1(k2_zfmisc_1(A_3,B_4),C_5,C_1945) = k2_zfmisc_1(k3_zfmisc_1(A_3,B_4,C_5),C_1945) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_14163])).

tff(c_14348,plain,(
    ! [A_3,B_4,C_5,C_1945] : k3_zfmisc_1(k2_zfmisc_1(A_3,B_4),C_5,C_1945) = k4_zfmisc_1(A_3,B_4,C_5,C_1945) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_14179])).

tff(c_14147,plain,(
    '#skF_6' = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_9528])).

tff(c_14199,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_7','#skF_4') = k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14147,c_8614,c_9529,c_42])).

tff(c_14204,plain,(
    ! [A_1946,B_1947,C_1948,D_1949] : k2_zfmisc_1(k3_zfmisc_1(A_1946,B_1947,C_1948),D_1949) = k4_zfmisc_1(A_1946,B_1947,C_1948,D_1949) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_14436,plain,(
    ! [D_1978,A_1979,B_1980,C_1981] :
      ( k1_xboole_0 = D_1978
      | k3_zfmisc_1(A_1979,B_1980,C_1981) = k1_xboole_0
      | k4_zfmisc_1(A_1979,B_1980,C_1981,D_1978) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14204,c_2])).

tff(c_14451,plain,
    ( k1_xboole_0 = '#skF_4'
    | k3_zfmisc_1('#skF_1','#skF_2','#skF_7') = k1_xboole_0
    | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_14199,c_14436])).

tff(c_14460,plain,
    ( k3_zfmisc_1('#skF_1','#skF_2','#skF_7') = k1_xboole_0
    | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_14451])).

tff(c_14461,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_14460])).

tff(c_14466,plain,(
    ! [A_1985,E_1983,D_1987,F_1986,B_1984,C_1982] :
      ( E_1983 = B_1984
      | k3_zfmisc_1(A_1985,B_1984,C_1982) = k1_xboole_0
      | k3_zfmisc_1(D_1987,E_1983,F_1986) != k3_zfmisc_1(A_1985,B_1984,C_1982) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_14472,plain,(
    ! [A_3,E_1983,D_1987,F_1986,C_5,C_1945,B_4] :
      ( E_1983 = C_5
      | k3_zfmisc_1(k2_zfmisc_1(A_3,B_4),C_5,C_1945) = k1_xboole_0
      | k4_zfmisc_1(A_3,B_4,C_5,C_1945) != k3_zfmisc_1(D_1987,E_1983,F_1986) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14348,c_14466])).

tff(c_15185,plain,(
    ! [A_2085,D_2082,E_2083,C_2087,F_2084,C_2086,B_2088] :
      ( E_2083 = C_2087
      | k4_zfmisc_1(A_2085,B_2088,C_2087,C_2086) = k1_xboole_0
      | k4_zfmisc_1(A_2085,B_2088,C_2087,C_2086) != k3_zfmisc_1(D_2082,E_2083,F_2084) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14348,c_14472])).

tff(c_15212,plain,(
    ! [E_2083,D_2082,F_2084] :
      ( E_2083 = '#skF_7'
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_7','#skF_4') = k1_xboole_0
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k3_zfmisc_1(D_2082,E_2083,F_2084) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14199,c_15185])).

tff(c_15228,plain,(
    ! [E_2083,D_2082,F_2084] :
      ( E_2083 = '#skF_7'
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = k1_xboole_0
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k3_zfmisc_1(D_2082,E_2083,F_2084) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14199,c_15212])).

tff(c_15230,plain,(
    ! [E_2089,D_2090,F_2091] :
      ( E_2089 = '#skF_7'
      | k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k3_zfmisc_1(D_2090,E_2089,F_2091) ) ),
    inference(negUnitSimplification,[status(thm)],[c_14461,c_15228])).

tff(c_15236,plain,(
    ! [C_5,A_3,B_4,C_1945] :
      ( C_5 = '#skF_7'
      | k4_zfmisc_1(A_3,B_4,C_5,C_1945) != k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14348,c_15230])).

tff(c_15248,plain,(
    '#skF_7' = '#skF_3' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_15236])).

tff(c_15250,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14146,c_15248])).

tff(c_15251,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_7') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_14460])).

tff(c_15265,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_15251,c_12])).

tff(c_15275,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_38,c_15265])).

tff(c_15296,plain,(
    '#skF_7' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15275,c_40])).

tff(c_15293,plain,(
    '#skF_7' != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15275,c_38])).

tff(c_15294,plain,(
    '#skF_7' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15275,c_34])).

tff(c_15252,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_14460])).

tff(c_15366,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15275,c_15252])).

tff(c_14349,plain,(
    ! [A_1968,B_1969,C_1970,C_1971] : k3_zfmisc_1(k2_zfmisc_1(A_1968,B_1969),C_1970,C_1971) = k4_zfmisc_1(A_1968,B_1969,C_1970,C_1971) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_14179])).

tff(c_14172,plain,(
    ! [C_1945,A_1943,B_1944] :
      ( k1_xboole_0 = C_1945
      | k2_zfmisc_1(A_1943,B_1944) = k1_xboole_0
      | k3_zfmisc_1(A_1943,B_1944,C_1945) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14163,c_2])).

tff(c_14355,plain,(
    ! [C_1971,A_1968,B_1969,C_1970] :
      ( k1_xboole_0 = C_1971
      | k2_zfmisc_1(k2_zfmisc_1(A_1968,B_1969),C_1970) = k1_xboole_0
      | k4_zfmisc_1(A_1968,B_1969,C_1970,C_1971) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14349,c_14172])).

tff(c_14394,plain,(
    ! [C_1971,A_1968,B_1969,C_1970] :
      ( k1_xboole_0 = C_1971
      | k3_zfmisc_1(A_1968,B_1969,C_1970) = k1_xboole_0
      | k4_zfmisc_1(A_1968,B_1969,C_1970,C_1971) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_14355])).

tff(c_15882,plain,(
    ! [C_2156,A_2157,B_2158,C_2159] :
      ( C_2156 = '#skF_7'
      | k3_zfmisc_1(A_2157,B_2158,C_2159) = '#skF_7'
      | k4_zfmisc_1(A_2157,B_2158,C_2159,C_2156) != '#skF_7' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15275,c_15275,c_15275,c_14394])).

tff(c_15897,plain,
    ( '#skF_7' = '#skF_4'
    | k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_15366,c_15882])).

tff(c_15908,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_15294,c_15897])).

tff(c_15283,plain,(
    ! [A_10,B_11,C_12] :
      ( k3_zfmisc_1(A_10,B_11,C_12) != '#skF_7'
      | C_12 = '#skF_7'
      | B_11 = '#skF_7'
      | A_10 = '#skF_7' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15275,c_15275,c_15275,c_15275,c_12])).

tff(c_15915,plain,
    ( '#skF_7' = '#skF_3'
    | '#skF_7' = '#skF_2'
    | '#skF_7' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_15908,c_15283])).

tff(c_15958,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_15296,c_15293,c_14146,c_15915])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:17:50 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.64/3.14  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.12/3.21  
% 9.12/3.21  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.12/3.21  %$ k4_zfmisc_1 > k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4
% 9.12/3.21  
% 9.12/3.21  %Foreground sorts:
% 9.12/3.21  
% 9.12/3.21  
% 9.12/3.21  %Background operators:
% 9.12/3.21  
% 9.12/3.21  
% 9.12/3.21  %Foreground operators:
% 9.12/3.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.12/3.21  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.12/3.21  tff(k4_zfmisc_1, type, k4_zfmisc_1: ($i * $i * $i * $i) > $i).
% 9.12/3.21  tff('#skF_7', type, '#skF_7': $i).
% 9.12/3.21  tff('#skF_5', type, '#skF_5': $i).
% 9.12/3.21  tff('#skF_6', type, '#skF_6': $i).
% 9.12/3.21  tff('#skF_2', type, '#skF_2': $i).
% 9.12/3.21  tff('#skF_3', type, '#skF_3': $i).
% 9.12/3.21  tff('#skF_1', type, '#skF_1': $i).
% 9.12/3.21  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 9.12/3.21  tff('#skF_8', type, '#skF_8': $i).
% 9.12/3.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.12/3.21  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.12/3.21  tff('#skF_4', type, '#skF_4': $i).
% 9.12/3.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.12/3.21  
% 9.28/3.25  tff(f_90, negated_conjecture, ~(![A, B, C, D, E, F, G, H]: ((k4_zfmisc_1(A, B, C, D) = k4_zfmisc_1(E, F, G, H)) => (((((A = k1_xboole_0) | (B = k1_xboole_0)) | (C = k1_xboole_0)) | (D = k1_xboole_0)) | ((((A = E) & (B = F)) & (C = G)) & (D = H))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_mcart_1)).
% 9.28/3.25  tff(f_33, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 9.28/3.25  tff(f_35, axiom, (![A, B, C, D]: (k4_zfmisc_1(A, B, C, D) = k2_zfmisc_1(k3_zfmisc_1(A, B, C), D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_zfmisc_1)).
% 9.28/3.25  tff(f_31, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 9.28/3.25  tff(f_71, axiom, (![A, B, C, D, E, F]: ((k3_zfmisc_1(A, B, C) = k3_zfmisc_1(D, E, F)) => ((k3_zfmisc_1(A, B, C) = k1_xboole_0) | (((A = D) & (B = E)) & (C = F))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_mcart_1)).
% 9.28/3.25  tff(f_47, axiom, (![A, B, C]: (((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) <=> ~(k3_zfmisc_1(A, B, C) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_mcart_1)).
% 9.28/3.25  tff(f_61, axiom, (![A, B, C, D, E, F]: ((k3_zfmisc_1(A, B, C) = k3_zfmisc_1(D, E, F)) => ((((A = k1_xboole_0) | (B = k1_xboole_0)) | (C = k1_xboole_0)) | (((A = D) & (B = E)) & (C = F))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_mcart_1)).
% 9.28/3.25  tff(c_40, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_90])).
% 9.28/3.25  tff(c_38, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_90])).
% 9.28/3.25  tff(c_36, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_90])).
% 9.28/3.25  tff(c_34, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_90])).
% 9.28/3.25  tff(c_32, plain, ('#skF_8'!='#skF_4' | '#skF_7'!='#skF_3' | '#skF_6'!='#skF_2' | '#skF_5'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_90])).
% 9.28/3.25  tff(c_110, plain, ('#skF_5'!='#skF_1'), inference(splitLeft, [status(thm)], [c_32])).
% 9.28/3.25  tff(c_8, plain, (![A_3, B_4, C_5]: (k2_zfmisc_1(k2_zfmisc_1(A_3, B_4), C_5)=k3_zfmisc_1(A_3, B_4, C_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 9.28/3.25  tff(c_10, plain, (![A_6, B_7, C_8, D_9]: (k2_zfmisc_1(k3_zfmisc_1(A_6, B_7, C_8), D_9)=k4_zfmisc_1(A_6, B_7, C_8, D_9))), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.28/3.25  tff(c_122, plain, (![A_35, B_36, C_37]: (k2_zfmisc_1(k2_zfmisc_1(A_35, B_36), C_37)=k3_zfmisc_1(A_35, B_36, C_37))), inference(cnfTransformation, [status(thm)], [f_33])).
% 9.28/3.25  tff(c_138, plain, (![A_3, B_4, C_5, C_37]: (k3_zfmisc_1(k2_zfmisc_1(A_3, B_4), C_5, C_37)=k2_zfmisc_1(k3_zfmisc_1(A_3, B_4, C_5), C_37))), inference(superposition, [status(thm), theory('equality')], [c_8, c_122])).
% 9.28/3.25  tff(c_332, plain, (![A_3, B_4, C_5, C_37]: (k3_zfmisc_1(k2_zfmisc_1(A_3, B_4), C_5, C_37)=k4_zfmisc_1(A_3, B_4, C_5, C_37))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_138])).
% 9.28/3.25  tff(c_42, plain, (k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_90])).
% 9.28/3.25  tff(c_178, plain, (![A_41, B_42, C_43, D_44]: (k2_zfmisc_1(k3_zfmisc_1(A_41, B_42, C_43), D_44)=k4_zfmisc_1(A_41, B_42, C_43, D_44))), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.28/3.25  tff(c_2, plain, (![B_2, A_1]: (k1_xboole_0=B_2 | k1_xboole_0=A_1 | k2_zfmisc_1(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.28/3.25  tff(c_427, plain, (![D_76, A_77, B_78, C_79]: (k1_xboole_0=D_76 | k3_zfmisc_1(A_77, B_78, C_79)=k1_xboole_0 | k4_zfmisc_1(A_77, B_78, C_79, D_76)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_178, c_2])).
% 9.28/3.25  tff(c_442, plain, (k1_xboole_0='#skF_8' | k3_zfmisc_1('#skF_5', '#skF_6', '#skF_7')=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_42, c_427])).
% 9.28/3.25  tff(c_451, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_442])).
% 9.28/3.25  tff(c_398, plain, (![C_70, F_74, B_72, D_75, A_73, E_71]: (E_71=B_72 | k3_zfmisc_1(A_73, B_72, C_70)=k1_xboole_0 | k3_zfmisc_1(D_75, E_71, F_74)!=k3_zfmisc_1(A_73, B_72, C_70))), inference(cnfTransformation, [status(thm)], [f_71])).
% 9.28/3.25  tff(c_404, plain, (![A_3, F_74, C_37, D_75, C_5, E_71, B_4]: (E_71=C_5 | k3_zfmisc_1(k2_zfmisc_1(A_3, B_4), C_5, C_37)=k1_xboole_0 | k4_zfmisc_1(A_3, B_4, C_5, C_37)!=k3_zfmisc_1(D_75, E_71, F_74))), inference(superposition, [status(thm), theory('equality')], [c_332, c_398])).
% 9.28/3.25  tff(c_965, plain, (![B_150, C_148, D_149, E_144, F_145, A_147, C_146]: (E_144=C_148 | k4_zfmisc_1(A_147, B_150, C_148, C_146)=k1_xboole_0 | k4_zfmisc_1(A_147, B_150, C_148, C_146)!=k3_zfmisc_1(D_149, E_144, F_145))), inference(demodulation, [status(thm), theory('equality')], [c_332, c_404])).
% 9.28/3.25  tff(c_992, plain, (![E_144, D_149, F_145]: (E_144='#skF_7' | k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k3_zfmisc_1(D_149, E_144, F_145))), inference(superposition, [status(thm), theory('equality')], [c_42, c_965])).
% 9.28/3.25  tff(c_1008, plain, (![E_144, D_149, F_145]: (E_144='#skF_7' | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k3_zfmisc_1(D_149, E_144, F_145))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_992])).
% 9.28/3.25  tff(c_1010, plain, (![E_151, D_152, F_153]: (E_151='#skF_7' | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k3_zfmisc_1(D_152, E_151, F_153))), inference(negUnitSimplification, [status(thm)], [c_451, c_1008])).
% 9.28/3.25  tff(c_1016, plain, (![C_5, A_3, B_4, C_37]: (C_5='#skF_7' | k4_zfmisc_1(A_3, B_4, C_5, C_37)!=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_332, c_1010])).
% 9.28/3.25  tff(c_1028, plain, ('#skF_7'='#skF_3'), inference(reflexivity, [status(thm), theory('equality')], [c_1016])).
% 9.28/3.25  tff(c_1055, plain, (k4_zfmisc_1('#skF_5', '#skF_6', '#skF_3', '#skF_8')=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1028, c_42])).
% 9.28/3.25  tff(c_620, plain, (![D_99, E_95, C_94, B_96, F_98, A_97]: (F_98=C_94 | k3_zfmisc_1(A_97, B_96, C_94)=k1_xboole_0 | k3_zfmisc_1(D_99, E_95, F_98)!=k3_zfmisc_1(A_97, B_96, C_94))), inference(cnfTransformation, [status(thm)], [f_71])).
% 9.28/3.25  tff(c_632, plain, (![A_3, D_99, E_95, C_37, C_5, F_98, B_4]: (F_98=C_37 | k3_zfmisc_1(k2_zfmisc_1(A_3, B_4), C_5, C_37)=k1_xboole_0 | k4_zfmisc_1(A_3, B_4, C_5, C_37)!=k3_zfmisc_1(D_99, E_95, F_98))), inference(superposition, [status(thm), theory('equality')], [c_332, c_620])).
% 9.28/3.25  tff(c_1301, plain, (![A_195, B_199, C_194, C_198, E_196, F_193, D_197]: (F_193=C_194 | k4_zfmisc_1(A_195, B_199, C_198, C_194)=k1_xboole_0 | k4_zfmisc_1(A_195, B_199, C_198, C_194)!=k3_zfmisc_1(D_197, E_196, F_193))), inference(demodulation, [status(thm), theory('equality')], [c_332, c_632])).
% 9.28/3.25  tff(c_1304, plain, (![F_193, D_197, E_196]: (F_193='#skF_8' | k4_zfmisc_1('#skF_5', '#skF_6', '#skF_3', '#skF_8')=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k3_zfmisc_1(D_197, E_196, F_193))), inference(superposition, [status(thm), theory('equality')], [c_1055, c_1301])).
% 9.28/3.25  tff(c_1338, plain, (![F_193, D_197, E_196]: (F_193='#skF_8' | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k3_zfmisc_1(D_197, E_196, F_193))), inference(demodulation, [status(thm), theory('equality')], [c_1055, c_1304])).
% 9.28/3.25  tff(c_1347, plain, (![F_200, D_201, E_202]: (F_200='#skF_8' | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k3_zfmisc_1(D_201, E_202, F_200))), inference(negUnitSimplification, [status(thm)], [c_451, c_1338])).
% 9.28/3.25  tff(c_1353, plain, (![C_37, A_3, B_4, C_5]: (C_37='#skF_8' | k4_zfmisc_1(A_3, B_4, C_5, C_37)!=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_332, c_1347])).
% 9.28/3.25  tff(c_1365, plain, ('#skF_8'='#skF_4'), inference(reflexivity, [status(thm), theory('equality')], [c_1353])).
% 9.28/3.25  tff(c_1392, plain, (k4_zfmisc_1('#skF_5', '#skF_6', '#skF_3', '#skF_4')=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1365, c_1055])).
% 9.28/3.25  tff(c_333, plain, (![A_66, B_67, C_68, C_69]: (k3_zfmisc_1(k2_zfmisc_1(A_66, B_67), C_68, C_69)=k4_zfmisc_1(A_66, B_67, C_68, C_69))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_138])).
% 9.28/3.25  tff(c_30, plain, (![A_19, C_21, D_22, B_20, F_24, E_23]: (D_22=A_19 | k3_zfmisc_1(A_19, B_20, C_21)=k1_xboole_0 | k3_zfmisc_1(D_22, E_23, F_24)!=k3_zfmisc_1(A_19, B_20, C_21))), inference(cnfTransformation, [status(thm)], [f_71])).
% 9.28/3.25  tff(c_345, plain, (![B_67, A_66, C_68, D_22, C_69, F_24, E_23]: (k2_zfmisc_1(A_66, B_67)=D_22 | k3_zfmisc_1(k2_zfmisc_1(A_66, B_67), C_68, C_69)=k1_xboole_0 | k4_zfmisc_1(A_66, B_67, C_68, C_69)!=k3_zfmisc_1(D_22, E_23, F_24))), inference(superposition, [status(thm), theory('equality')], [c_333, c_30])).
% 9.28/3.25  tff(c_3168, plain, (![D_376, C_375, C_378, A_373, E_372, B_377, F_374]: (k2_zfmisc_1(A_373, B_377)=D_376 | k4_zfmisc_1(A_373, B_377, C_378, C_375)=k1_xboole_0 | k4_zfmisc_1(A_373, B_377, C_378, C_375)!=k3_zfmisc_1(D_376, E_372, F_374))), inference(demodulation, [status(thm), theory('equality')], [c_332, c_345])).
% 9.28/3.25  tff(c_3171, plain, (![D_376, E_372, F_374]: (k2_zfmisc_1('#skF_5', '#skF_6')=D_376 | k4_zfmisc_1('#skF_5', '#skF_6', '#skF_3', '#skF_4')=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k3_zfmisc_1(D_376, E_372, F_374))), inference(superposition, [status(thm), theory('equality')], [c_1392, c_3168])).
% 9.28/3.25  tff(c_3205, plain, (![D_376, E_372, F_374]: (k2_zfmisc_1('#skF_5', '#skF_6')=D_376 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k3_zfmisc_1(D_376, E_372, F_374))), inference(demodulation, [status(thm), theory('equality')], [c_1392, c_3171])).
% 9.28/3.25  tff(c_3213, plain, (![D_379, E_380, F_381]: (k2_zfmisc_1('#skF_5', '#skF_6')=D_379 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k3_zfmisc_1(D_379, E_380, F_381))), inference(negUnitSimplification, [status(thm)], [c_451, c_3205])).
% 9.28/3.25  tff(c_3219, plain, (![A_3, B_4, C_5, C_37]: (k2_zfmisc_1(A_3, B_4)=k2_zfmisc_1('#skF_5', '#skF_6') | k4_zfmisc_1(A_3, B_4, C_5, C_37)!=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_332, c_3213])).
% 9.28/3.25  tff(c_3231, plain, (k2_zfmisc_1('#skF_5', '#skF_6')=k2_zfmisc_1('#skF_1', '#skF_2')), inference(reflexivity, [status(thm), theory('equality')], [c_3219])).
% 9.28/3.25  tff(c_3318, plain, (k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k2_zfmisc_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_3231, c_2])).
% 9.28/3.25  tff(c_3460, plain, (k2_zfmisc_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_3318])).
% 9.28/3.25  tff(c_3315, plain, (![C_5]: (k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), C_5)=k3_zfmisc_1('#skF_5', '#skF_6', C_5))), inference(superposition, [status(thm), theory('equality')], [c_3231, c_8])).
% 9.28/3.25  tff(c_3326, plain, (![C_393]: (k3_zfmisc_1('#skF_5', '#skF_6', C_393)=k3_zfmisc_1('#skF_1', '#skF_2', C_393))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_3315])).
% 9.28/3.25  tff(c_12, plain, (![A_10, B_11, C_12]: (k3_zfmisc_1(A_10, B_11, C_12)!=k1_xboole_0 | k1_xboole_0=C_12 | k1_xboole_0=B_11 | k1_xboole_0=A_10)), inference(cnfTransformation, [status(thm)], [f_47])).
% 9.28/3.25  tff(c_3431, plain, (![C_393]: (k3_zfmisc_1('#skF_1', '#skF_2', C_393)!=k1_xboole_0 | k1_xboole_0=C_393 | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_3326, c_12])).
% 9.28/3.25  tff(c_3598, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_3431])).
% 9.28/3.25  tff(c_3601, plain, (k2_zfmisc_1('#skF_1', '#skF_2')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_3598, c_3460])).
% 9.28/3.25  tff(c_6, plain, (![B_2]: (k2_zfmisc_1(k1_xboole_0, B_2)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.28/3.25  tff(c_3642, plain, (![B_2]: (k2_zfmisc_1('#skF_5', B_2)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_3598, c_3598, c_6])).
% 9.28/3.25  tff(c_3723, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_3642, c_3231])).
% 9.28/3.25  tff(c_3749, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3601, c_3723])).
% 9.28/3.25  tff(c_3751, plain, (k1_xboole_0!='#skF_5'), inference(splitRight, [status(thm)], [c_3431])).
% 9.28/3.25  tff(c_28, plain, (![A_19, C_21, D_22, B_20, F_24, E_23]: (E_23=B_20 | k3_zfmisc_1(A_19, B_20, C_21)=k1_xboole_0 | k3_zfmisc_1(D_22, E_23, F_24)!=k3_zfmisc_1(A_19, B_20, C_21))), inference(cnfTransformation, [status(thm)], [f_71])).
% 9.28/3.25  tff(c_3413, plain, (![B_20, A_19, C_21, C_393]: (B_20='#skF_6' | k3_zfmisc_1(A_19, B_20, C_21)=k1_xboole_0 | k3_zfmisc_1(A_19, B_20, C_21)!=k3_zfmisc_1('#skF_1', '#skF_2', C_393))), inference(superposition, [status(thm), theory('equality')], [c_3326, c_28])).
% 9.28/3.25  tff(c_3987, plain, (![C_393]: ('#skF_6'='#skF_2' | k3_zfmisc_1('#skF_1', '#skF_2', C_393)=k1_xboole_0)), inference(reflexivity, [status(thm), theory('equality')], [c_3413])).
% 9.28/3.25  tff(c_4018, plain, ('#skF_6'='#skF_2'), inference(splitLeft, [status(thm)], [c_3987])).
% 9.28/3.25  tff(c_3323, plain, (![C_5]: (k3_zfmisc_1('#skF_5', '#skF_6', C_5)=k3_zfmisc_1('#skF_1', '#skF_2', C_5))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_3315])).
% 9.28/3.25  tff(c_4093, plain, (![C_442]: (k3_zfmisc_1('#skF_5', '#skF_2', C_442)=k3_zfmisc_1('#skF_1', '#skF_2', C_442))), inference(demodulation, [status(thm), theory('equality')], [c_4018, c_3323])).
% 9.28/3.25  tff(c_24, plain, (![E_17, F_18, A_13, B_14, C_15, D_16]: (D_16=A_13 | k1_xboole_0=C_15 | k1_xboole_0=B_14 | k1_xboole_0=A_13 | k3_zfmisc_1(D_16, E_17, F_18)!=k3_zfmisc_1(A_13, B_14, C_15))), inference(cnfTransformation, [status(thm)], [f_61])).
% 9.28/3.25  tff(c_4171, plain, (![D_16, C_442, E_17, F_18]: (D_16='#skF_5' | k1_xboole_0=C_442 | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_5' | k3_zfmisc_1(D_16, E_17, F_18)!=k3_zfmisc_1('#skF_1', '#skF_2', C_442))), inference(superposition, [status(thm), theory('equality')], [c_4093, c_24])).
% 9.28/3.25  tff(c_4232, plain, (![D_16, C_442, E_17, F_18]: (D_16='#skF_5' | k1_xboole_0=C_442 | k3_zfmisc_1(D_16, E_17, F_18)!=k3_zfmisc_1('#skF_1', '#skF_2', C_442))), inference(negUnitSimplification, [status(thm)], [c_3751, c_38, c_4171])).
% 9.28/3.25  tff(c_4435, plain, (![C_442]: ('#skF_5'='#skF_1' | k1_xboole_0=C_442)), inference(reflexivity, [status(thm), theory('equality')], [c_4232])).
% 9.28/3.25  tff(c_4463, plain, (![C_457]: (k1_xboole_0=C_457)), inference(negUnitSimplification, [status(thm)], [c_110, c_4435])).
% 9.28/3.25  tff(c_4023, plain, (k2_zfmisc_1('#skF_5', '#skF_2')=k2_zfmisc_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4018, c_3231])).
% 9.28/3.25  tff(c_4493, plain, (k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_4463, c_4023])).
% 9.28/3.25  tff(c_4590, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3460, c_4493])).
% 9.28/3.25  tff(c_4591, plain, (![C_393]: (k3_zfmisc_1('#skF_1', '#skF_2', C_393)=k1_xboole_0)), inference(splitRight, [status(thm)], [c_3987])).
% 9.28/3.25  tff(c_452, plain, (![C_81, B_83, C_84, A_80, D_82]: (k3_zfmisc_1(k3_zfmisc_1(A_80, B_83, C_81), D_82, C_84)=k2_zfmisc_1(k4_zfmisc_1(A_80, B_83, C_81, D_82), C_84))), inference(superposition, [status(thm), theory('equality')], [c_178, c_8])).
% 9.28/3.25  tff(c_479, plain, (![C_81, B_83, C_84, A_80, D_82]: (k2_zfmisc_1(k4_zfmisc_1(A_80, B_83, C_81, D_82), C_84)!=k1_xboole_0 | k1_xboole_0=C_84 | k1_xboole_0=D_82 | k3_zfmisc_1(A_80, B_83, C_81)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_452, c_12])).
% 9.28/3.25  tff(c_1406, plain, (![C_84]: (k2_zfmisc_1(k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), C_84)!=k1_xboole_0 | k1_xboole_0=C_84 | k1_xboole_0='#skF_4' | k3_zfmisc_1('#skF_5', '#skF_6', '#skF_3')=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1392, c_479])).
% 9.28/3.25  tff(c_1435, plain, (![C_84]: (k2_zfmisc_1(k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), C_84)!=k1_xboole_0 | k1_xboole_0=C_84 | k3_zfmisc_1('#skF_5', '#skF_6', '#skF_3')=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_34, c_1406])).
% 9.28/3.25  tff(c_1560, plain, (k3_zfmisc_1('#skF_5', '#skF_6', '#skF_3')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_1435])).
% 9.28/3.25  tff(c_1612, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_1560, c_12])).
% 9.28/3.25  tff(c_1629, plain, (k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_36, c_1612])).
% 9.28/3.25  tff(c_1651, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_1629])).
% 9.28/3.25  tff(c_1667, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_1651, c_451])).
% 9.28/3.25  tff(c_18, plain, (![B_11, C_12]: (k3_zfmisc_1(k1_xboole_0, B_11, C_12)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 9.28/3.25  tff(c_197, plain, (![B_11, C_12, D_44]: (k4_zfmisc_1(k1_xboole_0, B_11, C_12, D_44)=k2_zfmisc_1(k1_xboole_0, D_44))), inference(superposition, [status(thm), theory('equality')], [c_18, c_178])).
% 9.28/3.25  tff(c_210, plain, (![B_11, C_12, D_44]: (k4_zfmisc_1(k1_xboole_0, B_11, C_12, D_44)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_197])).
% 9.28/3.25  tff(c_1672, plain, (![B_11, C_12, D_44]: (k4_zfmisc_1('#skF_5', B_11, C_12, D_44)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1651, c_1651, c_210])).
% 9.28/3.25  tff(c_2054, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_1672, c_1392])).
% 9.28/3.25  tff(c_2238, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1667, c_2054])).
% 9.28/3.25  tff(c_2239, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_1629])).
% 9.28/3.25  tff(c_2272, plain, (![B_2]: (k2_zfmisc_1('#skF_6', B_2)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2239, c_2239, c_6])).
% 9.28/3.25  tff(c_1609, plain, (![D_9]: (k4_zfmisc_1('#skF_5', '#skF_6', '#skF_3', D_9)=k2_zfmisc_1(k1_xboole_0, D_9))), inference(superposition, [status(thm), theory('equality')], [c_1560, c_10])).
% 9.28/3.25  tff(c_1626, plain, (![D_9]: (k4_zfmisc_1('#skF_5', '#skF_6', '#skF_3', D_9)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_1609])).
% 9.28/3.25  tff(c_2621, plain, (![D_9]: (k4_zfmisc_1('#skF_5', '#skF_6', '#skF_3', D_9)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2239, c_1626])).
% 9.28/3.25  tff(c_2622, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_2621, c_1392])).
% 9.28/3.25  tff(c_184, plain, (![D_44, C_43, A_41, B_42, C_5]: (k3_zfmisc_1(k3_zfmisc_1(A_41, B_42, C_43), D_44, C_5)=k2_zfmisc_1(k4_zfmisc_1(A_41, B_42, C_43, D_44), C_5))), inference(superposition, [status(thm), theory('equality')], [c_178, c_8])).
% 9.28/3.25  tff(c_1013, plain, (![D_44, C_43, A_41, B_42, C_5]: (D_44='#skF_7' | k2_zfmisc_1(k4_zfmisc_1(A_41, B_42, C_43, D_44), C_5)!=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_184, c_1010])).
% 9.28/3.25  tff(c_1128, plain, (![C_169, C_166, A_165, D_167, B_168]: (D_167='#skF_3' | k2_zfmisc_1(k4_zfmisc_1(A_165, B_168, C_166, D_167), C_169)!=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1028, c_1013])).
% 9.28/3.25  tff(c_1131, plain, (![C_169]: ('#skF_3'='#skF_8' | k2_zfmisc_1(k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), C_169)!=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1055, c_1128])).
% 9.28/3.25  tff(c_1201, plain, (![C_169]: (k2_zfmisc_1(k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), C_169)!=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_1131])).
% 9.28/3.25  tff(c_2723, plain, (![C_169]: (k2_zfmisc_1('#skF_6', C_169)!='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2622, c_2622, c_1201])).
% 9.28/3.25  tff(c_2729, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2272, c_2723])).
% 9.28/3.25  tff(c_2731, plain, (k3_zfmisc_1('#skF_5', '#skF_6', '#skF_3')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_1435])).
% 9.28/3.25  tff(c_3325, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_3323, c_2731])).
% 9.28/3.25  tff(c_4652, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4591, c_3325])).
% 9.28/3.25  tff(c_4653, plain, (k1_xboole_0='#skF_5' | k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_3318])).
% 9.28/3.25  tff(c_4655, plain, (k1_xboole_0='#skF_6'), inference(splitLeft, [status(thm)], [c_4653])).
% 9.28/3.25  tff(c_16, plain, (![A_10, C_12]: (k3_zfmisc_1(A_10, k1_xboole_0, C_12)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 9.28/3.25  tff(c_4694, plain, (![A_10, C_12]: (k3_zfmisc_1(A_10, '#skF_6', C_12)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_4655, c_4655, c_16])).
% 9.28/3.25  tff(c_4815, plain, (![C_5]: (k3_zfmisc_1('#skF_1', '#skF_2', C_5)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_4694, c_3323])).
% 9.28/3.25  tff(c_4657, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_4655, c_3325])).
% 9.28/3.25  tff(c_4998, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4815, c_4657])).
% 9.28/3.25  tff(c_4999, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_4653])).
% 9.28/3.25  tff(c_5038, plain, (![B_11, C_12]: (k3_zfmisc_1('#skF_5', B_11, C_12)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_4999, c_4999, c_18])).
% 9.28/3.25  tff(c_5190, plain, (![C_5]: (k3_zfmisc_1('#skF_1', '#skF_2', C_5)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_5038, c_3323])).
% 9.28/3.25  tff(c_5002, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_4999, c_3325])).
% 9.28/3.25  tff(c_5282, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5190, c_5002])).
% 9.28/3.25  tff(c_5283, plain, ('#skF_3'='#skF_8'), inference(splitRight, [status(thm)], [c_1131])).
% 9.28/3.25  tff(c_5290, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_8', '#skF_4')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_5283, c_451])).
% 9.28/3.25  tff(c_5287, plain, (k4_zfmisc_1('#skF_5', '#skF_6', '#skF_8', '#skF_8')=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_8', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5283, c_5283, c_1055])).
% 9.28/3.25  tff(c_652, plain, (![A_3, D_99, E_95, C_37, C_5, F_98, B_4]: (F_98=C_37 | k4_zfmisc_1(A_3, B_4, C_5, C_37)=k1_xboole_0 | k4_zfmisc_1(A_3, B_4, C_5, C_37)!=k3_zfmisc_1(D_99, E_95, F_98))), inference(demodulation, [status(thm), theory('equality')], [c_332, c_632])).
% 9.28/3.25  tff(c_5343, plain, (![F_98, D_99, E_95]: (F_98='#skF_8' | k4_zfmisc_1('#skF_5', '#skF_6', '#skF_8', '#skF_8')=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_8', '#skF_4')!=k3_zfmisc_1(D_99, E_95, F_98))), inference(superposition, [status(thm), theory('equality')], [c_5287, c_652])).
% 9.28/3.25  tff(c_5364, plain, (![F_98, D_99, E_95]: (F_98='#skF_8' | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_8', '#skF_4')=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_8', '#skF_4')!=k3_zfmisc_1(D_99, E_95, F_98))), inference(demodulation, [status(thm), theory('equality')], [c_5287, c_5343])).
% 9.28/3.25  tff(c_5388, plain, (![F_807, D_808, E_809]: (F_807='#skF_8' | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_8', '#skF_4')!=k3_zfmisc_1(D_808, E_809, F_807))), inference(negUnitSimplification, [status(thm)], [c_5290, c_5364])).
% 9.28/3.25  tff(c_5394, plain, (![C_37, A_3, B_4, C_5]: (C_37='#skF_8' | k4_zfmisc_1(A_3, B_4, C_5, C_37)!=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_8', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_332, c_5388])).
% 9.28/3.25  tff(c_5475, plain, ('#skF_8'='#skF_4'), inference(reflexivity, [status(thm), theory('equality')], [c_5394])).
% 9.28/3.25  tff(c_5505, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_4', '#skF_4')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_5475, c_5290])).
% 9.28/3.25  tff(c_5504, plain, (k4_zfmisc_1('#skF_5', '#skF_6', '#skF_4', '#skF_4')=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5475, c_5475, c_5475, c_5287])).
% 9.28/3.25  tff(c_7708, plain, (![D_1063, A_1060, C_1062, B_1064, C_1065, F_1061, E_1059]: (k2_zfmisc_1(A_1060, B_1064)=D_1063 | k4_zfmisc_1(A_1060, B_1064, C_1065, C_1062)=k1_xboole_0 | k4_zfmisc_1(A_1060, B_1064, C_1065, C_1062)!=k3_zfmisc_1(D_1063, E_1059, F_1061))), inference(demodulation, [status(thm), theory('equality')], [c_332, c_345])).
% 9.28/3.25  tff(c_7711, plain, (![D_1063, E_1059, F_1061]: (k2_zfmisc_1('#skF_5', '#skF_6')=D_1063 | k4_zfmisc_1('#skF_5', '#skF_6', '#skF_4', '#skF_4')=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_4', '#skF_4')!=k3_zfmisc_1(D_1063, E_1059, F_1061))), inference(superposition, [status(thm), theory('equality')], [c_5504, c_7708])).
% 9.28/3.25  tff(c_7745, plain, (![D_1063, E_1059, F_1061]: (k2_zfmisc_1('#skF_5', '#skF_6')=D_1063 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_4', '#skF_4')=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_4', '#skF_4')!=k3_zfmisc_1(D_1063, E_1059, F_1061))), inference(demodulation, [status(thm), theory('equality')], [c_5504, c_7711])).
% 9.28/3.25  tff(c_7753, plain, (![D_1066, E_1067, F_1068]: (k2_zfmisc_1('#skF_5', '#skF_6')=D_1066 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_4', '#skF_4')!=k3_zfmisc_1(D_1066, E_1067, F_1068))), inference(negUnitSimplification, [status(thm)], [c_5505, c_7745])).
% 9.28/3.25  tff(c_7759, plain, (![A_3, B_4, C_5, C_37]: (k2_zfmisc_1(A_3, B_4)=k2_zfmisc_1('#skF_5', '#skF_6') | k4_zfmisc_1(A_3, B_4, C_5, C_37)!=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_4', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_332, c_7753])).
% 9.28/3.25  tff(c_7771, plain, (k2_zfmisc_1('#skF_5', '#skF_6')=k2_zfmisc_1('#skF_1', '#skF_2')), inference(reflexivity, [status(thm), theory('equality')], [c_7759])).
% 9.28/3.25  tff(c_7812, plain, (![C_5]: (k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), C_5)=k3_zfmisc_1('#skF_5', '#skF_6', C_5))), inference(superposition, [status(thm), theory('equality')], [c_7771, c_8])).
% 9.28/3.25  tff(c_7823, plain, (![C_1073]: (k3_zfmisc_1('#skF_5', '#skF_6', C_1073)=k3_zfmisc_1('#skF_1', '#skF_2', C_1073))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_7812])).
% 9.28/3.25  tff(c_7919, plain, (![A_19, B_20, C_21, C_1073]: (A_19='#skF_5' | k3_zfmisc_1(A_19, B_20, C_21)=k1_xboole_0 | k3_zfmisc_1(A_19, B_20, C_21)!=k3_zfmisc_1('#skF_1', '#skF_2', C_1073))), inference(superposition, [status(thm), theory('equality')], [c_7823, c_30])).
% 9.28/3.25  tff(c_8526, plain, (![C_1073]: ('#skF_5'='#skF_1' | k3_zfmisc_1('#skF_1', '#skF_2', C_1073)=k1_xboole_0)), inference(reflexivity, [status(thm), theory('equality')], [c_7919])).
% 9.28/3.25  tff(c_8527, plain, (![C_1073]: (k3_zfmisc_1('#skF_1', '#skF_2', C_1073)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_110, c_8526])).
% 9.28/3.25  tff(c_7820, plain, (![C_5]: (k3_zfmisc_1('#skF_5', '#skF_6', C_5)=k3_zfmisc_1('#skF_1', '#skF_2', C_5))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_7812])).
% 9.28/3.25  tff(c_5291, plain, (k1_xboole_0!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_5283, c_36])).
% 9.28/3.25  tff(c_5433, plain, (![B_818, C_817, D_815, A_814, C_816]: (k2_zfmisc_1(k4_zfmisc_1(A_814, B_818, C_816, D_815), C_817)!=k1_xboole_0 | k1_xboole_0=C_817 | k1_xboole_0=D_815 | k3_zfmisc_1(A_814, B_818, C_816)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_452, c_12])).
% 9.28/3.25  tff(c_5436, plain, (![C_817]: (k2_zfmisc_1(k4_zfmisc_1('#skF_1', '#skF_2', '#skF_8', '#skF_4'), C_817)!=k1_xboole_0 | k1_xboole_0=C_817 | k1_xboole_0='#skF_8' | k3_zfmisc_1('#skF_5', '#skF_6', '#skF_8')=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_5287, c_5433])).
% 9.28/3.25  tff(c_5459, plain, (![C_817]: (k2_zfmisc_1(k4_zfmisc_1('#skF_1', '#skF_2', '#skF_8', '#skF_4'), C_817)!=k1_xboole_0 | k1_xboole_0=C_817 | k3_zfmisc_1('#skF_5', '#skF_6', '#skF_8')=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_5291, c_5436])).
% 9.28/3.25  tff(c_5517, plain, (![C_817]: (k2_zfmisc_1(k4_zfmisc_1('#skF_1', '#skF_2', '#skF_4', '#skF_4'), C_817)!=k1_xboole_0 | k1_xboole_0=C_817 | k3_zfmisc_1('#skF_5', '#skF_6', '#skF_4')=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_5475, c_5475, c_5459])).
% 9.28/3.25  tff(c_5518, plain, (k3_zfmisc_1('#skF_5', '#skF_6', '#skF_4')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_5517])).
% 9.28/3.25  tff(c_5574, plain, (k1_xboole_0='#skF_4' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_5518, c_12])).
% 9.28/3.25  tff(c_5591, plain, (k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_34, c_5574])).
% 9.28/3.25  tff(c_5613, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_5591])).
% 9.28/3.25  tff(c_5856, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_4', '#skF_4')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_5613, c_5505])).
% 9.28/3.25  tff(c_5631, plain, (![B_11, C_12, D_44]: (k4_zfmisc_1('#skF_5', B_11, C_12, D_44)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_5613, c_5613, c_210])).
% 9.28/3.25  tff(c_6245, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_4', '#skF_4')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_5631, c_5504])).
% 9.28/3.25  tff(c_6246, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5856, c_6245])).
% 9.28/3.25  tff(c_6247, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_5591])).
% 9.28/3.25  tff(c_6571, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_4', '#skF_4')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_6247, c_5505])).
% 9.28/3.25  tff(c_200, plain, (![A_10, C_12, D_44]: (k4_zfmisc_1(A_10, k1_xboole_0, C_12, D_44)=k2_zfmisc_1(k1_xboole_0, D_44))), inference(superposition, [status(thm), theory('equality')], [c_16, c_178])).
% 9.28/3.25  tff(c_211, plain, (![A_10, C_12, D_44]: (k4_zfmisc_1(A_10, k1_xboole_0, C_12, D_44)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_200])).
% 9.28/3.25  tff(c_6344, plain, (![A_10, C_12, D_44]: (k4_zfmisc_1(A_10, '#skF_6', C_12, D_44)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_6247, c_6247, c_211])).
% 9.28/3.25  tff(c_6957, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_4', '#skF_4')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_6344, c_5504])).
% 9.28/3.25  tff(c_6958, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6571, c_6957])).
% 9.28/3.25  tff(c_6960, plain, (k3_zfmisc_1('#skF_5', '#skF_6', '#skF_4')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_5517])).
% 9.28/3.25  tff(c_7822, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_4')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_7820, c_6960])).
% 9.28/3.25  tff(c_8565, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8527, c_7822])).
% 9.28/3.25  tff(c_8567, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_442])).
% 9.28/3.25  tff(c_187, plain, (![D_44, A_41, B_42, C_43]: (k1_xboole_0=D_44 | k3_zfmisc_1(A_41, B_42, C_43)=k1_xboole_0 | k4_zfmisc_1(A_41, B_42, C_43, D_44)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_178, c_2])).
% 9.28/3.25  tff(c_8572, plain, (k1_xboole_0='#skF_4' | k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_8567, c_187])).
% 9.28/3.25  tff(c_8577, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_34, c_8572])).
% 9.28/3.25  tff(c_8600, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_8577, c_12])).
% 9.28/3.25  tff(c_8612, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_38, c_36, c_8600])).
% 9.28/3.25  tff(c_8614, plain, ('#skF_5'='#skF_1'), inference(splitRight, [status(thm)], [c_32])).
% 9.28/3.25  tff(c_8667, plain, (k4_zfmisc_1('#skF_1', '#skF_6', '#skF_7', '#skF_8')=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8614, c_42])).
% 9.28/3.25  tff(c_8688, plain, (![A_1130, B_1131, C_1132, D_1133]: (k2_zfmisc_1(k3_zfmisc_1(A_1130, B_1131, C_1132), D_1133)=k4_zfmisc_1(A_1130, B_1131, C_1132, D_1133))), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.28/3.25  tff(c_8937, plain, (![D_1165, A_1166, B_1167, C_1168]: (k1_xboole_0=D_1165 | k3_zfmisc_1(A_1166, B_1167, C_1168)=k1_xboole_0 | k4_zfmisc_1(A_1166, B_1167, C_1168, D_1165)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_8688, c_2])).
% 9.28/3.25  tff(c_8952, plain, (k1_xboole_0='#skF_8' | k3_zfmisc_1('#skF_1', '#skF_6', '#skF_7')=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_8667, c_8937])).
% 9.28/3.25  tff(c_8961, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_8952])).
% 9.28/3.25  tff(c_8613, plain, ('#skF_6'!='#skF_2' | '#skF_7'!='#skF_3' | '#skF_8'!='#skF_4'), inference(splitRight, [status(thm)], [c_32])).
% 9.28/3.25  tff(c_8619, plain, ('#skF_8'!='#skF_4'), inference(splitLeft, [status(thm)], [c_8613])).
% 9.28/3.25  tff(c_8631, plain, (![A_1124, B_1125, C_1126]: (k2_zfmisc_1(k2_zfmisc_1(A_1124, B_1125), C_1126)=k3_zfmisc_1(A_1124, B_1125, C_1126))), inference(cnfTransformation, [status(thm)], [f_33])).
% 9.28/3.25  tff(c_8634, plain, (![A_1124, B_1125, C_1126, C_5]: (k3_zfmisc_1(k2_zfmisc_1(A_1124, B_1125), C_1126, C_5)=k2_zfmisc_1(k3_zfmisc_1(A_1124, B_1125, C_1126), C_5))), inference(superposition, [status(thm), theory('equality')], [c_8631, c_8])).
% 9.28/3.25  tff(c_8842, plain, (![A_1124, B_1125, C_1126, C_5]: (k3_zfmisc_1(k2_zfmisc_1(A_1124, B_1125), C_1126, C_5)=k4_zfmisc_1(A_1124, B_1125, C_1126, C_5))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_8634])).
% 9.28/3.25  tff(c_9043, plain, (![D_1179, B_1176, F_1178, A_1177, E_1175, C_1174]: (F_1178=C_1174 | k3_zfmisc_1(A_1177, B_1176, C_1174)=k1_xboole_0 | k3_zfmisc_1(D_1179, E_1175, F_1178)!=k3_zfmisc_1(A_1177, B_1176, C_1174))), inference(cnfTransformation, [status(thm)], [f_71])).
% 9.28/3.25  tff(c_9348, plain, (![C_1216, B_1217, A_1214, C_1219, C_1218, A_1215, B_1213]: (C_1219=C_1216 | k3_zfmisc_1(A_1215, B_1217, C_1216)=k1_xboole_0 | k4_zfmisc_1(A_1214, B_1213, C_1218, C_1219)!=k3_zfmisc_1(A_1215, B_1217, C_1216))), inference(superposition, [status(thm), theory('equality')], [c_8842, c_9043])).
% 9.28/3.25  tff(c_9433, plain, (![C_1227, A_1228, B_1229]: (C_1227='#skF_8' | k3_zfmisc_1(A_1228, B_1229, C_1227)=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k3_zfmisc_1(A_1228, B_1229, C_1227))), inference(superposition, [status(thm), theory('equality')], [c_8667, c_9348])).
% 9.28/3.25  tff(c_9439, plain, (![C_5, A_1124, B_1125, C_1126]: (C_5='#skF_8' | k3_zfmisc_1(k2_zfmisc_1(A_1124, B_1125), C_1126, C_5)=k1_xboole_0 | k4_zfmisc_1(A_1124, B_1125, C_1126, C_5)!=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_8842, c_9433])).
% 9.28/3.25  tff(c_9450, plain, (![C_5, A_1124, B_1125, C_1126]: (C_5='#skF_8' | k4_zfmisc_1(A_1124, B_1125, C_1126, C_5)=k1_xboole_0 | k4_zfmisc_1(A_1124, B_1125, C_1126, C_5)!=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_8842, c_9439])).
% 9.28/3.25  tff(c_9478, plain, ('#skF_8'='#skF_4' | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')=k1_xboole_0), inference(reflexivity, [status(thm), theory('equality')], [c_9450])).
% 9.28/3.25  tff(c_9480, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8961, c_8619, c_9478])).
% 9.28/3.25  tff(c_9482, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_8952])).
% 9.28/3.25  tff(c_8697, plain, (![D_1133, A_1130, B_1131, C_1132]: (k1_xboole_0=D_1133 | k3_zfmisc_1(A_1130, B_1131, C_1132)=k1_xboole_0 | k4_zfmisc_1(A_1130, B_1131, C_1132, D_1133)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_8688, c_2])).
% 9.28/3.25  tff(c_9487, plain, (k1_xboole_0='#skF_4' | k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_9482, c_8697])).
% 9.28/3.25  tff(c_9492, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_34, c_9487])).
% 9.28/3.25  tff(c_9515, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_9492, c_12])).
% 9.28/3.25  tff(c_9527, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_38, c_36, c_9515])).
% 9.28/3.25  tff(c_9528, plain, ('#skF_7'!='#skF_3' | '#skF_6'!='#skF_2'), inference(splitRight, [status(thm)], [c_8613])).
% 9.28/3.25  tff(c_9534, plain, ('#skF_6'!='#skF_2'), inference(splitLeft, [status(thm)], [c_9528])).
% 9.28/3.25  tff(c_9546, plain, (![A_1235, B_1236, C_1237]: (k2_zfmisc_1(k2_zfmisc_1(A_1235, B_1236), C_1237)=k3_zfmisc_1(A_1235, B_1236, C_1237))), inference(cnfTransformation, [status(thm)], [f_33])).
% 9.28/3.25  tff(c_9549, plain, (![A_1235, B_1236, C_1237, C_5]: (k3_zfmisc_1(k2_zfmisc_1(A_1235, B_1236), C_1237, C_5)=k2_zfmisc_1(k3_zfmisc_1(A_1235, B_1236, C_1237), C_5))), inference(superposition, [status(thm), theory('equality')], [c_9546, c_8])).
% 9.28/3.25  tff(c_9757, plain, (![A_1235, B_1236, C_1237, C_5]: (k3_zfmisc_1(k2_zfmisc_1(A_1235, B_1236), C_1237, C_5)=k4_zfmisc_1(A_1235, B_1236, C_1237, C_5))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_9549])).
% 9.28/3.25  tff(c_9529, plain, ('#skF_8'='#skF_4'), inference(splitRight, [status(thm)], [c_8613])).
% 9.28/3.25  tff(c_9582, plain, (k4_zfmisc_1('#skF_1', '#skF_6', '#skF_7', '#skF_4')=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_9529, c_8614, c_42])).
% 9.28/3.25  tff(c_9603, plain, (![A_1241, B_1242, C_1243, D_1244]: (k2_zfmisc_1(k3_zfmisc_1(A_1241, B_1242, C_1243), D_1244)=k4_zfmisc_1(A_1241, B_1242, C_1243, D_1244))), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.28/3.25  tff(c_9852, plain, (![D_1276, A_1277, B_1278, C_1279]: (k1_xboole_0=D_1276 | k3_zfmisc_1(A_1277, B_1278, C_1279)=k1_xboole_0 | k4_zfmisc_1(A_1277, B_1278, C_1279, D_1276)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_9603, c_2])).
% 9.28/3.25  tff(c_9867, plain, (k1_xboole_0='#skF_4' | k3_zfmisc_1('#skF_1', '#skF_6', '#skF_7')=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_9582, c_9852])).
% 9.28/3.25  tff(c_9876, plain, (k3_zfmisc_1('#skF_1', '#skF_6', '#skF_7')=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_34, c_9867])).
% 9.28/3.25  tff(c_9877, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_9876])).
% 9.28/3.25  tff(c_9823, plain, (![A_1273, B_1272, E_1271, D_1275, C_1270, F_1274]: (E_1271=B_1272 | k3_zfmisc_1(A_1273, B_1272, C_1270)=k1_xboole_0 | k3_zfmisc_1(D_1275, E_1271, F_1274)!=k3_zfmisc_1(A_1273, B_1272, C_1270))), inference(cnfTransformation, [status(thm)], [f_71])).
% 9.28/3.25  tff(c_9829, plain, (![A_1235, E_1271, B_1236, C_1237, C_5, D_1275, F_1274]: (E_1271=C_1237 | k3_zfmisc_1(k2_zfmisc_1(A_1235, B_1236), C_1237, C_5)=k1_xboole_0 | k4_zfmisc_1(A_1235, B_1236, C_1237, C_5)!=k3_zfmisc_1(D_1275, E_1271, F_1274))), inference(superposition, [status(thm), theory('equality')], [c_9757, c_9823])).
% 9.28/3.25  tff(c_11648, plain, (![A_1453, D_1452, C_1458, C_1456, E_1457, F_1455, B_1454]: (E_1457=C_1458 | k4_zfmisc_1(A_1453, B_1454, C_1458, C_1456)=k1_xboole_0 | k4_zfmisc_1(A_1453, B_1454, C_1458, C_1456)!=k3_zfmisc_1(D_1452, E_1457, F_1455))), inference(demodulation, [status(thm), theory('equality')], [c_9757, c_9829])).
% 9.28/3.25  tff(c_11675, plain, (![E_1457, D_1452, F_1455]: (E_1457='#skF_7' | k4_zfmisc_1('#skF_1', '#skF_6', '#skF_7', '#skF_4')=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k3_zfmisc_1(D_1452, E_1457, F_1455))), inference(superposition, [status(thm), theory('equality')], [c_9582, c_11648])).
% 9.28/3.25  tff(c_11691, plain, (![E_1457, D_1452, F_1455]: (E_1457='#skF_7' | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k3_zfmisc_1(D_1452, E_1457, F_1455))), inference(demodulation, [status(thm), theory('equality')], [c_9582, c_11675])).
% 9.28/3.25  tff(c_11693, plain, (![E_1459, D_1460, F_1461]: (E_1459='#skF_7' | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k3_zfmisc_1(D_1460, E_1459, F_1461))), inference(negUnitSimplification, [status(thm)], [c_9877, c_11691])).
% 9.28/3.25  tff(c_11699, plain, (![C_1237, A_1235, B_1236, C_5]: (C_1237='#skF_7' | k4_zfmisc_1(A_1235, B_1236, C_1237, C_5)!=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_9757, c_11693])).
% 9.28/3.25  tff(c_11711, plain, ('#skF_7'='#skF_3'), inference(reflexivity, [status(thm), theory('equality')], [c_11699])).
% 9.28/3.25  tff(c_11739, plain, (k4_zfmisc_1('#skF_1', '#skF_6', '#skF_3', '#skF_4')=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_11711, c_9582])).
% 9.28/3.25  tff(c_9758, plain, (![A_1266, B_1267, C_1268, C_1269]: (k3_zfmisc_1(k2_zfmisc_1(A_1266, B_1267), C_1268, C_1269)=k4_zfmisc_1(A_1266, B_1267, C_1268, C_1269))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_9549])).
% 9.28/3.25  tff(c_9770, plain, (![C_1268, B_1267, A_1266, C_1269, D_22, F_24, E_23]: (k2_zfmisc_1(A_1266, B_1267)=D_22 | k3_zfmisc_1(k2_zfmisc_1(A_1266, B_1267), C_1268, C_1269)=k1_xboole_0 | k4_zfmisc_1(A_1266, B_1267, C_1268, C_1269)!=k3_zfmisc_1(D_22, E_23, F_24))), inference(superposition, [status(thm), theory('equality')], [c_9758, c_30])).
% 9.28/3.25  tff(c_12010, plain, (![D_1506, C_1505, F_1504, E_1501, A_1503, C_1502, B_1507]: (k2_zfmisc_1(A_1503, B_1507)=D_1506 | k4_zfmisc_1(A_1503, B_1507, C_1502, C_1505)=k1_xboole_0 | k4_zfmisc_1(A_1503, B_1507, C_1502, C_1505)!=k3_zfmisc_1(D_1506, E_1501, F_1504))), inference(demodulation, [status(thm), theory('equality')], [c_9757, c_9770])).
% 9.28/3.25  tff(c_12013, plain, (![D_1506, E_1501, F_1504]: (k2_zfmisc_1('#skF_1', '#skF_6')=D_1506 | k4_zfmisc_1('#skF_1', '#skF_6', '#skF_3', '#skF_4')=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k3_zfmisc_1(D_1506, E_1501, F_1504))), inference(superposition, [status(thm), theory('equality')], [c_11739, c_12010])).
% 9.28/3.25  tff(c_12047, plain, (![D_1506, E_1501, F_1504]: (k2_zfmisc_1('#skF_1', '#skF_6')=D_1506 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k3_zfmisc_1(D_1506, E_1501, F_1504))), inference(demodulation, [status(thm), theory('equality')], [c_11739, c_12013])).
% 9.28/3.25  tff(c_12055, plain, (![D_1508, E_1509, F_1510]: (k2_zfmisc_1('#skF_1', '#skF_6')=D_1508 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k3_zfmisc_1(D_1508, E_1509, F_1510))), inference(negUnitSimplification, [status(thm)], [c_9877, c_12047])).
% 9.28/3.25  tff(c_12061, plain, (![A_1235, B_1236, C_1237, C_5]: (k2_zfmisc_1(A_1235, B_1236)=k2_zfmisc_1('#skF_1', '#skF_6') | k4_zfmisc_1(A_1235, B_1236, C_1237, C_5)!=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_9757, c_12055])).
% 9.28/3.25  tff(c_12073, plain, (k2_zfmisc_1('#skF_1', '#skF_6')=k2_zfmisc_1('#skF_1', '#skF_2')), inference(reflexivity, [status(thm), theory('equality')], [c_12061])).
% 9.28/3.25  tff(c_12113, plain, (![C_5]: (k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'), C_5)=k3_zfmisc_1('#skF_1', '#skF_6', C_5))), inference(superposition, [status(thm), theory('equality')], [c_12073, c_8])).
% 9.28/3.25  tff(c_12126, plain, (![C_1515]: (k3_zfmisc_1('#skF_1', '#skF_6', C_1515)=k3_zfmisc_1('#skF_1', '#skF_2', C_1515))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_12113])).
% 9.28/3.25  tff(c_12180, plain, (![D_16, C_1515, E_17, F_18]: (D_16='#skF_1' | k1_xboole_0=C_1515 | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_1' | k3_zfmisc_1(D_16, E_17, F_18)!=k3_zfmisc_1('#skF_1', '#skF_2', C_1515))), inference(superposition, [status(thm), theory('equality')], [c_12126, c_24])).
% 9.28/3.25  tff(c_12238, plain, (![D_16, C_1515, E_17, F_18]: (D_16='#skF_1' | k1_xboole_0=C_1515 | k1_xboole_0='#skF_6' | k3_zfmisc_1(D_16, E_17, F_18)!=k3_zfmisc_1('#skF_1', '#skF_2', C_1515))), inference(negUnitSimplification, [status(thm)], [c_40, c_12180])).
% 9.28/3.25  tff(c_12408, plain, (k1_xboole_0='#skF_6'), inference(splitLeft, [status(thm)], [c_12238])).
% 9.28/3.25  tff(c_4, plain, (![A_1]: (k2_zfmisc_1(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.28/3.25  tff(c_12445, plain, (![A_1]: (k2_zfmisc_1(A_1, '#skF_6')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_12408, c_12408, c_4])).
% 9.28/3.25  tff(c_12455, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_12445, c_12073])).
% 9.28/3.25  tff(c_12116, plain, (k1_xboole_0='#skF_6' | k1_xboole_0='#skF_1' | k2_zfmisc_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_12073, c_2])).
% 9.28/3.25  tff(c_12122, plain, (k1_xboole_0='#skF_6' | k2_zfmisc_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_40, c_12116])).
% 9.28/3.25  tff(c_12124, plain, (k2_zfmisc_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_12122])).
% 9.28/3.25  tff(c_12413, plain, (k2_zfmisc_1('#skF_1', '#skF_2')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_12408, c_12124])).
% 9.28/3.25  tff(c_12559, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12455, c_12413])).
% 9.28/3.25  tff(c_12561, plain, (k1_xboole_0!='#skF_6'), inference(splitRight, [status(thm)], [c_12238])).
% 9.28/3.25  tff(c_22, plain, (![E_17, F_18, A_13, B_14, C_15, D_16]: (E_17=B_14 | k1_xboole_0=C_15 | k1_xboole_0=B_14 | k1_xboole_0=A_13 | k3_zfmisc_1(D_16, E_17, F_18)!=k3_zfmisc_1(A_13, B_14, C_15))), inference(cnfTransformation, [status(thm)], [f_61])).
% 9.28/3.25  tff(c_12186, plain, (![E_17, C_1515, D_16, F_18]: (E_17='#skF_6' | k1_xboole_0=C_1515 | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_1' | k3_zfmisc_1(D_16, E_17, F_18)!=k3_zfmisc_1('#skF_1', '#skF_2', C_1515))), inference(superposition, [status(thm), theory('equality')], [c_12126, c_22])).
% 9.28/3.25  tff(c_12239, plain, (![E_17, C_1515, D_16, F_18]: (E_17='#skF_6' | k1_xboole_0=C_1515 | k1_xboole_0='#skF_6' | k3_zfmisc_1(D_16, E_17, F_18)!=k3_zfmisc_1('#skF_1', '#skF_2', C_1515))), inference(negUnitSimplification, [status(thm)], [c_40, c_12186])).
% 9.28/3.25  tff(c_12667, plain, (![E_17, C_1515, D_16, F_18]: (E_17='#skF_6' | k1_xboole_0=C_1515 | k3_zfmisc_1(D_16, E_17, F_18)!=k3_zfmisc_1('#skF_1', '#skF_2', C_1515))), inference(negUnitSimplification, [status(thm)], [c_12561, c_12239])).
% 9.28/3.25  tff(c_12670, plain, (![C_1515]: ('#skF_6'='#skF_2' | k1_xboole_0=C_1515)), inference(reflexivity, [status(thm), theory('equality')], [c_12667])).
% 9.28/3.25  tff(c_12698, plain, (![C_1550]: (k1_xboole_0=C_1550)), inference(negUnitSimplification, [status(thm)], [c_9534, c_12670])).
% 9.28/3.25  tff(c_12121, plain, (![C_5]: (k3_zfmisc_1('#skF_1', '#skF_6', C_5)=k3_zfmisc_1('#skF_1', '#skF_2', C_5))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_12113])).
% 9.28/3.25  tff(c_9878, plain, (![B_1282, A_1280, C_1281, D_1283, C_1284]: (k3_zfmisc_1(k3_zfmisc_1(A_1280, B_1282, C_1281), D_1283, C_1284)=k2_zfmisc_1(k4_zfmisc_1(A_1280, B_1282, C_1281, D_1283), C_1284))), inference(superposition, [status(thm), theory('equality')], [c_9603, c_8])).
% 9.28/3.25  tff(c_10489, plain, (![C_1363, D_1362, A_1361, C_1360, B_1364]: (k2_zfmisc_1(k4_zfmisc_1(A_1361, B_1364, C_1363, D_1362), C_1360)!=k1_xboole_0 | k1_xboole_0=C_1360 | k1_xboole_0=D_1362 | k3_zfmisc_1(A_1361, B_1364, C_1363)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_9878, c_12])).
% 9.28/3.25  tff(c_10510, plain, (![C_1360]: (k2_zfmisc_1(k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), C_1360)!=k1_xboole_0 | k1_xboole_0=C_1360 | k1_xboole_0='#skF_4' | k3_zfmisc_1('#skF_1', '#skF_6', '#skF_7')=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_9582, c_10489])).
% 9.28/3.25  tff(c_10526, plain, (![C_1360]: (k2_zfmisc_1(k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), C_1360)!=k1_xboole_0 | k1_xboole_0=C_1360 | k3_zfmisc_1('#skF_1', '#skF_6', '#skF_7')=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_34, c_10510])).
% 9.28/3.25  tff(c_10569, plain, (k3_zfmisc_1('#skF_1', '#skF_6', '#skF_7')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_10526])).
% 9.28/3.25  tff(c_10621, plain, (k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_10569, c_12])).
% 9.28/3.25  tff(c_10636, plain, (k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_40, c_10621])).
% 9.28/3.25  tff(c_10638, plain, (k1_xboole_0='#skF_6'), inference(splitLeft, [status(thm)], [c_10636])).
% 9.28/3.25  tff(c_10652, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_10638, c_9877])).
% 9.28/3.25  tff(c_10618, plain, (![D_9]: (k4_zfmisc_1('#skF_1', '#skF_6', '#skF_7', D_9)=k2_zfmisc_1(k1_xboole_0, D_9))), inference(superposition, [status(thm), theory('equality')], [c_10569, c_10])).
% 9.28/3.25  tff(c_10633, plain, (![D_9]: (k4_zfmisc_1('#skF_1', '#skF_6', '#skF_7', D_9)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_10618])).
% 9.28/3.25  tff(c_10923, plain, (![D_9]: (k4_zfmisc_1('#skF_1', '#skF_6', '#skF_7', D_9)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_10638, c_10633])).
% 9.28/3.25  tff(c_10924, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_10923, c_9582])).
% 9.28/3.25  tff(c_11191, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10652, c_10924])).
% 9.28/3.25  tff(c_11192, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_10636])).
% 9.28/3.25  tff(c_11495, plain, (![D_9]: (k4_zfmisc_1('#skF_1', '#skF_6', '#skF_7', D_9)='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_11192, c_10633])).
% 9.28/3.25  tff(c_11496, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_11495, c_9582])).
% 9.28/3.25  tff(c_11206, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_11192, c_9877])).
% 9.28/3.25  tff(c_11598, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_11496, c_11206])).
% 9.28/3.25  tff(c_11600, plain, (k3_zfmisc_1('#skF_1', '#skF_6', '#skF_7')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_10526])).
% 9.28/3.25  tff(c_11738, plain, (k3_zfmisc_1('#skF_1', '#skF_6', '#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_11711, c_11600])).
% 9.28/3.25  tff(c_12125, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_12121, c_11738])).
% 9.28/3.25  tff(c_12813, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_12698, c_12125])).
% 9.28/3.25  tff(c_12814, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_12122])).
% 9.28/3.25  tff(c_12846, plain, (![A_10, C_12]: (k3_zfmisc_1(A_10, '#skF_6', C_12)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_12814, c_12814, c_16])).
% 9.28/3.25  tff(c_12820, plain, (k3_zfmisc_1('#skF_1', '#skF_6', '#skF_3')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_12814, c_11738])).
% 9.28/3.25  tff(c_12961, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12846, c_12820])).
% 9.28/3.25  tff(c_12962, plain, (k3_zfmisc_1('#skF_1', '#skF_6', '#skF_7')=k1_xboole_0), inference(splitRight, [status(thm)], [c_9876])).
% 9.28/3.25  tff(c_12985, plain, (k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_12962, c_12])).
% 9.28/3.25  tff(c_12994, plain, (k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_40, c_12985])).
% 9.28/3.25  tff(c_12996, plain, (k1_xboole_0='#skF_6'), inference(splitLeft, [status(thm)], [c_12994])).
% 9.28/3.25  tff(c_13057, plain, ('#skF_6'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_12996, c_40])).
% 9.28/3.25  tff(c_13056, plain, ('#skF_6'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_12996, c_36])).
% 9.28/3.25  tff(c_13055, plain, ('#skF_6'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_12996, c_34])).
% 9.28/3.25  tff(c_12963, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_9876])).
% 9.28/3.25  tff(c_13223, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_12996, c_12963])).
% 9.28/3.25  tff(c_9555, plain, (![C_1237, A_1235, B_1236]: (k1_xboole_0=C_1237 | k2_zfmisc_1(A_1235, B_1236)=k1_xboole_0 | k3_zfmisc_1(A_1235, B_1236, C_1237)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_9546, c_2])).
% 9.28/3.25  tff(c_9764, plain, (![C_1269, A_1266, B_1267, C_1268]: (k1_xboole_0=C_1269 | k2_zfmisc_1(k2_zfmisc_1(A_1266, B_1267), C_1268)=k1_xboole_0 | k4_zfmisc_1(A_1266, B_1267, C_1268, C_1269)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_9758, c_9555])).
% 9.28/3.25  tff(c_9809, plain, (![C_1269, A_1266, B_1267, C_1268]: (k1_xboole_0=C_1269 | k3_zfmisc_1(A_1266, B_1267, C_1268)=k1_xboole_0 | k4_zfmisc_1(A_1266, B_1267, C_1268, C_1269)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_9764])).
% 9.28/3.25  tff(c_13533, plain, (![C_1880, A_1881, B_1882, C_1883]: (C_1880='#skF_6' | k3_zfmisc_1(A_1881, B_1882, C_1883)='#skF_6' | k4_zfmisc_1(A_1881, B_1882, C_1883, C_1880)!='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_12996, c_12996, c_12996, c_9809])).
% 9.28/3.25  tff(c_13548, plain, ('#skF_6'='#skF_4' | k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_13223, c_13533])).
% 9.28/3.25  tff(c_13559, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_13055, c_13548])).
% 9.28/3.25  tff(c_13047, plain, (![A_10, B_11, C_12]: (k3_zfmisc_1(A_10, B_11, C_12)!='#skF_6' | C_12='#skF_6' | B_11='#skF_6' | A_10='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_12996, c_12996, c_12996, c_12996, c_12])).
% 9.28/3.25  tff(c_13569, plain, ('#skF_6'='#skF_3' | '#skF_6'='#skF_2' | '#skF_6'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_13559, c_13047])).
% 9.28/3.25  tff(c_13600, plain, $false, inference(negUnitSimplification, [status(thm)], [c_13057, c_9534, c_13056, c_13569])).
% 9.28/3.25  tff(c_13601, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_12994])).
% 9.28/3.25  tff(c_13622, plain, ('#skF_7'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_13601, c_40])).
% 9.28/3.25  tff(c_13619, plain, ('#skF_7'!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_13601, c_38])).
% 9.28/3.25  tff(c_13621, plain, ('#skF_7'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_13601, c_36])).
% 9.28/3.25  tff(c_13620, plain, ('#skF_7'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_13601, c_34])).
% 9.28/3.25  tff(c_13719, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_13601, c_12963])).
% 9.28/3.25  tff(c_14076, plain, (![C_1937, A_1938, B_1939, C_1940]: (C_1937='#skF_7' | k3_zfmisc_1(A_1938, B_1939, C_1940)='#skF_7' | k4_zfmisc_1(A_1938, B_1939, C_1940, C_1937)!='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_13601, c_13601, c_13601, c_9809])).
% 9.28/3.25  tff(c_14091, plain, ('#skF_7'='#skF_4' | k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_13719, c_14076])).
% 9.28/3.25  tff(c_14102, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_13620, c_14091])).
% 9.28/3.25  tff(c_13612, plain, (![A_10, B_11, C_12]: (k3_zfmisc_1(A_10, B_11, C_12)!='#skF_7' | C_12='#skF_7' | B_11='#skF_7' | A_10='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_13601, c_13601, c_13601, c_13601, c_12])).
% 9.28/3.25  tff(c_14109, plain, ('#skF_7'='#skF_3' | '#skF_7'='#skF_2' | '#skF_7'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_14102, c_13612])).
% 9.28/3.25  tff(c_14145, plain, $false, inference(negUnitSimplification, [status(thm)], [c_13622, c_13619, c_13621, c_14109])).
% 9.28/3.25  tff(c_14146, plain, ('#skF_7'!='#skF_3'), inference(splitRight, [status(thm)], [c_9528])).
% 9.28/3.25  tff(c_14163, plain, (![A_1943, B_1944, C_1945]: (k2_zfmisc_1(k2_zfmisc_1(A_1943, B_1944), C_1945)=k3_zfmisc_1(A_1943, B_1944, C_1945))), inference(cnfTransformation, [status(thm)], [f_33])).
% 9.28/3.25  tff(c_14179, plain, (![A_3, B_4, C_5, C_1945]: (k3_zfmisc_1(k2_zfmisc_1(A_3, B_4), C_5, C_1945)=k2_zfmisc_1(k3_zfmisc_1(A_3, B_4, C_5), C_1945))), inference(superposition, [status(thm), theory('equality')], [c_8, c_14163])).
% 9.28/3.25  tff(c_14348, plain, (![A_3, B_4, C_5, C_1945]: (k3_zfmisc_1(k2_zfmisc_1(A_3, B_4), C_5, C_1945)=k4_zfmisc_1(A_3, B_4, C_5, C_1945))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_14179])).
% 9.28/3.25  tff(c_14147, plain, ('#skF_6'='#skF_2'), inference(splitRight, [status(thm)], [c_9528])).
% 9.28/3.25  tff(c_14199, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_7', '#skF_4')=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_14147, c_8614, c_9529, c_42])).
% 9.28/3.25  tff(c_14204, plain, (![A_1946, B_1947, C_1948, D_1949]: (k2_zfmisc_1(k3_zfmisc_1(A_1946, B_1947, C_1948), D_1949)=k4_zfmisc_1(A_1946, B_1947, C_1948, D_1949))), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.28/3.25  tff(c_14436, plain, (![D_1978, A_1979, B_1980, C_1981]: (k1_xboole_0=D_1978 | k3_zfmisc_1(A_1979, B_1980, C_1981)=k1_xboole_0 | k4_zfmisc_1(A_1979, B_1980, C_1981, D_1978)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_14204, c_2])).
% 9.28/3.25  tff(c_14451, plain, (k1_xboole_0='#skF_4' | k3_zfmisc_1('#skF_1', '#skF_2', '#skF_7')=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_14199, c_14436])).
% 9.28/3.25  tff(c_14460, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_7')=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_34, c_14451])).
% 9.28/3.25  tff(c_14461, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_14460])).
% 9.28/3.25  tff(c_14466, plain, (![A_1985, E_1983, D_1987, F_1986, B_1984, C_1982]: (E_1983=B_1984 | k3_zfmisc_1(A_1985, B_1984, C_1982)=k1_xboole_0 | k3_zfmisc_1(D_1987, E_1983, F_1986)!=k3_zfmisc_1(A_1985, B_1984, C_1982))), inference(cnfTransformation, [status(thm)], [f_71])).
% 9.28/3.25  tff(c_14472, plain, (![A_3, E_1983, D_1987, F_1986, C_5, C_1945, B_4]: (E_1983=C_5 | k3_zfmisc_1(k2_zfmisc_1(A_3, B_4), C_5, C_1945)=k1_xboole_0 | k4_zfmisc_1(A_3, B_4, C_5, C_1945)!=k3_zfmisc_1(D_1987, E_1983, F_1986))), inference(superposition, [status(thm), theory('equality')], [c_14348, c_14466])).
% 9.28/3.25  tff(c_15185, plain, (![A_2085, D_2082, E_2083, C_2087, F_2084, C_2086, B_2088]: (E_2083=C_2087 | k4_zfmisc_1(A_2085, B_2088, C_2087, C_2086)=k1_xboole_0 | k4_zfmisc_1(A_2085, B_2088, C_2087, C_2086)!=k3_zfmisc_1(D_2082, E_2083, F_2084))), inference(demodulation, [status(thm), theory('equality')], [c_14348, c_14472])).
% 9.28/3.25  tff(c_15212, plain, (![E_2083, D_2082, F_2084]: (E_2083='#skF_7' | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_7', '#skF_4')=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k3_zfmisc_1(D_2082, E_2083, F_2084))), inference(superposition, [status(thm), theory('equality')], [c_14199, c_15185])).
% 9.28/3.25  tff(c_15228, plain, (![E_2083, D_2082, F_2084]: (E_2083='#skF_7' | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')=k1_xboole_0 | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k3_zfmisc_1(D_2082, E_2083, F_2084))), inference(demodulation, [status(thm), theory('equality')], [c_14199, c_15212])).
% 9.28/3.25  tff(c_15230, plain, (![E_2089, D_2090, F_2091]: (E_2089='#skF_7' | k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k3_zfmisc_1(D_2090, E_2089, F_2091))), inference(negUnitSimplification, [status(thm)], [c_14461, c_15228])).
% 9.28/3.25  tff(c_15236, plain, (![C_5, A_3, B_4, C_1945]: (C_5='#skF_7' | k4_zfmisc_1(A_3, B_4, C_5, C_1945)!=k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_14348, c_15230])).
% 9.28/3.25  tff(c_15248, plain, ('#skF_7'='#skF_3'), inference(reflexivity, [status(thm), theory('equality')], [c_15236])).
% 9.28/3.25  tff(c_15250, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14146, c_15248])).
% 9.28/3.25  tff(c_15251, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_7')=k1_xboole_0), inference(splitRight, [status(thm)], [c_14460])).
% 9.28/3.25  tff(c_15265, plain, (k1_xboole_0='#skF_7' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_15251, c_12])).
% 9.28/3.25  tff(c_15275, plain, (k1_xboole_0='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_40, c_38, c_15265])).
% 9.28/3.25  tff(c_15296, plain, ('#skF_7'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_15275, c_40])).
% 9.28/3.25  tff(c_15293, plain, ('#skF_7'!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_15275, c_38])).
% 9.28/3.25  tff(c_15294, plain, ('#skF_7'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_15275, c_34])).
% 9.28/3.25  tff(c_15252, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_14460])).
% 9.28/3.25  tff(c_15366, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_15275, c_15252])).
% 9.28/3.25  tff(c_14349, plain, (![A_1968, B_1969, C_1970, C_1971]: (k3_zfmisc_1(k2_zfmisc_1(A_1968, B_1969), C_1970, C_1971)=k4_zfmisc_1(A_1968, B_1969, C_1970, C_1971))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_14179])).
% 9.28/3.25  tff(c_14172, plain, (![C_1945, A_1943, B_1944]: (k1_xboole_0=C_1945 | k2_zfmisc_1(A_1943, B_1944)=k1_xboole_0 | k3_zfmisc_1(A_1943, B_1944, C_1945)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_14163, c_2])).
% 9.28/3.25  tff(c_14355, plain, (![C_1971, A_1968, B_1969, C_1970]: (k1_xboole_0=C_1971 | k2_zfmisc_1(k2_zfmisc_1(A_1968, B_1969), C_1970)=k1_xboole_0 | k4_zfmisc_1(A_1968, B_1969, C_1970, C_1971)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_14349, c_14172])).
% 9.28/3.25  tff(c_14394, plain, (![C_1971, A_1968, B_1969, C_1970]: (k1_xboole_0=C_1971 | k3_zfmisc_1(A_1968, B_1969, C_1970)=k1_xboole_0 | k4_zfmisc_1(A_1968, B_1969, C_1970, C_1971)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_14355])).
% 9.28/3.25  tff(c_15882, plain, (![C_2156, A_2157, B_2158, C_2159]: (C_2156='#skF_7' | k3_zfmisc_1(A_2157, B_2158, C_2159)='#skF_7' | k4_zfmisc_1(A_2157, B_2158, C_2159, C_2156)!='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_15275, c_15275, c_15275, c_14394])).
% 9.28/3.25  tff(c_15897, plain, ('#skF_7'='#skF_4' | k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_15366, c_15882])).
% 9.28/3.25  tff(c_15908, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_15294, c_15897])).
% 9.28/3.25  tff(c_15283, plain, (![A_10, B_11, C_12]: (k3_zfmisc_1(A_10, B_11, C_12)!='#skF_7' | C_12='#skF_7' | B_11='#skF_7' | A_10='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_15275, c_15275, c_15275, c_15275, c_12])).
% 9.28/3.25  tff(c_15915, plain, ('#skF_7'='#skF_3' | '#skF_7'='#skF_2' | '#skF_7'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_15908, c_15283])).
% 9.28/3.25  tff(c_15958, plain, $false, inference(negUnitSimplification, [status(thm)], [c_15296, c_15293, c_14146, c_15915])).
% 9.28/3.25  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.28/3.25  
% 9.28/3.25  Inference rules
% 9.28/3.25  ----------------------
% 9.28/3.25  #Ref     : 64
% 9.28/3.25  #Sup     : 3926
% 9.28/3.25  #Fact    : 0
% 9.28/3.25  #Define  : 0
% 9.28/3.25  #Split   : 31
% 9.28/3.25  #Chain   : 0
% 9.28/3.25  #Close   : 0
% 9.28/3.25  
% 9.28/3.25  Ordering : KBO
% 9.28/3.25  
% 9.28/3.25  Simplification rules
% 9.28/3.25  ----------------------
% 9.28/3.25  #Subsume      : 904
% 9.28/3.25  #Demod        : 3539
% 9.28/3.25  #Tautology    : 2030
% 9.28/3.25  #SimpNegUnit  : 198
% 9.28/3.25  #BackRed      : 773
% 9.28/3.25  
% 9.28/3.25  #Partial instantiations: 488
% 9.28/3.25  #Strategies tried      : 1
% 9.28/3.25  
% 9.28/3.25  Timing (in seconds)
% 9.28/3.25  ----------------------
% 9.28/3.26  Preprocessing        : 0.31
% 9.28/3.26  Parsing              : 0.17
% 9.28/3.26  CNF conversion       : 0.02
% 9.28/3.26  Main loop            : 2.01
% 9.28/3.26  Inferencing          : 0.62
% 9.28/3.26  Reduction            : 0.64
% 9.28/3.26  Demodulation         : 0.44
% 9.28/3.26  BG Simplification    : 0.07
% 9.28/3.26  Subsumption          : 0.55
% 9.28/3.26  Abstraction          : 0.12
% 9.28/3.26  MUC search           : 0.00
% 9.28/3.26  Cooper               : 0.00
% 9.28/3.26  Total                : 2.45
% 9.28/3.26  Index Insertion      : 0.00
% 9.28/3.26  Index Deletion       : 0.00
% 9.28/3.26  Index Matching       : 0.00
% 9.28/3.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
