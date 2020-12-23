%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:40 EST 2020

% Result     : Theorem 7.76s
% Output     : CNFRefutation 8.22s
% Verified   : 
% Statistics : Number of formulae       :  361 (3460 expanded)
%              Number of leaves         :   38 (1063 expanded)
%              Depth                    :   20
%              Number of atoms          :  555 (6906 expanded)
%              Number of equality atoms :  205 (3718 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_xboole_0 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k3_tarski > k1_xboole_0 > #skF_11 > #skF_6 > #skF_15 > #skF_1 > #skF_12 > #skF_4 > #skF_8 > #skF_16 > #skF_14 > #skF_13 > #skF_5 > #skF_10 > #skF_7 > #skF_3 > #skF_2 > #skF_9

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_11',type,(
    '#skF_11': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_15',type,(
    '#skF_15': $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_12',type,(
    '#skF_12': ( $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i * $i ) > $i )).

tff('#skF_16',type,(
    '#skF_16': $i )).

tff('#skF_14',type,(
    '#skF_14': $i )).

tff('#skF_13',type,(
    '#skF_13': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i ) > $i )).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( C = k2_zfmisc_1(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E,F] :
              ( r2_hidden(E,A)
              & r2_hidden(F,B)
              & D = k4_tarski(E,F) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_39,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_49,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_43,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_80,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_zfmisc_1(A,B) = k1_xboole_0
      <=> ( A = k1_xboole_0
          | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( B = k3_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] :
              ( r2_hidden(C,D)
              & r2_hidden(D,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tarski)).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_2'(A_5,B_6),A_5)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_18650,plain,(
    ! [A_1194,B_1195,D_1196] :
      ( r2_hidden('#skF_8'(A_1194,B_1195,k2_zfmisc_1(A_1194,B_1195),D_1196),B_1195)
      | ~ r2_hidden(D_1196,k2_zfmisc_1(A_1194,B_1195)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_30,plain,(
    ! [A_17,B_18,D_44] :
      ( r2_hidden('#skF_7'(A_17,B_18,k2_zfmisc_1(A_17,B_18),D_44),A_17)
      | ~ r2_hidden(D_44,k2_zfmisc_1(A_17,B_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_15238,plain,(
    ! [A_956,B_957,D_958] :
      ( r2_hidden('#skF_8'(A_956,B_957,k2_zfmisc_1(A_956,B_957),D_958),B_957)
      | ~ r2_hidden(D_958,k2_zfmisc_1(A_956,B_957)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_20,plain,(
    ! [A_14] : k4_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_112,plain,(
    ! [A_82,B_83] :
      ( r1_tarski(A_82,B_83)
      | k4_xboole_0(A_82,B_83) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_18,plain,(
    ! [A_12,B_13] :
      ( k2_xboole_0(A_12,B_13) = B_13
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_4582,plain,(
    ! [A_413,B_414] :
      ( k2_xboole_0(A_413,B_414) = B_414
      | k4_xboole_0(A_413,B_414) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_112,c_18])).

tff(c_4601,plain,(
    ! [A_415] :
      ( k2_xboole_0(A_415,k1_xboole_0) = k1_xboole_0
      | k1_xboole_0 != A_415 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_4582])).

tff(c_22,plain,(
    ! [A_15,B_16] : r1_tarski(A_15,k2_xboole_0(A_15,B_16)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_4618,plain,(
    ! [A_415] :
      ( r1_tarski(A_415,k1_xboole_0)
      | k1_xboole_0 != A_415 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4601,c_22])).

tff(c_4507,plain,(
    ! [C_404,B_405,A_406] :
      ( r2_hidden(C_404,B_405)
      | ~ r2_hidden(C_404,A_406)
      | ~ r1_tarski(A_406,B_405) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_4711,plain,(
    ! [A_421,B_422] :
      ( r2_hidden('#skF_1'(A_421),B_422)
      | ~ r1_tarski(A_421,B_422)
      | v1_xboole_0(A_421) ) ),
    inference(resolution,[status(thm)],[c_4,c_4507])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4722,plain,(
    ! [B_423,A_424] :
      ( ~ v1_xboole_0(B_423)
      | ~ r1_tarski(A_424,B_423)
      | v1_xboole_0(A_424) ) ),
    inference(resolution,[status(thm)],[c_4711,c_2])).

tff(c_4725,plain,(
    ! [A_415] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | v1_xboole_0(A_415)
      | k1_xboole_0 != A_415 ) ),
    inference(resolution,[status(thm)],[c_4618,c_4722])).

tff(c_4750,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_4725])).

tff(c_4046,plain,(
    ! [A_369,B_370,D_371] :
      ( r2_hidden('#skF_7'(A_369,B_370,k2_zfmisc_1(A_369,B_370),D_371),A_369)
      | ~ r2_hidden(D_371,k2_zfmisc_1(A_369,B_370)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_28,plain,(
    ! [A_17,B_18,D_44] :
      ( r2_hidden('#skF_8'(A_17,B_18,k2_zfmisc_1(A_17,B_18),D_44),B_18)
      | ~ r2_hidden(D_44,k2_zfmisc_1(A_17,B_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_66,plain,
    ( k2_zfmisc_1('#skF_13','#skF_14') != k1_xboole_0
    | k1_xboole_0 != '#skF_16' ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_89,plain,(
    k1_xboole_0 != '#skF_16' ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_70,plain,
    ( k2_zfmisc_1('#skF_13','#skF_14') != k1_xboole_0
    | k1_xboole_0 != '#skF_15' ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_88,plain,(
    k1_xboole_0 != '#skF_15' ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_325,plain,(
    ! [A_108,B_109] :
      ( k2_xboole_0(A_108,B_109) = B_109
      | k4_xboole_0(A_108,B_109) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_112,c_18])).

tff(c_345,plain,(
    ! [A_110] :
      ( k2_xboole_0(A_110,k1_xboole_0) = k1_xboole_0
      | k1_xboole_0 != A_110 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_325])).

tff(c_365,plain,(
    ! [A_110] :
      ( r1_tarski(A_110,k1_xboole_0)
      | k1_xboole_0 != A_110 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_345,c_22])).

tff(c_190,plain,(
    ! [C_93,B_94,A_95] :
      ( r2_hidden(C_93,B_94)
      | ~ r2_hidden(C_93,A_95)
      | ~ r1_tarski(A_95,B_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_411,plain,(
    ! [A_114,B_115] :
      ( r2_hidden('#skF_1'(A_114),B_115)
      | ~ r1_tarski(A_114,B_115)
      | v1_xboole_0(A_114) ) ),
    inference(resolution,[status(thm)],[c_4,c_190])).

tff(c_422,plain,(
    ! [B_116,A_117] :
      ( ~ v1_xboole_0(B_116)
      | ~ r1_tarski(A_117,B_116)
      | v1_xboole_0(A_117) ) ),
    inference(resolution,[status(thm)],[c_411,c_2])).

tff(c_425,plain,(
    ! [A_110] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | v1_xboole_0(A_110)
      | k1_xboole_0 != A_110 ) ),
    inference(resolution,[status(thm)],[c_365,c_422])).

tff(c_461,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_425])).

tff(c_76,plain,
    ( k1_xboole_0 = '#skF_14'
    | k1_xboole_0 = '#skF_13'
    | k2_zfmisc_1('#skF_15','#skF_16') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_122,plain,(
    k2_zfmisc_1('#skF_15','#skF_16') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_76])).

tff(c_531,plain,(
    ! [E_128,F_129,A_130,B_131] :
      ( r2_hidden(k4_tarski(E_128,F_129),k2_zfmisc_1(A_130,B_131))
      | ~ r2_hidden(F_129,B_131)
      | ~ r2_hidden(E_128,A_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_639,plain,(
    ! [E_138,F_139] :
      ( r2_hidden(k4_tarski(E_138,F_139),k1_xboole_0)
      | ~ r2_hidden(F_139,'#skF_16')
      | ~ r2_hidden(E_138,'#skF_15') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_122,c_531])).

tff(c_646,plain,(
    ! [F_139,E_138] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(F_139,'#skF_16')
      | ~ r2_hidden(E_138,'#skF_15') ) ),
    inference(resolution,[status(thm)],[c_639,c_2])).

tff(c_653,plain,(
    ! [F_139,E_138] :
      ( ~ r2_hidden(F_139,'#skF_16')
      | ~ r2_hidden(E_138,'#skF_15') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_461,c_646])).

tff(c_670,plain,(
    ! [E_142] : ~ r2_hidden(E_142,'#skF_15') ),
    inference(splitLeft,[status(thm)],[c_653])).

tff(c_697,plain,(
    ! [B_143] : r1_tarski('#skF_15',B_143) ),
    inference(resolution,[status(thm)],[c_10,c_670])).

tff(c_16,plain,(
    ! [A_10,B_11] :
      ( k4_xboole_0(A_10,B_11) = k1_xboole_0
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_786,plain,(
    ! [B_147] : k4_xboole_0('#skF_15',B_147) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_697,c_16])).

tff(c_804,plain,(
    k1_xboole_0 = '#skF_15' ),
    inference(superposition,[status(thm),theory(equality)],[c_786,c_20])).

tff(c_826,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_804])).

tff(c_849,plain,(
    ! [F_151] : ~ r2_hidden(F_151,'#skF_16') ),
    inference(splitRight,[status(thm)],[c_653])).

tff(c_876,plain,(
    ! [B_152] : r1_tarski('#skF_16',B_152) ),
    inference(resolution,[status(thm)],[c_10,c_849])).

tff(c_997,plain,(
    ! [B_157] : k4_xboole_0('#skF_16',B_157) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_876,c_16])).

tff(c_1015,plain,(
    k1_xboole_0 = '#skF_16' ),
    inference(superposition,[status(thm),theory(equality)],[c_997,c_20])).

tff(c_1038,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_89,c_1015])).

tff(c_1039,plain,
    ( k1_xboole_0 = '#skF_13'
    | k1_xboole_0 = '#skF_14' ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_1041,plain,(
    k1_xboole_0 = '#skF_14' ),
    inference(splitLeft,[status(thm)],[c_1039])).

tff(c_1050,plain,(
    v1_xboole_0('#skF_14') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1041,c_12])).

tff(c_1049,plain,(
    ! [A_14] : k4_xboole_0(A_14,'#skF_14') = A_14 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1041,c_20])).

tff(c_120,plain,(
    ! [A_82,B_83] :
      ( k2_xboole_0(A_82,B_83) = B_83
      | k4_xboole_0(A_82,B_83) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_112,c_18])).

tff(c_1278,plain,(
    ! [A_186,B_187] :
      ( k2_xboole_0(A_186,B_187) = B_187
      | k4_xboole_0(A_186,B_187) != '#skF_14' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1041,c_120])).

tff(c_1305,plain,(
    ! [A_191] :
      ( k2_xboole_0(A_191,'#skF_14') = '#skF_14'
      | A_191 != '#skF_14' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1049,c_1278])).

tff(c_1325,plain,(
    ! [A_191] :
      ( r1_tarski(A_191,'#skF_14')
      | A_191 != '#skF_14' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1305,c_22])).

tff(c_1175,plain,(
    ! [C_179,B_180,A_181] :
      ( r2_hidden(C_179,B_180)
      | ~ r2_hidden(C_179,A_181)
      | ~ r1_tarski(A_181,B_180) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1371,plain,(
    ! [A_195,B_196] :
      ( r2_hidden('#skF_1'(A_195),B_196)
      | ~ r1_tarski(A_195,B_196)
      | v1_xboole_0(A_195) ) ),
    inference(resolution,[status(thm)],[c_4,c_1175])).

tff(c_1382,plain,(
    ! [B_197,A_198] :
      ( ~ v1_xboole_0(B_197)
      | ~ r1_tarski(A_198,B_197)
      | v1_xboole_0(A_198) ) ),
    inference(resolution,[status(thm)],[c_1371,c_2])).

tff(c_1385,plain,(
    ! [A_191] :
      ( ~ v1_xboole_0('#skF_14')
      | v1_xboole_0(A_191)
      | A_191 != '#skF_14' ) ),
    inference(resolution,[status(thm)],[c_1325,c_1382])).

tff(c_1403,plain,(
    ! [A_191] :
      ( v1_xboole_0(A_191)
      | A_191 != '#skF_14' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1050,c_1385])).

tff(c_1478,plain,(
    ! [A_204,C_205] :
      ( r2_hidden('#skF_12'(A_204,k3_tarski(A_204),C_205),A_204)
      | ~ r2_hidden(C_205,k3_tarski(A_204)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1489,plain,(
    ! [A_206,C_207] :
      ( ~ v1_xboole_0(A_206)
      | ~ r2_hidden(C_207,k3_tarski(A_206)) ) ),
    inference(resolution,[status(thm)],[c_1478,c_2])).

tff(c_1517,plain,(
    ! [A_209,B_210] :
      ( ~ v1_xboole_0(A_209)
      | r1_tarski(k3_tarski(A_209),B_210) ) ),
    inference(resolution,[status(thm)],[c_10,c_1489])).

tff(c_1046,plain,(
    ! [A_10,B_11] :
      ( k4_xboole_0(A_10,B_11) = '#skF_14'
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1041,c_16])).

tff(c_1761,plain,(
    ! [A_232,B_233] :
      ( k4_xboole_0(k3_tarski(A_232),B_233) = '#skF_14'
      | ~ v1_xboole_0(A_232) ) ),
    inference(resolution,[status(thm)],[c_1517,c_1046])).

tff(c_1807,plain,(
    ! [A_234] :
      ( k3_tarski(A_234) = '#skF_14'
      | ~ v1_xboole_0(A_234) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1761,c_1049])).

tff(c_1820,plain,(
    k3_tarski('#skF_14') = '#skF_14' ),
    inference(resolution,[status(thm)],[c_1403,c_1807])).

tff(c_1821,plain,(
    ! [A_235] :
      ( k3_tarski(A_235) = '#skF_14'
      | A_235 != '#skF_14' ) ),
    inference(resolution,[status(thm)],[c_1403,c_1807])).

tff(c_50,plain,(
    ! [A_51,C_66] :
      ( r2_hidden('#skF_12'(A_51,k3_tarski(A_51),C_66),A_51)
      | ~ r2_hidden(C_66,k3_tarski(A_51)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1506,plain,(
    ! [A_206,C_66] :
      ( ~ v1_xboole_0(A_206)
      | ~ r2_hidden(C_66,k3_tarski(k3_tarski(A_206))) ) ),
    inference(resolution,[status(thm)],[c_50,c_1489])).

tff(c_1845,plain,(
    ! [A_235,C_66] :
      ( ~ v1_xboole_0(A_235)
      | ~ r2_hidden(C_66,k3_tarski('#skF_14'))
      | A_235 != '#skF_14' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1821,c_1506])).

tff(c_1874,plain,(
    ! [A_235,C_66] :
      ( ~ v1_xboole_0(A_235)
      | ~ r2_hidden(C_66,'#skF_14')
      | A_235 != '#skF_14' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1820,c_1845])).

tff(c_2400,plain,(
    ! [A_269] :
      ( ~ v1_xboole_0(A_269)
      | A_269 != '#skF_14' ) ),
    inference(splitLeft,[status(thm)],[c_1874])).

tff(c_2420,plain,(
    ! [A_191] : A_191 != '#skF_14' ),
    inference(resolution,[status(thm)],[c_1403,c_2400])).

tff(c_1160,plain,(
    ! [A_176,B_177] :
      ( ~ r2_hidden('#skF_2'(A_176,B_177),B_177)
      | r1_tarski(A_176,B_177) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1166,plain,(
    ! [A_178] : r1_tarski(A_178,A_178) ),
    inference(resolution,[status(thm)],[c_10,c_1160])).

tff(c_1173,plain,(
    ! [A_178] : k4_xboole_0(A_178,A_178) = '#skF_14' ),
    inference(resolution,[status(thm)],[c_1166,c_1046])).

tff(c_2434,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2420,c_1173])).

tff(c_2436,plain,(
    ! [C_270] : ~ r2_hidden(C_270,'#skF_14') ),
    inference(splitRight,[status(thm)],[c_1874])).

tff(c_2676,plain,(
    ! [D_281,A_282] : ~ r2_hidden(D_281,k2_zfmisc_1(A_282,'#skF_14')) ),
    inference(resolution,[status(thm)],[c_28,c_2436])).

tff(c_2737,plain,(
    ! [A_283] : v1_xboole_0(k2_zfmisc_1(A_283,'#skF_14')) ),
    inference(resolution,[status(thm)],[c_4,c_2676])).

tff(c_1076,plain,(
    ! [A_163,B_164] :
      ( r2_hidden('#skF_2'(A_163,B_164),A_163)
      | r1_tarski(A_163,B_164) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1080,plain,(
    ! [A_163,B_164] :
      ( ~ v1_xboole_0(A_163)
      | r1_tarski(A_163,B_164) ) ),
    inference(resolution,[status(thm)],[c_1076,c_2])).

tff(c_1136,plain,(
    ! [A_172,B_173] :
      ( k4_xboole_0(A_172,B_173) = '#skF_14'
      | ~ r1_tarski(A_172,B_173) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1041,c_16])).

tff(c_1151,plain,(
    ! [A_163,B_164] :
      ( k4_xboole_0(A_163,B_164) = '#skF_14'
      | ~ v1_xboole_0(A_163) ) ),
    inference(resolution,[status(thm)],[c_1080,c_1136])).

tff(c_3378,plain,(
    ! [A_306,B_307] : k4_xboole_0(k2_zfmisc_1(A_306,'#skF_14'),B_307) = '#skF_14' ),
    inference(resolution,[status(thm)],[c_2737,c_1151])).

tff(c_3396,plain,(
    ! [A_306] : k2_zfmisc_1(A_306,'#skF_14') = '#skF_14' ),
    inference(superposition,[status(thm),theory(equality)],[c_3378,c_1049])).

tff(c_74,plain,
    ( k2_zfmisc_1('#skF_13','#skF_14') != k1_xboole_0
    | k2_zfmisc_1('#skF_15','#skF_16') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_121,plain,(
    k2_zfmisc_1('#skF_13','#skF_14') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_1043,plain,(
    k2_zfmisc_1('#skF_13','#skF_14') != '#skF_14' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1041,c_121])).

tff(c_3460,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3396,c_1043])).

tff(c_3461,plain,(
    k1_xboole_0 = '#skF_13' ),
    inference(splitRight,[status(thm)],[c_1039])).

tff(c_3471,plain,(
    v1_xboole_0('#skF_13') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3461,c_12])).

tff(c_3674,plain,(
    ! [A_342,C_343] :
      ( r2_hidden('#skF_12'(A_342,k3_tarski(A_342),C_343),A_342)
      | ~ r2_hidden(C_343,k3_tarski(A_342)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_3685,plain,(
    ! [A_344,C_345] :
      ( ~ v1_xboole_0(A_344)
      | ~ r2_hidden(C_345,k3_tarski(A_344)) ) ),
    inference(resolution,[status(thm)],[c_3674,c_2])).

tff(c_3701,plain,(
    ! [A_346] :
      ( ~ v1_xboole_0(A_346)
      | v1_xboole_0(k3_tarski(A_346)) ) ),
    inference(resolution,[status(thm)],[c_4,c_3685])).

tff(c_3509,plain,(
    ! [A_320,B_321] :
      ( r2_hidden('#skF_2'(A_320,B_321),A_320)
      | r1_tarski(A_320,B_321) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_3576,plain,(
    ! [A_331,B_332] :
      ( ~ v1_xboole_0(A_331)
      | r1_tarski(A_331,B_332) ) ),
    inference(resolution,[status(thm)],[c_3509,c_2])).

tff(c_3467,plain,(
    ! [A_10,B_11] :
      ( k4_xboole_0(A_10,B_11) = '#skF_13'
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3461,c_16])).

tff(c_3583,plain,(
    ! [A_331,B_332] :
      ( k4_xboole_0(A_331,B_332) = '#skF_13'
      | ~ v1_xboole_0(A_331) ) ),
    inference(resolution,[status(thm)],[c_3576,c_3467])).

tff(c_3836,plain,(
    ! [A_360,B_361] :
      ( k4_xboole_0(k3_tarski(A_360),B_361) = '#skF_13'
      | ~ v1_xboole_0(A_360) ) ),
    inference(resolution,[status(thm)],[c_3701,c_3583])).

tff(c_3470,plain,(
    ! [A_14] : k4_xboole_0(A_14,'#skF_13') = A_14 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3461,c_20])).

tff(c_3869,plain,(
    ! [A_362] :
      ( k3_tarski(A_362) = '#skF_13'
      | ~ v1_xboole_0(A_362) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3836,c_3470])).

tff(c_3881,plain,(
    k3_tarski('#skF_13') = '#skF_13' ),
    inference(resolution,[status(thm)],[c_3471,c_3869])).

tff(c_3698,plain,(
    ! [A_344,C_66] :
      ( ~ v1_xboole_0(A_344)
      | ~ r2_hidden(C_66,k3_tarski(k3_tarski(A_344))) ) ),
    inference(resolution,[status(thm)],[c_50,c_3685])).

tff(c_3897,plain,(
    ! [C_66] :
      ( ~ v1_xboole_0('#skF_13')
      | ~ r2_hidden(C_66,k3_tarski('#skF_13')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3881,c_3698])).

tff(c_3924,plain,(
    ! [C_66] : ~ r2_hidden(C_66,'#skF_13') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3881,c_3471,c_3897])).

tff(c_4072,plain,(
    ! [D_372,B_373] : ~ r2_hidden(D_372,k2_zfmisc_1('#skF_13',B_373)) ),
    inference(resolution,[status(thm)],[c_4046,c_3924])).

tff(c_4124,plain,(
    ! [B_375,B_376] : r1_tarski(k2_zfmisc_1('#skF_13',B_375),B_376) ),
    inference(resolution,[status(thm)],[c_10,c_4072])).

tff(c_4373,plain,(
    ! [B_389,B_390] : k4_xboole_0(k2_zfmisc_1('#skF_13',B_389),B_390) = '#skF_13' ),
    inference(resolution,[status(thm)],[c_4124,c_3467])).

tff(c_4385,plain,(
    ! [B_389] : k2_zfmisc_1('#skF_13',B_389) = '#skF_13' ),
    inference(superposition,[status(thm),theory(equality)],[c_4373,c_3470])).

tff(c_3464,plain,(
    k2_zfmisc_1('#skF_13','#skF_14') != '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3461,c_121])).

tff(c_4415,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4385,c_3464])).

tff(c_4417,plain,(
    k2_zfmisc_1('#skF_13','#skF_14') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_4870,plain,(
    ! [E_437,F_438,A_439,B_440] :
      ( r2_hidden(k4_tarski(E_437,F_438),k2_zfmisc_1(A_439,B_440))
      | ~ r2_hidden(F_438,B_440)
      | ~ r2_hidden(E_437,A_439) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_4957,plain,(
    ! [E_447,F_448] :
      ( r2_hidden(k4_tarski(E_447,F_448),k1_xboole_0)
      | ~ r2_hidden(F_448,'#skF_14')
      | ~ r2_hidden(E_447,'#skF_13') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4417,c_4870])).

tff(c_4964,plain,(
    ! [F_448,E_447] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(F_448,'#skF_14')
      | ~ r2_hidden(E_447,'#skF_13') ) ),
    inference(resolution,[status(thm)],[c_4957,c_2])).

tff(c_4971,plain,(
    ! [F_448,E_447] :
      ( ~ r2_hidden(F_448,'#skF_14')
      | ~ r2_hidden(E_447,'#skF_13') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4750,c_4964])).

tff(c_4973,plain,(
    ! [E_449] : ~ r2_hidden(E_449,'#skF_13') ),
    inference(splitLeft,[status(thm)],[c_4971])).

tff(c_4993,plain,(
    v1_xboole_0('#skF_13') ),
    inference(resolution,[status(thm)],[c_4,c_4973])).

tff(c_4426,plain,(
    ! [A_391,B_392] :
      ( r2_hidden('#skF_2'(A_391,B_392),A_391)
      | r1_tarski(A_391,B_392) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_4431,plain,(
    ! [A_393,B_394] :
      ( ~ v1_xboole_0(A_393)
      | r1_tarski(A_393,B_394) ) ),
    inference(resolution,[status(thm)],[c_4426,c_2])).

tff(c_4438,plain,(
    ! [A_393,B_394] :
      ( k4_xboole_0(A_393,B_394) = k1_xboole_0
      | ~ v1_xboole_0(A_393) ) ),
    inference(resolution,[status(thm)],[c_4431,c_16])).

tff(c_5153,plain,(
    ! [B_458] : k4_xboole_0('#skF_13',B_458) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4993,c_4438])).

tff(c_5171,plain,(
    k1_xboole_0 = '#skF_13' ),
    inference(superposition,[status(thm),theory(equality)],[c_5153,c_20])).

tff(c_5213,plain,(
    '#skF_16' != '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5171,c_89])).

tff(c_5222,plain,(
    ! [A_459,B_460] :
      ( r2_hidden('#skF_10'(A_459,B_460),A_459)
      | r2_hidden('#skF_11'(A_459,B_460),B_460)
      | k3_tarski(A_459) = B_460 ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_4972,plain,(
    ! [E_447] : ~ r2_hidden(E_447,'#skF_13') ),
    inference(splitLeft,[status(thm)],[c_4971])).

tff(c_8440,plain,(
    ! [A_598] :
      ( r2_hidden('#skF_10'(A_598,'#skF_13'),A_598)
      | k3_tarski(A_598) = '#skF_13' ) ),
    inference(resolution,[status(thm)],[c_5222,c_4972])).

tff(c_5214,plain,(
    '#skF_15' != '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5171,c_88])).

tff(c_5014,plain,(
    ! [C_451] : ~ r2_hidden(C_451,k3_tarski('#skF_13')) ),
    inference(resolution,[status(thm)],[c_50,c_4973])).

tff(c_5067,plain,(
    ! [B_454] : r1_tarski(k3_tarski('#skF_13'),B_454) ),
    inference(resolution,[status(thm)],[c_10,c_5014])).

tff(c_5079,plain,(
    ! [B_454] : k4_xboole_0(k3_tarski('#skF_13'),B_454) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_5067,c_16])).

tff(c_5617,plain,(
    ! [B_479] : k4_xboole_0(k3_tarski('#skF_13'),B_479) = '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5171,c_5079])).

tff(c_5215,plain,(
    ! [A_14] : k4_xboole_0(A_14,'#skF_13') = A_14 ),
    inference(demodulation,[status(thm),theory(equality)],[c_5171,c_20])).

tff(c_5623,plain,(
    k3_tarski('#skF_13') = '#skF_13' ),
    inference(superposition,[status(thm),theory(equality)],[c_5617,c_5215])).

tff(c_62,plain,(
    ! [A_51,B_52] :
      ( r2_hidden('#skF_10'(A_51,B_52),A_51)
      | r2_hidden('#skF_11'(A_51,B_52),B_52)
      | k3_tarski(A_51) = B_52 ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_4416,plain,(
    k2_zfmisc_1('#skF_15','#skF_16') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_5137,plain,(
    ! [E_456,F_457] :
      ( r2_hidden(k4_tarski(E_456,F_457),k1_xboole_0)
      | ~ r2_hidden(F_457,'#skF_16')
      | ~ r2_hidden(E_456,'#skF_15') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4416,c_4870])).

tff(c_5144,plain,(
    ! [F_457,E_456] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(F_457,'#skF_16')
      | ~ r2_hidden(E_456,'#skF_15') ) ),
    inference(resolution,[status(thm)],[c_5137,c_2])).

tff(c_5151,plain,(
    ! [F_457,E_456] :
      ( ~ r2_hidden(F_457,'#skF_16')
      | ~ r2_hidden(E_456,'#skF_15') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4750,c_5144])).

tff(c_5834,plain,(
    ! [E_492] : ~ r2_hidden(E_492,'#skF_15') ),
    inference(splitLeft,[status(thm)],[c_5151])).

tff(c_6960,plain,(
    ! [A_538] :
      ( r2_hidden('#skF_10'(A_538,'#skF_15'),A_538)
      | k3_tarski(A_538) = '#skF_15' ) ),
    inference(resolution,[status(thm)],[c_62,c_5834])).

tff(c_7008,plain,(
    k3_tarski('#skF_13') = '#skF_15' ),
    inference(resolution,[status(thm)],[c_6960,c_4972])).

tff(c_7032,plain,(
    '#skF_15' = '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5623,c_7008])).

tff(c_7034,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5214,c_7032])).

tff(c_7036,plain,(
    ! [F_539] : ~ r2_hidden(F_539,'#skF_16') ),
    inference(splitRight,[status(thm)],[c_5151])).

tff(c_7071,plain,(
    ! [D_44,A_17] : ~ r2_hidden(D_44,k2_zfmisc_1(A_17,'#skF_16')) ),
    inference(resolution,[status(thm)],[c_28,c_7036])).

tff(c_8515,plain,(
    ! [A_17] : k3_tarski(k2_zfmisc_1(A_17,'#skF_16')) = '#skF_13' ),
    inference(resolution,[status(thm)],[c_8440,c_7071])).

tff(c_8832,plain,(
    ! [A_607] :
      ( r2_hidden('#skF_10'(A_607,'#skF_16'),A_607)
      | k3_tarski(A_607) = '#skF_16' ) ),
    inference(resolution,[status(thm)],[c_62,c_7036])).

tff(c_8836,plain,(
    ! [A_17] : k3_tarski(k2_zfmisc_1(A_17,'#skF_16')) = '#skF_16' ),
    inference(resolution,[status(thm)],[c_8832,c_7071])).

tff(c_8869,plain,(
    '#skF_16' = '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8515,c_8836])).

tff(c_8871,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5213,c_8869])).

tff(c_8873,plain,(
    ! [F_608] : ~ r2_hidden(F_608,'#skF_14') ),
    inference(splitRight,[status(thm)],[c_4971])).

tff(c_8893,plain,(
    v1_xboole_0('#skF_14') ),
    inference(resolution,[status(thm)],[c_4,c_8873])).

tff(c_8967,plain,(
    ! [B_613] : k4_xboole_0('#skF_14',B_613) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8893,c_4438])).

tff(c_8985,plain,(
    k1_xboole_0 = '#skF_14' ),
    inference(superposition,[status(thm),theory(equality)],[c_8967,c_20])).

tff(c_9025,plain,(
    '#skF_16' != '#skF_14' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8985,c_89])).

tff(c_9093,plain,(
    ! [A_617,B_618] :
      ( r2_hidden('#skF_10'(A_617,B_618),A_617)
      | r2_hidden('#skF_11'(A_617,B_618),B_618)
      | k3_tarski(A_617) = B_618 ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_8872,plain,(
    ! [F_448] : ~ r2_hidden(F_448,'#skF_14') ),
    inference(splitRight,[status(thm)],[c_4971])).

tff(c_11736,plain,(
    ! [A_725] :
      ( r2_hidden('#skF_10'(A_725,'#skF_14'),A_725)
      | k3_tarski(A_725) = '#skF_14' ) ),
    inference(resolution,[status(thm)],[c_9093,c_8872])).

tff(c_10902,plain,(
    ! [A_686,B_687,D_688] :
      ( r2_hidden('#skF_7'(A_686,B_687,k2_zfmisc_1(A_686,B_687),D_688),A_686)
      | ~ r2_hidden(D_688,k2_zfmisc_1(A_686,B_687)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_9026,plain,(
    '#skF_15' != '#skF_14' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8985,c_88])).

tff(c_10316,plain,(
    ! [A_672] :
      ( r2_hidden('#skF_10'(A_672,'#skF_14'),A_672)
      | k3_tarski(A_672) = '#skF_14' ) ),
    inference(resolution,[status(thm)],[c_9093,c_8872])).

tff(c_9480,plain,(
    ! [A_633,B_634,D_635] :
      ( r2_hidden('#skF_7'(A_633,B_634,k2_zfmisc_1(A_633,B_634),D_635),A_633)
      | ~ r2_hidden(D_635,k2_zfmisc_1(A_633,B_634)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_4883,plain,(
    ! [E_437,F_438] :
      ( r2_hidden(k4_tarski(E_437,F_438),k1_xboole_0)
      | ~ r2_hidden(F_438,'#skF_16')
      | ~ r2_hidden(E_437,'#skF_15') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4416,c_4870])).

tff(c_9376,plain,(
    ! [E_437,F_438] :
      ( r2_hidden(k4_tarski(E_437,F_438),'#skF_14')
      | ~ r2_hidden(F_438,'#skF_16')
      | ~ r2_hidden(E_437,'#skF_15') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8985,c_4883])).

tff(c_9377,plain,(
    ! [F_438,E_437] :
      ( ~ r2_hidden(F_438,'#skF_16')
      | ~ r2_hidden(E_437,'#skF_15') ) ),
    inference(negUnitSimplification,[status(thm)],[c_8872,c_9376])).

tff(c_9378,plain,(
    ! [E_437] : ~ r2_hidden(E_437,'#skF_15') ),
    inference(splitLeft,[status(thm)],[c_9377])).

tff(c_9523,plain,(
    ! [D_635,B_634] : ~ r2_hidden(D_635,k2_zfmisc_1('#skF_15',B_634)) ),
    inference(resolution,[status(thm)],[c_9480,c_9378])).

tff(c_10361,plain,(
    ! [B_634] : k3_tarski(k2_zfmisc_1('#skF_15',B_634)) = '#skF_14' ),
    inference(resolution,[status(thm)],[c_10316,c_9523])).

tff(c_9379,plain,(
    ! [E_630] : ~ r2_hidden(E_630,'#skF_15') ),
    inference(splitLeft,[status(thm)],[c_9377])).

tff(c_10760,plain,(
    ! [A_682] :
      ( r2_hidden('#skF_10'(A_682,'#skF_15'),A_682)
      | k3_tarski(A_682) = '#skF_15' ) ),
    inference(resolution,[status(thm)],[c_62,c_9379])).

tff(c_10764,plain,(
    ! [B_634] : k3_tarski(k2_zfmisc_1('#skF_15',B_634)) = '#skF_15' ),
    inference(resolution,[status(thm)],[c_10760,c_9523])).

tff(c_10797,plain,(
    '#skF_15' = '#skF_14' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10361,c_10764])).

tff(c_10799,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9026,c_10797])).

tff(c_10800,plain,(
    ! [F_438] : ~ r2_hidden(F_438,'#skF_16') ),
    inference(splitRight,[status(thm)],[c_9377])).

tff(c_10945,plain,(
    ! [D_688,B_687] : ~ r2_hidden(D_688,k2_zfmisc_1('#skF_16',B_687)) ),
    inference(resolution,[status(thm)],[c_10902,c_10800])).

tff(c_11781,plain,(
    ! [B_687] : k3_tarski(k2_zfmisc_1('#skF_16',B_687)) = '#skF_14' ),
    inference(resolution,[status(thm)],[c_11736,c_10945])).

tff(c_10801,plain,(
    ! [F_683] : ~ r2_hidden(F_683,'#skF_16') ),
    inference(splitRight,[status(thm)],[c_9377])).

tff(c_12180,plain,(
    ! [A_735] :
      ( r2_hidden('#skF_10'(A_735,'#skF_16'),A_735)
      | k3_tarski(A_735) = '#skF_16' ) ),
    inference(resolution,[status(thm)],[c_62,c_10801])).

tff(c_12184,plain,(
    ! [B_687] : k3_tarski(k2_zfmisc_1('#skF_16',B_687)) = '#skF_16' ),
    inference(resolution,[status(thm)],[c_12180,c_10945])).

tff(c_12217,plain,(
    '#skF_16' = '#skF_14' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11781,c_12184])).

tff(c_12219,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9025,c_12217])).

tff(c_12221,plain,(
    k1_xboole_0 = '#skF_16' ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_68,plain,
    ( k1_xboole_0 = '#skF_14'
    | k1_xboole_0 = '#skF_13'
    | k1_xboole_0 != '#skF_16' ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_12240,plain,
    ( '#skF_16' = '#skF_14'
    | '#skF_16' = '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12221,c_12221,c_12221,c_68])).

tff(c_12241,plain,(
    '#skF_16' = '#skF_13' ),
    inference(splitLeft,[status(thm)],[c_12240])).

tff(c_12224,plain,(
    v1_xboole_0('#skF_16') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12221,c_12])).

tff(c_12244,plain,(
    v1_xboole_0('#skF_13') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12241,c_12224])).

tff(c_12223,plain,(
    ! [A_14] : k4_xboole_0(A_14,'#skF_16') = A_14 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12221,c_20])).

tff(c_12242,plain,(
    ! [A_14] : k4_xboole_0(A_14,'#skF_13') = A_14 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12241,c_12223])).

tff(c_12246,plain,(
    k1_xboole_0 = '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12241,c_12221])).

tff(c_14,plain,(
    ! [A_10,B_11] :
      ( r1_tarski(A_10,B_11)
      | k4_xboole_0(A_10,B_11) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_12271,plain,(
    ! [A_10,B_11] :
      ( r1_tarski(A_10,B_11)
      | k4_xboole_0(A_10,B_11) != '#skF_13' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12246,c_14])).

tff(c_12273,plain,(
    ! [A_741,B_742] :
      ( k2_xboole_0(A_741,B_742) = B_742
      | ~ r1_tarski(A_741,B_742) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_12499,plain,(
    ! [A_771,B_772] :
      ( k2_xboole_0(A_771,B_772) = B_772
      | k4_xboole_0(A_771,B_772) != '#skF_13' ) ),
    inference(resolution,[status(thm)],[c_12271,c_12273])).

tff(c_12519,plain,(
    ! [A_773] :
      ( k2_xboole_0(A_773,'#skF_13') = '#skF_13'
      | A_773 != '#skF_13' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12242,c_12499])).

tff(c_12539,plain,(
    ! [A_773] :
      ( r1_tarski(A_773,'#skF_13')
      | A_773 != '#skF_13' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12519,c_22])).

tff(c_12385,plain,(
    ! [C_759,B_760,A_761] :
      ( r2_hidden(C_759,B_760)
      | ~ r2_hidden(C_759,A_761)
      | ~ r1_tarski(A_761,B_760) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_12585,plain,(
    ! [A_777,B_778] :
      ( r2_hidden('#skF_1'(A_777),B_778)
      | ~ r1_tarski(A_777,B_778)
      | v1_xboole_0(A_777) ) ),
    inference(resolution,[status(thm)],[c_4,c_12385])).

tff(c_12596,plain,(
    ! [B_779,A_780] :
      ( ~ v1_xboole_0(B_779)
      | ~ r1_tarski(A_780,B_779)
      | v1_xboole_0(A_780) ) ),
    inference(resolution,[status(thm)],[c_12585,c_2])).

tff(c_12599,plain,(
    ! [A_773] :
      ( ~ v1_xboole_0('#skF_13')
      | v1_xboole_0(A_773)
      | A_773 != '#skF_13' ) ),
    inference(resolution,[status(thm)],[c_12539,c_12596])).

tff(c_12617,plain,(
    ! [A_773] :
      ( v1_xboole_0(A_773)
      | A_773 != '#skF_13' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12244,c_12599])).

tff(c_12653,plain,(
    ! [A_784,C_785] :
      ( r2_hidden('#skF_12'(A_784,k3_tarski(A_784),C_785),A_784)
      | ~ r2_hidden(C_785,k3_tarski(A_784)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_12664,plain,(
    ! [A_786,C_787] :
      ( ~ v1_xboole_0(A_786)
      | ~ r2_hidden(C_787,k3_tarski(A_786)) ) ),
    inference(resolution,[status(thm)],[c_12653,c_2])).

tff(c_12692,plain,(
    ! [A_789,B_790] :
      ( ~ v1_xboole_0(A_789)
      | r1_tarski(k3_tarski(A_789),B_790) ) ),
    inference(resolution,[status(thm)],[c_10,c_12664])).

tff(c_12282,plain,(
    ! [A_10,B_11] :
      ( k4_xboole_0(A_10,B_11) = '#skF_13'
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12246,c_16])).

tff(c_12981,plain,(
    ! [A_814,B_815] :
      ( k4_xboole_0(k3_tarski(A_814),B_815) = '#skF_13'
      | ~ v1_xboole_0(A_814) ) ),
    inference(resolution,[status(thm)],[c_12692,c_12282])).

tff(c_13027,plain,(
    ! [A_816] :
      ( k3_tarski(A_816) = '#skF_13'
      | ~ v1_xboole_0(A_816) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12981,c_12242])).

tff(c_13061,plain,(
    k3_tarski('#skF_13') = '#skF_13' ),
    inference(resolution,[status(thm)],[c_12617,c_13027])).

tff(c_13062,plain,(
    ! [A_820] :
      ( k3_tarski(A_820) = '#skF_13'
      | A_820 != '#skF_13' ) ),
    inference(resolution,[status(thm)],[c_12617,c_13027])).

tff(c_12681,plain,(
    ! [A_786,C_66] :
      ( ~ v1_xboole_0(A_786)
      | ~ r2_hidden(C_66,k3_tarski(k3_tarski(A_786))) ) ),
    inference(resolution,[status(thm)],[c_50,c_12664])).

tff(c_13086,plain,(
    ! [A_820,C_66] :
      ( ~ v1_xboole_0(A_820)
      | ~ r2_hidden(C_66,k3_tarski('#skF_13'))
      | A_820 != '#skF_13' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13062,c_12681])).

tff(c_13115,plain,(
    ! [A_820,C_66] :
      ( ~ v1_xboole_0(A_820)
      | ~ r2_hidden(C_66,'#skF_13')
      | A_820 != '#skF_13' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13061,c_13086])).

tff(c_13680,plain,(
    ! [A_851] :
      ( ~ v1_xboole_0(A_851)
      | A_851 != '#skF_13' ) ),
    inference(splitLeft,[status(thm)],[c_13115])).

tff(c_13700,plain,(
    ! [A_773] : A_773 != '#skF_13' ),
    inference(resolution,[status(thm)],[c_12617,c_13680])).

tff(c_12334,plain,(
    ! [A_754,B_755] :
      ( ~ r2_hidden('#skF_2'(A_754,B_755),B_755)
      | r1_tarski(A_754,B_755) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_12340,plain,(
    ! [A_756] : r1_tarski(A_756,A_756) ),
    inference(resolution,[status(thm)],[c_10,c_12334])).

tff(c_12347,plain,(
    ! [A_756] : k4_xboole_0(A_756,A_756) = '#skF_13' ),
    inference(resolution,[status(thm)],[c_12340,c_12282])).

tff(c_13746,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_13700,c_12347])).

tff(c_13748,plain,(
    ! [C_855] : ~ r2_hidden(C_855,'#skF_13') ),
    inference(splitRight,[status(thm)],[c_13115])).

tff(c_13957,plain,(
    ! [D_863,B_864] : ~ r2_hidden(D_863,k2_zfmisc_1('#skF_13',B_864)) ),
    inference(resolution,[status(thm)],[c_30,c_13748])).

tff(c_14055,plain,(
    ! [B_871,B_872] : r1_tarski(k2_zfmisc_1('#skF_13',B_871),B_872) ),
    inference(resolution,[status(thm)],[c_10,c_13957])).

tff(c_14286,plain,(
    ! [B_878,B_879] : k4_xboole_0(k2_zfmisc_1('#skF_13',B_878),B_879) = '#skF_13' ),
    inference(resolution,[status(thm)],[c_14055,c_12282])).

tff(c_14304,plain,(
    ! [B_878] : k2_zfmisc_1('#skF_13',B_878) = '#skF_13' ),
    inference(superposition,[status(thm),theory(equality)],[c_14286,c_12242])).

tff(c_12220,plain,(
    k2_zfmisc_1('#skF_13','#skF_14') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_12229,plain,(
    k2_zfmisc_1('#skF_13','#skF_14') != '#skF_16' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12221,c_12220])).

tff(c_12243,plain,(
    k2_zfmisc_1('#skF_13','#skF_14') != '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12241,c_12229])).

tff(c_14341,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14304,c_12243])).

tff(c_14342,plain,(
    '#skF_16' = '#skF_14' ),
    inference(splitRight,[status(thm)],[c_12240])).

tff(c_14346,plain,(
    v1_xboole_0('#skF_14') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14342,c_12224])).

tff(c_14689,plain,(
    ! [A_920,C_921] :
      ( r2_hidden('#skF_12'(A_920,k3_tarski(A_920),C_921),A_920)
      | ~ r2_hidden(C_921,k3_tarski(A_920)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_14700,plain,(
    ! [A_922,C_923] :
      ( ~ v1_xboole_0(A_922)
      | ~ r2_hidden(C_923,k3_tarski(A_922)) ) ),
    inference(resolution,[status(thm)],[c_14689,c_2])).

tff(c_14716,plain,(
    ! [A_924] :
      ( ~ v1_xboole_0(A_924)
      | v1_xboole_0(k3_tarski(A_924)) ) ),
    inference(resolution,[status(thm)],[c_4,c_14700])).

tff(c_14406,plain,(
    ! [A_892,B_893] :
      ( r2_hidden('#skF_2'(A_892,B_893),A_892)
      | r1_tarski(A_892,B_893) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_14466,plain,(
    ! [A_900,B_901] :
      ( ~ v1_xboole_0(A_900)
      | r1_tarski(A_900,B_901) ) ),
    inference(resolution,[status(thm)],[c_14406,c_2])).

tff(c_14348,plain,(
    k1_xboole_0 = '#skF_14' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14342,c_12221])).

tff(c_14385,plain,(
    ! [A_10,B_11] :
      ( k4_xboole_0(A_10,B_11) = '#skF_14'
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14348,c_16])).

tff(c_14473,plain,(
    ! [A_900,B_901] :
      ( k4_xboole_0(A_900,B_901) = '#skF_14'
      | ~ v1_xboole_0(A_900) ) ),
    inference(resolution,[status(thm)],[c_14466,c_14385])).

tff(c_14875,plain,(
    ! [A_938,B_939] :
      ( k4_xboole_0(k3_tarski(A_938),B_939) = '#skF_14'
      | ~ v1_xboole_0(A_938) ) ),
    inference(resolution,[status(thm)],[c_14716,c_14473])).

tff(c_14344,plain,(
    ! [A_14] : k4_xboole_0(A_14,'#skF_14') = A_14 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14342,c_12223])).

tff(c_14912,plain,(
    ! [A_940] :
      ( k3_tarski(A_940) = '#skF_14'
      | ~ v1_xboole_0(A_940) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14875,c_14344])).

tff(c_14924,plain,(
    k3_tarski('#skF_14') = '#skF_14' ),
    inference(resolution,[status(thm)],[c_14346,c_14912])).

tff(c_14713,plain,(
    ! [A_922,C_66] :
      ( ~ v1_xboole_0(A_922)
      | ~ r2_hidden(C_66,k3_tarski(k3_tarski(A_922))) ) ),
    inference(resolution,[status(thm)],[c_50,c_14700])).

tff(c_14940,plain,(
    ! [C_66] :
      ( ~ v1_xboole_0('#skF_14')
      | ~ r2_hidden(C_66,k3_tarski('#skF_14')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14924,c_14713])).

tff(c_14967,plain,(
    ! [C_66] : ~ r2_hidden(C_66,'#skF_14') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14924,c_14346,c_14940])).

tff(c_15269,plain,(
    ! [D_959,A_960] : ~ r2_hidden(D_959,k2_zfmisc_1(A_960,'#skF_14')) ),
    inference(resolution,[status(thm)],[c_15238,c_14967])).

tff(c_15315,plain,(
    ! [A_961] : v1_xboole_0(k2_zfmisc_1(A_961,'#skF_14')) ),
    inference(resolution,[status(thm)],[c_4,c_15269])).

tff(c_15622,plain,(
    ! [A_978,B_979] : k4_xboole_0(k2_zfmisc_1(A_978,'#skF_14'),B_979) = '#skF_14' ),
    inference(resolution,[status(thm)],[c_15315,c_14473])).

tff(c_15637,plain,(
    ! [A_978] : k2_zfmisc_1(A_978,'#skF_14') = '#skF_14' ),
    inference(superposition,[status(thm),theory(equality)],[c_15622,c_14344])).

tff(c_14345,plain,(
    k2_zfmisc_1('#skF_13','#skF_14') != '#skF_14' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14342,c_12229])).

tff(c_15675,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_15637,c_14345])).

tff(c_15677,plain,(
    k1_xboole_0 = '#skF_15' ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_72,plain,
    ( k1_xboole_0 = '#skF_14'
    | k1_xboole_0 = '#skF_13'
    | k1_xboole_0 != '#skF_15' ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_15703,plain,
    ( '#skF_15' = '#skF_14'
    | '#skF_15' = '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15677,c_15677,c_15677,c_72])).

tff(c_15704,plain,(
    '#skF_15' = '#skF_13' ),
    inference(splitLeft,[status(thm)],[c_15703])).

tff(c_15679,plain,(
    v1_xboole_0('#skF_15') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15677,c_12])).

tff(c_15708,plain,(
    v1_xboole_0('#skF_13') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15704,c_15679])).

tff(c_15678,plain,(
    ! [A_14] : k4_xboole_0(A_14,'#skF_15') = A_14 ),
    inference(demodulation,[status(thm),theory(equality)],[c_15677,c_20])).

tff(c_15706,plain,(
    ! [A_14] : k4_xboole_0(A_14,'#skF_13') = A_14 ),
    inference(demodulation,[status(thm),theory(equality)],[c_15704,c_15678])).

tff(c_15709,plain,(
    k1_xboole_0 = '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15704,c_15677])).

tff(c_15747,plain,(
    ! [A_989,B_990] :
      ( r1_tarski(A_989,B_990)
      | k4_xboole_0(A_989,B_990) != '#skF_13' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15709,c_14])).

tff(c_15966,plain,(
    ! [A_1017,B_1018] :
      ( k2_xboole_0(A_1017,B_1018) = B_1018
      | k4_xboole_0(A_1017,B_1018) != '#skF_13' ) ),
    inference(resolution,[status(thm)],[c_15747,c_18])).

tff(c_15986,plain,(
    ! [A_1019] :
      ( k2_xboole_0(A_1019,'#skF_13') = '#skF_13'
      | A_1019 != '#skF_13' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_15706,c_15966])).

tff(c_16006,plain,(
    ! [A_1019] :
      ( r1_tarski(A_1019,'#skF_13')
      | A_1019 != '#skF_13' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_15986,c_22])).

tff(c_15810,plain,(
    ! [C_998,B_999,A_1000] :
      ( r2_hidden(C_998,B_999)
      | ~ r2_hidden(C_998,A_1000)
      | ~ r1_tarski(A_1000,B_999) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_16041,plain,(
    ! [A_1021,B_1022] :
      ( r2_hidden('#skF_1'(A_1021),B_1022)
      | ~ r1_tarski(A_1021,B_1022)
      | v1_xboole_0(A_1021) ) ),
    inference(resolution,[status(thm)],[c_4,c_15810])).

tff(c_16111,plain,(
    ! [B_1034,A_1035] :
      ( ~ v1_xboole_0(B_1034)
      | ~ r1_tarski(A_1035,B_1034)
      | v1_xboole_0(A_1035) ) ),
    inference(resolution,[status(thm)],[c_16041,c_2])).

tff(c_16117,plain,(
    ! [A_1019] :
      ( ~ v1_xboole_0('#skF_13')
      | v1_xboole_0(A_1019)
      | A_1019 != '#skF_13' ) ),
    inference(resolution,[status(thm)],[c_16006,c_16111])).

tff(c_16136,plain,(
    ! [A_1019] :
      ( v1_xboole_0(A_1019)
      | A_1019 != '#skF_13' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15708,c_16117])).

tff(c_16052,plain,(
    ! [A_1023,C_1024] :
      ( r2_hidden('#skF_12'(A_1023,k3_tarski(A_1023),C_1024),A_1023)
      | ~ r2_hidden(C_1024,k3_tarski(A_1023)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_16063,plain,(
    ! [A_1025,C_1026] :
      ( ~ v1_xboole_0(A_1025)
      | ~ r2_hidden(C_1026,k3_tarski(A_1025)) ) ),
    inference(resolution,[status(thm)],[c_16052,c_2])).

tff(c_16083,plain,(
    ! [A_1025] :
      ( ~ v1_xboole_0(A_1025)
      | v1_xboole_0(k3_tarski(A_1025)) ) ),
    inference(resolution,[status(thm)],[c_4,c_16063])).

tff(c_16084,plain,(
    ! [A_1027] :
      ( ~ v1_xboole_0(A_1027)
      | v1_xboole_0(k3_tarski(A_1027)) ) ),
    inference(resolution,[status(thm)],[c_4,c_16063])).

tff(c_15758,plain,(
    ! [A_993,B_994] :
      ( r2_hidden('#skF_2'(A_993,B_994),A_993)
      | r1_tarski(A_993,B_994) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_15818,plain,(
    ! [A_1001,B_1002] :
      ( ~ v1_xboole_0(A_1001)
      | r1_tarski(A_1001,B_1002) ) ),
    inference(resolution,[status(thm)],[c_15758,c_2])).

tff(c_15727,plain,(
    ! [A_10,B_11] :
      ( k4_xboole_0(A_10,B_11) = '#skF_13'
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15709,c_16])).

tff(c_15826,plain,(
    ! [A_1001,B_1002] :
      ( k4_xboole_0(A_1001,B_1002) = '#skF_13'
      | ~ v1_xboole_0(A_1001) ) ),
    inference(resolution,[status(thm)],[c_15818,c_15727])).

tff(c_16613,plain,(
    ! [A_1080,B_1081] :
      ( k4_xboole_0(k3_tarski(A_1080),B_1081) = '#skF_13'
      | ~ v1_xboole_0(A_1080) ) ),
    inference(resolution,[status(thm)],[c_16084,c_15826])).

tff(c_16659,plain,(
    ! [A_1082] :
      ( k3_tarski(A_1082) = '#skF_13'
      | ~ v1_xboole_0(A_1082) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16613,c_15706])).

tff(c_16749,plain,(
    ! [A_1086] :
      ( k3_tarski(k3_tarski(A_1086)) = '#skF_13'
      | ~ v1_xboole_0(A_1086) ) ),
    inference(resolution,[status(thm)],[c_16083,c_16659])).

tff(c_16080,plain,(
    ! [A_1025,C_66] :
      ( ~ v1_xboole_0(A_1025)
      | ~ r2_hidden(C_66,k3_tarski(k3_tarski(A_1025))) ) ),
    inference(resolution,[status(thm)],[c_50,c_16063])).

tff(c_16782,plain,(
    ! [A_1086,C_66] :
      ( ~ v1_xboole_0(A_1086)
      | ~ r2_hidden(C_66,'#skF_13')
      | ~ v1_xboole_0(A_1086) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16749,c_16080])).

tff(c_17160,plain,(
    ! [A_1098] :
      ( ~ v1_xboole_0(A_1098)
      | ~ v1_xboole_0(A_1098) ) ),
    inference(splitLeft,[status(thm)],[c_16782])).

tff(c_17177,plain,(
    ! [A_1099] :
      ( ~ v1_xboole_0(A_1099)
      | A_1099 != '#skF_13' ) ),
    inference(resolution,[status(thm)],[c_16136,c_17160])).

tff(c_17196,plain,(
    ! [A_1019] : A_1019 != '#skF_13' ),
    inference(resolution,[status(thm)],[c_16136,c_17177])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( ~ r2_hidden('#skF_2'(A_5,B_6),B_6)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_15768,plain,(
    ! [A_995] : r1_tarski(A_995,A_995) ),
    inference(resolution,[status(thm)],[c_15758,c_8])).

tff(c_15776,plain,(
    ! [A_995] : k4_xboole_0(A_995,A_995) = '#skF_13' ),
    inference(resolution,[status(thm)],[c_15768,c_15727])).

tff(c_17223,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_17196,c_15776])).

tff(c_17225,plain,(
    ! [C_1103] : ~ r2_hidden(C_1103,'#skF_13') ),
    inference(splitRight,[status(thm)],[c_16782])).

tff(c_17283,plain,(
    ! [D_1104,B_1105] : ~ r2_hidden(D_1104,k2_zfmisc_1('#skF_13',B_1105)) ),
    inference(resolution,[status(thm)],[c_30,c_17225])).

tff(c_17481,plain,(
    ! [B_1114,B_1115] : r1_tarski(k2_zfmisc_1('#skF_13',B_1114),B_1115) ),
    inference(resolution,[status(thm)],[c_10,c_17283])).

tff(c_17876,plain,(
    ! [B_1128,B_1129] : k4_xboole_0(k2_zfmisc_1('#skF_13',B_1128),B_1129) = '#skF_13' ),
    inference(resolution,[status(thm)],[c_17481,c_15727])).

tff(c_17894,plain,(
    ! [B_1128] : k2_zfmisc_1('#skF_13',B_1128) = '#skF_13' ),
    inference(superposition,[status(thm),theory(equality)],[c_17876,c_15706])).

tff(c_15676,plain,(
    k2_zfmisc_1('#skF_13','#skF_14') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_15684,plain,(
    k2_zfmisc_1('#skF_13','#skF_14') != '#skF_15' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15677,c_15676])).

tff(c_15707,plain,(
    k2_zfmisc_1('#skF_13','#skF_14') != '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15704,c_15684])).

tff(c_17931,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_17894,c_15707])).

tff(c_17932,plain,(
    '#skF_15' = '#skF_14' ),
    inference(splitRight,[status(thm)],[c_15703])).

tff(c_17938,plain,(
    v1_xboole_0('#skF_14') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17932,c_15679])).

tff(c_18216,plain,(
    ! [A_1167,C_1168] :
      ( r2_hidden('#skF_12'(A_1167,k3_tarski(A_1167),C_1168),A_1167)
      | ~ r2_hidden(C_1168,k3_tarski(A_1167)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_18227,plain,(
    ! [A_1169,C_1170] :
      ( ~ v1_xboole_0(A_1169)
      | ~ r2_hidden(C_1170,k3_tarski(A_1169)) ) ),
    inference(resolution,[status(thm)],[c_18216,c_2])).

tff(c_18306,plain,(
    ! [A_1174,B_1175] :
      ( ~ v1_xboole_0(A_1174)
      | r1_tarski(k3_tarski(A_1174),B_1175) ) ),
    inference(resolution,[status(thm)],[c_10,c_18227])).

tff(c_17939,plain,(
    k1_xboole_0 = '#skF_14' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17932,c_15677])).

tff(c_17971,plain,(
    ! [A_10,B_11] :
      ( k4_xboole_0(A_10,B_11) = '#skF_14'
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17939,c_16])).

tff(c_18359,plain,(
    ! [A_1181,B_1182] :
      ( k4_xboole_0(k3_tarski(A_1181),B_1182) = '#skF_14'
      | ~ v1_xboole_0(A_1181) ) ),
    inference(resolution,[status(thm)],[c_18306,c_17971])).

tff(c_17936,plain,(
    ! [A_14] : k4_xboole_0(A_14,'#skF_14') = A_14 ),
    inference(demodulation,[status(thm),theory(equality)],[c_17932,c_15678])).

tff(c_18437,plain,(
    ! [A_1185] :
      ( k3_tarski(A_1185) = '#skF_14'
      | ~ v1_xboole_0(A_1185) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18359,c_17936])).

tff(c_18449,plain,(
    k3_tarski('#skF_14') = '#skF_14' ),
    inference(resolution,[status(thm)],[c_17938,c_18437])).

tff(c_18240,plain,(
    ! [A_1169,C_66] :
      ( ~ v1_xboole_0(A_1169)
      | ~ r2_hidden(C_66,k3_tarski(k3_tarski(A_1169))) ) ),
    inference(resolution,[status(thm)],[c_50,c_18227])).

tff(c_18459,plain,(
    ! [C_66] :
      ( ~ v1_xboole_0('#skF_14')
      | ~ r2_hidden(C_66,k3_tarski('#skF_14')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18449,c_18240])).

tff(c_18482,plain,(
    ! [C_66] : ~ r2_hidden(C_66,'#skF_14') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18449,c_17938,c_18459])).

tff(c_18676,plain,(
    ! [D_1197,A_1198] : ~ r2_hidden(D_1197,k2_zfmisc_1(A_1198,'#skF_14')) ),
    inference(resolution,[status(thm)],[c_18650,c_18482])).

tff(c_18728,plain,(
    ! [A_1200,B_1201] : r1_tarski(k2_zfmisc_1(A_1200,'#skF_14'),B_1201) ),
    inference(resolution,[status(thm)],[c_10,c_18676])).

tff(c_18967,plain,(
    ! [A_1214,B_1215] : k4_xboole_0(k2_zfmisc_1(A_1214,'#skF_14'),B_1215) = '#skF_14' ),
    inference(resolution,[status(thm)],[c_18728,c_17971])).

tff(c_18982,plain,(
    ! [A_1214] : k2_zfmisc_1(A_1214,'#skF_14') = '#skF_14' ),
    inference(superposition,[status(thm),theory(equality)],[c_18967,c_17936])).

tff(c_17937,plain,(
    k2_zfmisc_1('#skF_13','#skF_14') != '#skF_14' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17932,c_15684])).

tff(c_19013,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18982,c_17937])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:18:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.76/2.80  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.76/2.85  
% 7.76/2.85  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.76/2.85  %$ r2_hidden > r1_tarski > v1_xboole_0 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k3_tarski > k1_xboole_0 > #skF_11 > #skF_6 > #skF_15 > #skF_1 > #skF_12 > #skF_4 > #skF_8 > #skF_16 > #skF_14 > #skF_13 > #skF_5 > #skF_10 > #skF_7 > #skF_3 > #skF_2 > #skF_9
% 7.76/2.85  
% 7.76/2.85  %Foreground sorts:
% 7.76/2.85  
% 7.76/2.85  
% 7.76/2.85  %Background operators:
% 7.76/2.85  
% 7.76/2.85  
% 7.76/2.85  %Foreground operators:
% 7.76/2.85  tff('#skF_11', type, '#skF_11': ($i * $i) > $i).
% 7.76/2.85  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.76/2.85  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.76/2.85  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 7.76/2.85  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.76/2.85  tff('#skF_15', type, '#skF_15': $i).
% 7.76/2.85  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 7.76/2.85  tff('#skF_1', type, '#skF_1': $i > $i).
% 7.76/2.85  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.76/2.85  tff('#skF_12', type, '#skF_12': ($i * $i * $i) > $i).
% 7.76/2.85  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 7.76/2.85  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.76/2.85  tff('#skF_8', type, '#skF_8': ($i * $i * $i * $i) > $i).
% 7.76/2.85  tff('#skF_16', type, '#skF_16': $i).
% 7.76/2.85  tff('#skF_14', type, '#skF_14': $i).
% 7.76/2.85  tff('#skF_13', type, '#skF_13': $i).
% 7.76/2.85  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 7.76/2.85  tff('#skF_10', type, '#skF_10': ($i * $i) > $i).
% 7.76/2.85  tff('#skF_7', type, '#skF_7': ($i * $i * $i * $i) > $i).
% 7.76/2.85  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.76/2.85  tff(k3_tarski, type, k3_tarski: $i > $i).
% 7.76/2.85  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.76/2.85  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 7.76/2.85  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.76/2.85  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 7.76/2.85  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.76/2.85  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.76/2.85  tff('#skF_9', type, '#skF_9': ($i * $i) > $i).
% 7.76/2.85  
% 8.22/2.90  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 8.22/2.90  tff(f_63, axiom, (![A, B, C]: ((C = k2_zfmisc_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E, F]: ((r2_hidden(E, A) & r2_hidden(F, B)) & (D = k4_tarski(E, F)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 8.22/2.90  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 8.22/2.90  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 8.22/2.90  tff(f_49, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 8.22/2.90  tff(f_43, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 8.22/2.90  tff(f_47, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 8.22/2.90  tff(f_51, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 8.22/2.90  tff(f_80, negated_conjecture, ~(![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 8.22/2.90  tff(f_73, axiom, (![A, B]: ((B = k3_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(C, D) & r2_hidden(D, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tarski)).
% 8.22/2.90  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_2'(A_5, B_6), A_5) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.22/2.90  tff(c_18650, plain, (![A_1194, B_1195, D_1196]: (r2_hidden('#skF_8'(A_1194, B_1195, k2_zfmisc_1(A_1194, B_1195), D_1196), B_1195) | ~r2_hidden(D_1196, k2_zfmisc_1(A_1194, B_1195)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 8.22/2.90  tff(c_30, plain, (![A_17, B_18, D_44]: (r2_hidden('#skF_7'(A_17, B_18, k2_zfmisc_1(A_17, B_18), D_44), A_17) | ~r2_hidden(D_44, k2_zfmisc_1(A_17, B_18)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 8.22/2.90  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.22/2.90  tff(c_15238, plain, (![A_956, B_957, D_958]: (r2_hidden('#skF_8'(A_956, B_957, k2_zfmisc_1(A_956, B_957), D_958), B_957) | ~r2_hidden(D_958, k2_zfmisc_1(A_956, B_957)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 8.22/2.90  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.22/2.90  tff(c_20, plain, (![A_14]: (k4_xboole_0(A_14, k1_xboole_0)=A_14)), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.22/2.90  tff(c_112, plain, (![A_82, B_83]: (r1_tarski(A_82, B_83) | k4_xboole_0(A_82, B_83)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.22/2.90  tff(c_18, plain, (![A_12, B_13]: (k2_xboole_0(A_12, B_13)=B_13 | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_47])).
% 8.22/2.90  tff(c_4582, plain, (![A_413, B_414]: (k2_xboole_0(A_413, B_414)=B_414 | k4_xboole_0(A_413, B_414)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_112, c_18])).
% 8.22/2.90  tff(c_4601, plain, (![A_415]: (k2_xboole_0(A_415, k1_xboole_0)=k1_xboole_0 | k1_xboole_0!=A_415)), inference(superposition, [status(thm), theory('equality')], [c_20, c_4582])).
% 8.22/2.90  tff(c_22, plain, (![A_15, B_16]: (r1_tarski(A_15, k2_xboole_0(A_15, B_16)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.22/2.90  tff(c_4618, plain, (![A_415]: (r1_tarski(A_415, k1_xboole_0) | k1_xboole_0!=A_415)), inference(superposition, [status(thm), theory('equality')], [c_4601, c_22])).
% 8.22/2.90  tff(c_4507, plain, (![C_404, B_405, A_406]: (r2_hidden(C_404, B_405) | ~r2_hidden(C_404, A_406) | ~r1_tarski(A_406, B_405))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.22/2.90  tff(c_4711, plain, (![A_421, B_422]: (r2_hidden('#skF_1'(A_421), B_422) | ~r1_tarski(A_421, B_422) | v1_xboole_0(A_421))), inference(resolution, [status(thm)], [c_4, c_4507])).
% 8.22/2.90  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.22/2.90  tff(c_4722, plain, (![B_423, A_424]: (~v1_xboole_0(B_423) | ~r1_tarski(A_424, B_423) | v1_xboole_0(A_424))), inference(resolution, [status(thm)], [c_4711, c_2])).
% 8.22/2.90  tff(c_4725, plain, (![A_415]: (~v1_xboole_0(k1_xboole_0) | v1_xboole_0(A_415) | k1_xboole_0!=A_415)), inference(resolution, [status(thm)], [c_4618, c_4722])).
% 8.22/2.90  tff(c_4750, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_4725])).
% 8.22/2.90  tff(c_4046, plain, (![A_369, B_370, D_371]: (r2_hidden('#skF_7'(A_369, B_370, k2_zfmisc_1(A_369, B_370), D_371), A_369) | ~r2_hidden(D_371, k2_zfmisc_1(A_369, B_370)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 8.22/2.90  tff(c_28, plain, (![A_17, B_18, D_44]: (r2_hidden('#skF_8'(A_17, B_18, k2_zfmisc_1(A_17, B_18), D_44), B_18) | ~r2_hidden(D_44, k2_zfmisc_1(A_17, B_18)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 8.22/2.90  tff(c_66, plain, (k2_zfmisc_1('#skF_13', '#skF_14')!=k1_xboole_0 | k1_xboole_0!='#skF_16'), inference(cnfTransformation, [status(thm)], [f_80])).
% 8.22/2.90  tff(c_89, plain, (k1_xboole_0!='#skF_16'), inference(splitLeft, [status(thm)], [c_66])).
% 8.22/2.90  tff(c_70, plain, (k2_zfmisc_1('#skF_13', '#skF_14')!=k1_xboole_0 | k1_xboole_0!='#skF_15'), inference(cnfTransformation, [status(thm)], [f_80])).
% 8.22/2.90  tff(c_88, plain, (k1_xboole_0!='#skF_15'), inference(splitLeft, [status(thm)], [c_70])).
% 8.22/2.90  tff(c_325, plain, (![A_108, B_109]: (k2_xboole_0(A_108, B_109)=B_109 | k4_xboole_0(A_108, B_109)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_112, c_18])).
% 8.22/2.90  tff(c_345, plain, (![A_110]: (k2_xboole_0(A_110, k1_xboole_0)=k1_xboole_0 | k1_xboole_0!=A_110)), inference(superposition, [status(thm), theory('equality')], [c_20, c_325])).
% 8.22/2.90  tff(c_365, plain, (![A_110]: (r1_tarski(A_110, k1_xboole_0) | k1_xboole_0!=A_110)), inference(superposition, [status(thm), theory('equality')], [c_345, c_22])).
% 8.22/2.90  tff(c_190, plain, (![C_93, B_94, A_95]: (r2_hidden(C_93, B_94) | ~r2_hidden(C_93, A_95) | ~r1_tarski(A_95, B_94))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.22/2.90  tff(c_411, plain, (![A_114, B_115]: (r2_hidden('#skF_1'(A_114), B_115) | ~r1_tarski(A_114, B_115) | v1_xboole_0(A_114))), inference(resolution, [status(thm)], [c_4, c_190])).
% 8.22/2.90  tff(c_422, plain, (![B_116, A_117]: (~v1_xboole_0(B_116) | ~r1_tarski(A_117, B_116) | v1_xboole_0(A_117))), inference(resolution, [status(thm)], [c_411, c_2])).
% 8.22/2.90  tff(c_425, plain, (![A_110]: (~v1_xboole_0(k1_xboole_0) | v1_xboole_0(A_110) | k1_xboole_0!=A_110)), inference(resolution, [status(thm)], [c_365, c_422])).
% 8.22/2.90  tff(c_461, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_425])).
% 8.22/2.90  tff(c_76, plain, (k1_xboole_0='#skF_14' | k1_xboole_0='#skF_13' | k2_zfmisc_1('#skF_15', '#skF_16')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_80])).
% 8.22/2.90  tff(c_122, plain, (k2_zfmisc_1('#skF_15', '#skF_16')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_76])).
% 8.22/2.90  tff(c_531, plain, (![E_128, F_129, A_130, B_131]: (r2_hidden(k4_tarski(E_128, F_129), k2_zfmisc_1(A_130, B_131)) | ~r2_hidden(F_129, B_131) | ~r2_hidden(E_128, A_130))), inference(cnfTransformation, [status(thm)], [f_63])).
% 8.22/2.90  tff(c_639, plain, (![E_138, F_139]: (r2_hidden(k4_tarski(E_138, F_139), k1_xboole_0) | ~r2_hidden(F_139, '#skF_16') | ~r2_hidden(E_138, '#skF_15'))), inference(superposition, [status(thm), theory('equality')], [c_122, c_531])).
% 8.22/2.90  tff(c_646, plain, (![F_139, E_138]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(F_139, '#skF_16') | ~r2_hidden(E_138, '#skF_15'))), inference(resolution, [status(thm)], [c_639, c_2])).
% 8.22/2.90  tff(c_653, plain, (![F_139, E_138]: (~r2_hidden(F_139, '#skF_16') | ~r2_hidden(E_138, '#skF_15'))), inference(demodulation, [status(thm), theory('equality')], [c_461, c_646])).
% 8.22/2.90  tff(c_670, plain, (![E_142]: (~r2_hidden(E_142, '#skF_15'))), inference(splitLeft, [status(thm)], [c_653])).
% 8.22/2.90  tff(c_697, plain, (![B_143]: (r1_tarski('#skF_15', B_143))), inference(resolution, [status(thm)], [c_10, c_670])).
% 8.22/2.90  tff(c_16, plain, (![A_10, B_11]: (k4_xboole_0(A_10, B_11)=k1_xboole_0 | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.22/2.90  tff(c_786, plain, (![B_147]: (k4_xboole_0('#skF_15', B_147)=k1_xboole_0)), inference(resolution, [status(thm)], [c_697, c_16])).
% 8.22/2.90  tff(c_804, plain, (k1_xboole_0='#skF_15'), inference(superposition, [status(thm), theory('equality')], [c_786, c_20])).
% 8.22/2.90  tff(c_826, plain, $false, inference(negUnitSimplification, [status(thm)], [c_88, c_804])).
% 8.22/2.90  tff(c_849, plain, (![F_151]: (~r2_hidden(F_151, '#skF_16'))), inference(splitRight, [status(thm)], [c_653])).
% 8.22/2.90  tff(c_876, plain, (![B_152]: (r1_tarski('#skF_16', B_152))), inference(resolution, [status(thm)], [c_10, c_849])).
% 8.22/2.90  tff(c_997, plain, (![B_157]: (k4_xboole_0('#skF_16', B_157)=k1_xboole_0)), inference(resolution, [status(thm)], [c_876, c_16])).
% 8.22/2.90  tff(c_1015, plain, (k1_xboole_0='#skF_16'), inference(superposition, [status(thm), theory('equality')], [c_997, c_20])).
% 8.22/2.90  tff(c_1038, plain, $false, inference(negUnitSimplification, [status(thm)], [c_89, c_1015])).
% 8.22/2.90  tff(c_1039, plain, (k1_xboole_0='#skF_13' | k1_xboole_0='#skF_14'), inference(splitRight, [status(thm)], [c_76])).
% 8.22/2.90  tff(c_1041, plain, (k1_xboole_0='#skF_14'), inference(splitLeft, [status(thm)], [c_1039])).
% 8.22/2.90  tff(c_1050, plain, (v1_xboole_0('#skF_14')), inference(demodulation, [status(thm), theory('equality')], [c_1041, c_12])).
% 8.22/2.90  tff(c_1049, plain, (![A_14]: (k4_xboole_0(A_14, '#skF_14')=A_14)), inference(demodulation, [status(thm), theory('equality')], [c_1041, c_20])).
% 8.22/2.90  tff(c_120, plain, (![A_82, B_83]: (k2_xboole_0(A_82, B_83)=B_83 | k4_xboole_0(A_82, B_83)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_112, c_18])).
% 8.22/2.90  tff(c_1278, plain, (![A_186, B_187]: (k2_xboole_0(A_186, B_187)=B_187 | k4_xboole_0(A_186, B_187)!='#skF_14')), inference(demodulation, [status(thm), theory('equality')], [c_1041, c_120])).
% 8.22/2.90  tff(c_1305, plain, (![A_191]: (k2_xboole_0(A_191, '#skF_14')='#skF_14' | A_191!='#skF_14')), inference(superposition, [status(thm), theory('equality')], [c_1049, c_1278])).
% 8.22/2.90  tff(c_1325, plain, (![A_191]: (r1_tarski(A_191, '#skF_14') | A_191!='#skF_14')), inference(superposition, [status(thm), theory('equality')], [c_1305, c_22])).
% 8.22/2.90  tff(c_1175, plain, (![C_179, B_180, A_181]: (r2_hidden(C_179, B_180) | ~r2_hidden(C_179, A_181) | ~r1_tarski(A_181, B_180))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.22/2.90  tff(c_1371, plain, (![A_195, B_196]: (r2_hidden('#skF_1'(A_195), B_196) | ~r1_tarski(A_195, B_196) | v1_xboole_0(A_195))), inference(resolution, [status(thm)], [c_4, c_1175])).
% 8.22/2.90  tff(c_1382, plain, (![B_197, A_198]: (~v1_xboole_0(B_197) | ~r1_tarski(A_198, B_197) | v1_xboole_0(A_198))), inference(resolution, [status(thm)], [c_1371, c_2])).
% 8.22/2.90  tff(c_1385, plain, (![A_191]: (~v1_xboole_0('#skF_14') | v1_xboole_0(A_191) | A_191!='#skF_14')), inference(resolution, [status(thm)], [c_1325, c_1382])).
% 8.22/2.90  tff(c_1403, plain, (![A_191]: (v1_xboole_0(A_191) | A_191!='#skF_14')), inference(demodulation, [status(thm), theory('equality')], [c_1050, c_1385])).
% 8.22/2.90  tff(c_1478, plain, (![A_204, C_205]: (r2_hidden('#skF_12'(A_204, k3_tarski(A_204), C_205), A_204) | ~r2_hidden(C_205, k3_tarski(A_204)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 8.22/2.90  tff(c_1489, plain, (![A_206, C_207]: (~v1_xboole_0(A_206) | ~r2_hidden(C_207, k3_tarski(A_206)))), inference(resolution, [status(thm)], [c_1478, c_2])).
% 8.22/2.90  tff(c_1517, plain, (![A_209, B_210]: (~v1_xboole_0(A_209) | r1_tarski(k3_tarski(A_209), B_210))), inference(resolution, [status(thm)], [c_10, c_1489])).
% 8.22/2.90  tff(c_1046, plain, (![A_10, B_11]: (k4_xboole_0(A_10, B_11)='#skF_14' | ~r1_tarski(A_10, B_11))), inference(demodulation, [status(thm), theory('equality')], [c_1041, c_16])).
% 8.22/2.90  tff(c_1761, plain, (![A_232, B_233]: (k4_xboole_0(k3_tarski(A_232), B_233)='#skF_14' | ~v1_xboole_0(A_232))), inference(resolution, [status(thm)], [c_1517, c_1046])).
% 8.22/2.90  tff(c_1807, plain, (![A_234]: (k3_tarski(A_234)='#skF_14' | ~v1_xboole_0(A_234))), inference(superposition, [status(thm), theory('equality')], [c_1761, c_1049])).
% 8.22/2.90  tff(c_1820, plain, (k3_tarski('#skF_14')='#skF_14'), inference(resolution, [status(thm)], [c_1403, c_1807])).
% 8.22/2.90  tff(c_1821, plain, (![A_235]: (k3_tarski(A_235)='#skF_14' | A_235!='#skF_14')), inference(resolution, [status(thm)], [c_1403, c_1807])).
% 8.22/2.90  tff(c_50, plain, (![A_51, C_66]: (r2_hidden('#skF_12'(A_51, k3_tarski(A_51), C_66), A_51) | ~r2_hidden(C_66, k3_tarski(A_51)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 8.22/2.90  tff(c_1506, plain, (![A_206, C_66]: (~v1_xboole_0(A_206) | ~r2_hidden(C_66, k3_tarski(k3_tarski(A_206))))), inference(resolution, [status(thm)], [c_50, c_1489])).
% 8.22/2.90  tff(c_1845, plain, (![A_235, C_66]: (~v1_xboole_0(A_235) | ~r2_hidden(C_66, k3_tarski('#skF_14')) | A_235!='#skF_14')), inference(superposition, [status(thm), theory('equality')], [c_1821, c_1506])).
% 8.22/2.90  tff(c_1874, plain, (![A_235, C_66]: (~v1_xboole_0(A_235) | ~r2_hidden(C_66, '#skF_14') | A_235!='#skF_14')), inference(demodulation, [status(thm), theory('equality')], [c_1820, c_1845])).
% 8.22/2.90  tff(c_2400, plain, (![A_269]: (~v1_xboole_0(A_269) | A_269!='#skF_14')), inference(splitLeft, [status(thm)], [c_1874])).
% 8.22/2.90  tff(c_2420, plain, (![A_191]: (A_191!='#skF_14')), inference(resolution, [status(thm)], [c_1403, c_2400])).
% 8.22/2.90  tff(c_1160, plain, (![A_176, B_177]: (~r2_hidden('#skF_2'(A_176, B_177), B_177) | r1_tarski(A_176, B_177))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.22/2.90  tff(c_1166, plain, (![A_178]: (r1_tarski(A_178, A_178))), inference(resolution, [status(thm)], [c_10, c_1160])).
% 8.22/2.90  tff(c_1173, plain, (![A_178]: (k4_xboole_0(A_178, A_178)='#skF_14')), inference(resolution, [status(thm)], [c_1166, c_1046])).
% 8.22/2.90  tff(c_2434, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2420, c_1173])).
% 8.22/2.90  tff(c_2436, plain, (![C_270]: (~r2_hidden(C_270, '#skF_14'))), inference(splitRight, [status(thm)], [c_1874])).
% 8.22/2.90  tff(c_2676, plain, (![D_281, A_282]: (~r2_hidden(D_281, k2_zfmisc_1(A_282, '#skF_14')))), inference(resolution, [status(thm)], [c_28, c_2436])).
% 8.22/2.90  tff(c_2737, plain, (![A_283]: (v1_xboole_0(k2_zfmisc_1(A_283, '#skF_14')))), inference(resolution, [status(thm)], [c_4, c_2676])).
% 8.22/2.90  tff(c_1076, plain, (![A_163, B_164]: (r2_hidden('#skF_2'(A_163, B_164), A_163) | r1_tarski(A_163, B_164))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.22/2.90  tff(c_1080, plain, (![A_163, B_164]: (~v1_xboole_0(A_163) | r1_tarski(A_163, B_164))), inference(resolution, [status(thm)], [c_1076, c_2])).
% 8.22/2.90  tff(c_1136, plain, (![A_172, B_173]: (k4_xboole_0(A_172, B_173)='#skF_14' | ~r1_tarski(A_172, B_173))), inference(demodulation, [status(thm), theory('equality')], [c_1041, c_16])).
% 8.22/2.90  tff(c_1151, plain, (![A_163, B_164]: (k4_xboole_0(A_163, B_164)='#skF_14' | ~v1_xboole_0(A_163))), inference(resolution, [status(thm)], [c_1080, c_1136])).
% 8.22/2.90  tff(c_3378, plain, (![A_306, B_307]: (k4_xboole_0(k2_zfmisc_1(A_306, '#skF_14'), B_307)='#skF_14')), inference(resolution, [status(thm)], [c_2737, c_1151])).
% 8.22/2.90  tff(c_3396, plain, (![A_306]: (k2_zfmisc_1(A_306, '#skF_14')='#skF_14')), inference(superposition, [status(thm), theory('equality')], [c_3378, c_1049])).
% 8.22/2.90  tff(c_74, plain, (k2_zfmisc_1('#skF_13', '#skF_14')!=k1_xboole_0 | k2_zfmisc_1('#skF_15', '#skF_16')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_80])).
% 8.22/2.90  tff(c_121, plain, (k2_zfmisc_1('#skF_13', '#skF_14')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_74])).
% 8.22/2.90  tff(c_1043, plain, (k2_zfmisc_1('#skF_13', '#skF_14')!='#skF_14'), inference(demodulation, [status(thm), theory('equality')], [c_1041, c_121])).
% 8.22/2.90  tff(c_3460, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3396, c_1043])).
% 8.22/2.90  tff(c_3461, plain, (k1_xboole_0='#skF_13'), inference(splitRight, [status(thm)], [c_1039])).
% 8.22/2.90  tff(c_3471, plain, (v1_xboole_0('#skF_13')), inference(demodulation, [status(thm), theory('equality')], [c_3461, c_12])).
% 8.22/2.90  tff(c_3674, plain, (![A_342, C_343]: (r2_hidden('#skF_12'(A_342, k3_tarski(A_342), C_343), A_342) | ~r2_hidden(C_343, k3_tarski(A_342)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 8.22/2.90  tff(c_3685, plain, (![A_344, C_345]: (~v1_xboole_0(A_344) | ~r2_hidden(C_345, k3_tarski(A_344)))), inference(resolution, [status(thm)], [c_3674, c_2])).
% 8.22/2.90  tff(c_3701, plain, (![A_346]: (~v1_xboole_0(A_346) | v1_xboole_0(k3_tarski(A_346)))), inference(resolution, [status(thm)], [c_4, c_3685])).
% 8.22/2.90  tff(c_3509, plain, (![A_320, B_321]: (r2_hidden('#skF_2'(A_320, B_321), A_320) | r1_tarski(A_320, B_321))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.22/2.90  tff(c_3576, plain, (![A_331, B_332]: (~v1_xboole_0(A_331) | r1_tarski(A_331, B_332))), inference(resolution, [status(thm)], [c_3509, c_2])).
% 8.22/2.90  tff(c_3467, plain, (![A_10, B_11]: (k4_xboole_0(A_10, B_11)='#skF_13' | ~r1_tarski(A_10, B_11))), inference(demodulation, [status(thm), theory('equality')], [c_3461, c_16])).
% 8.22/2.90  tff(c_3583, plain, (![A_331, B_332]: (k4_xboole_0(A_331, B_332)='#skF_13' | ~v1_xboole_0(A_331))), inference(resolution, [status(thm)], [c_3576, c_3467])).
% 8.22/2.90  tff(c_3836, plain, (![A_360, B_361]: (k4_xboole_0(k3_tarski(A_360), B_361)='#skF_13' | ~v1_xboole_0(A_360))), inference(resolution, [status(thm)], [c_3701, c_3583])).
% 8.22/2.90  tff(c_3470, plain, (![A_14]: (k4_xboole_0(A_14, '#skF_13')=A_14)), inference(demodulation, [status(thm), theory('equality')], [c_3461, c_20])).
% 8.22/2.90  tff(c_3869, plain, (![A_362]: (k3_tarski(A_362)='#skF_13' | ~v1_xboole_0(A_362))), inference(superposition, [status(thm), theory('equality')], [c_3836, c_3470])).
% 8.22/2.90  tff(c_3881, plain, (k3_tarski('#skF_13')='#skF_13'), inference(resolution, [status(thm)], [c_3471, c_3869])).
% 8.22/2.90  tff(c_3698, plain, (![A_344, C_66]: (~v1_xboole_0(A_344) | ~r2_hidden(C_66, k3_tarski(k3_tarski(A_344))))), inference(resolution, [status(thm)], [c_50, c_3685])).
% 8.22/2.90  tff(c_3897, plain, (![C_66]: (~v1_xboole_0('#skF_13') | ~r2_hidden(C_66, k3_tarski('#skF_13')))), inference(superposition, [status(thm), theory('equality')], [c_3881, c_3698])).
% 8.22/2.90  tff(c_3924, plain, (![C_66]: (~r2_hidden(C_66, '#skF_13'))), inference(demodulation, [status(thm), theory('equality')], [c_3881, c_3471, c_3897])).
% 8.22/2.90  tff(c_4072, plain, (![D_372, B_373]: (~r2_hidden(D_372, k2_zfmisc_1('#skF_13', B_373)))), inference(resolution, [status(thm)], [c_4046, c_3924])).
% 8.22/2.90  tff(c_4124, plain, (![B_375, B_376]: (r1_tarski(k2_zfmisc_1('#skF_13', B_375), B_376))), inference(resolution, [status(thm)], [c_10, c_4072])).
% 8.22/2.90  tff(c_4373, plain, (![B_389, B_390]: (k4_xboole_0(k2_zfmisc_1('#skF_13', B_389), B_390)='#skF_13')), inference(resolution, [status(thm)], [c_4124, c_3467])).
% 8.22/2.90  tff(c_4385, plain, (![B_389]: (k2_zfmisc_1('#skF_13', B_389)='#skF_13')), inference(superposition, [status(thm), theory('equality')], [c_4373, c_3470])).
% 8.22/2.90  tff(c_3464, plain, (k2_zfmisc_1('#skF_13', '#skF_14')!='#skF_13'), inference(demodulation, [status(thm), theory('equality')], [c_3461, c_121])).
% 8.22/2.90  tff(c_4415, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4385, c_3464])).
% 8.22/2.90  tff(c_4417, plain, (k2_zfmisc_1('#skF_13', '#skF_14')=k1_xboole_0), inference(splitRight, [status(thm)], [c_74])).
% 8.22/2.90  tff(c_4870, plain, (![E_437, F_438, A_439, B_440]: (r2_hidden(k4_tarski(E_437, F_438), k2_zfmisc_1(A_439, B_440)) | ~r2_hidden(F_438, B_440) | ~r2_hidden(E_437, A_439))), inference(cnfTransformation, [status(thm)], [f_63])).
% 8.22/2.90  tff(c_4957, plain, (![E_447, F_448]: (r2_hidden(k4_tarski(E_447, F_448), k1_xboole_0) | ~r2_hidden(F_448, '#skF_14') | ~r2_hidden(E_447, '#skF_13'))), inference(superposition, [status(thm), theory('equality')], [c_4417, c_4870])).
% 8.22/2.90  tff(c_4964, plain, (![F_448, E_447]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(F_448, '#skF_14') | ~r2_hidden(E_447, '#skF_13'))), inference(resolution, [status(thm)], [c_4957, c_2])).
% 8.22/2.90  tff(c_4971, plain, (![F_448, E_447]: (~r2_hidden(F_448, '#skF_14') | ~r2_hidden(E_447, '#skF_13'))), inference(demodulation, [status(thm), theory('equality')], [c_4750, c_4964])).
% 8.22/2.90  tff(c_4973, plain, (![E_449]: (~r2_hidden(E_449, '#skF_13'))), inference(splitLeft, [status(thm)], [c_4971])).
% 8.22/2.90  tff(c_4993, plain, (v1_xboole_0('#skF_13')), inference(resolution, [status(thm)], [c_4, c_4973])).
% 8.22/2.90  tff(c_4426, plain, (![A_391, B_392]: (r2_hidden('#skF_2'(A_391, B_392), A_391) | r1_tarski(A_391, B_392))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.22/2.90  tff(c_4431, plain, (![A_393, B_394]: (~v1_xboole_0(A_393) | r1_tarski(A_393, B_394))), inference(resolution, [status(thm)], [c_4426, c_2])).
% 8.22/2.90  tff(c_4438, plain, (![A_393, B_394]: (k4_xboole_0(A_393, B_394)=k1_xboole_0 | ~v1_xboole_0(A_393))), inference(resolution, [status(thm)], [c_4431, c_16])).
% 8.22/2.90  tff(c_5153, plain, (![B_458]: (k4_xboole_0('#skF_13', B_458)=k1_xboole_0)), inference(resolution, [status(thm)], [c_4993, c_4438])).
% 8.22/2.90  tff(c_5171, plain, (k1_xboole_0='#skF_13'), inference(superposition, [status(thm), theory('equality')], [c_5153, c_20])).
% 8.22/2.90  tff(c_5213, plain, ('#skF_16'!='#skF_13'), inference(demodulation, [status(thm), theory('equality')], [c_5171, c_89])).
% 8.22/2.90  tff(c_5222, plain, (![A_459, B_460]: (r2_hidden('#skF_10'(A_459, B_460), A_459) | r2_hidden('#skF_11'(A_459, B_460), B_460) | k3_tarski(A_459)=B_460)), inference(cnfTransformation, [status(thm)], [f_73])).
% 8.22/2.90  tff(c_4972, plain, (![E_447]: (~r2_hidden(E_447, '#skF_13'))), inference(splitLeft, [status(thm)], [c_4971])).
% 8.22/2.90  tff(c_8440, plain, (![A_598]: (r2_hidden('#skF_10'(A_598, '#skF_13'), A_598) | k3_tarski(A_598)='#skF_13')), inference(resolution, [status(thm)], [c_5222, c_4972])).
% 8.22/2.90  tff(c_5214, plain, ('#skF_15'!='#skF_13'), inference(demodulation, [status(thm), theory('equality')], [c_5171, c_88])).
% 8.22/2.90  tff(c_5014, plain, (![C_451]: (~r2_hidden(C_451, k3_tarski('#skF_13')))), inference(resolution, [status(thm)], [c_50, c_4973])).
% 8.22/2.90  tff(c_5067, plain, (![B_454]: (r1_tarski(k3_tarski('#skF_13'), B_454))), inference(resolution, [status(thm)], [c_10, c_5014])).
% 8.22/2.90  tff(c_5079, plain, (![B_454]: (k4_xboole_0(k3_tarski('#skF_13'), B_454)=k1_xboole_0)), inference(resolution, [status(thm)], [c_5067, c_16])).
% 8.22/2.90  tff(c_5617, plain, (![B_479]: (k4_xboole_0(k3_tarski('#skF_13'), B_479)='#skF_13')), inference(demodulation, [status(thm), theory('equality')], [c_5171, c_5079])).
% 8.22/2.90  tff(c_5215, plain, (![A_14]: (k4_xboole_0(A_14, '#skF_13')=A_14)), inference(demodulation, [status(thm), theory('equality')], [c_5171, c_20])).
% 8.22/2.90  tff(c_5623, plain, (k3_tarski('#skF_13')='#skF_13'), inference(superposition, [status(thm), theory('equality')], [c_5617, c_5215])).
% 8.22/2.90  tff(c_62, plain, (![A_51, B_52]: (r2_hidden('#skF_10'(A_51, B_52), A_51) | r2_hidden('#skF_11'(A_51, B_52), B_52) | k3_tarski(A_51)=B_52)), inference(cnfTransformation, [status(thm)], [f_73])).
% 8.22/2.90  tff(c_4416, plain, (k2_zfmisc_1('#skF_15', '#skF_16')=k1_xboole_0), inference(splitRight, [status(thm)], [c_74])).
% 8.22/2.90  tff(c_5137, plain, (![E_456, F_457]: (r2_hidden(k4_tarski(E_456, F_457), k1_xboole_0) | ~r2_hidden(F_457, '#skF_16') | ~r2_hidden(E_456, '#skF_15'))), inference(superposition, [status(thm), theory('equality')], [c_4416, c_4870])).
% 8.22/2.90  tff(c_5144, plain, (![F_457, E_456]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(F_457, '#skF_16') | ~r2_hidden(E_456, '#skF_15'))), inference(resolution, [status(thm)], [c_5137, c_2])).
% 8.22/2.90  tff(c_5151, plain, (![F_457, E_456]: (~r2_hidden(F_457, '#skF_16') | ~r2_hidden(E_456, '#skF_15'))), inference(demodulation, [status(thm), theory('equality')], [c_4750, c_5144])).
% 8.22/2.90  tff(c_5834, plain, (![E_492]: (~r2_hidden(E_492, '#skF_15'))), inference(splitLeft, [status(thm)], [c_5151])).
% 8.22/2.90  tff(c_6960, plain, (![A_538]: (r2_hidden('#skF_10'(A_538, '#skF_15'), A_538) | k3_tarski(A_538)='#skF_15')), inference(resolution, [status(thm)], [c_62, c_5834])).
% 8.22/2.90  tff(c_7008, plain, (k3_tarski('#skF_13')='#skF_15'), inference(resolution, [status(thm)], [c_6960, c_4972])).
% 8.22/2.90  tff(c_7032, plain, ('#skF_15'='#skF_13'), inference(demodulation, [status(thm), theory('equality')], [c_5623, c_7008])).
% 8.22/2.90  tff(c_7034, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5214, c_7032])).
% 8.22/2.90  tff(c_7036, plain, (![F_539]: (~r2_hidden(F_539, '#skF_16'))), inference(splitRight, [status(thm)], [c_5151])).
% 8.22/2.90  tff(c_7071, plain, (![D_44, A_17]: (~r2_hidden(D_44, k2_zfmisc_1(A_17, '#skF_16')))), inference(resolution, [status(thm)], [c_28, c_7036])).
% 8.22/2.90  tff(c_8515, plain, (![A_17]: (k3_tarski(k2_zfmisc_1(A_17, '#skF_16'))='#skF_13')), inference(resolution, [status(thm)], [c_8440, c_7071])).
% 8.22/2.90  tff(c_8832, plain, (![A_607]: (r2_hidden('#skF_10'(A_607, '#skF_16'), A_607) | k3_tarski(A_607)='#skF_16')), inference(resolution, [status(thm)], [c_62, c_7036])).
% 8.22/2.90  tff(c_8836, plain, (![A_17]: (k3_tarski(k2_zfmisc_1(A_17, '#skF_16'))='#skF_16')), inference(resolution, [status(thm)], [c_8832, c_7071])).
% 8.22/2.90  tff(c_8869, plain, ('#skF_16'='#skF_13'), inference(demodulation, [status(thm), theory('equality')], [c_8515, c_8836])).
% 8.22/2.90  tff(c_8871, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5213, c_8869])).
% 8.22/2.90  tff(c_8873, plain, (![F_608]: (~r2_hidden(F_608, '#skF_14'))), inference(splitRight, [status(thm)], [c_4971])).
% 8.22/2.90  tff(c_8893, plain, (v1_xboole_0('#skF_14')), inference(resolution, [status(thm)], [c_4, c_8873])).
% 8.22/2.90  tff(c_8967, plain, (![B_613]: (k4_xboole_0('#skF_14', B_613)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8893, c_4438])).
% 8.22/2.90  tff(c_8985, plain, (k1_xboole_0='#skF_14'), inference(superposition, [status(thm), theory('equality')], [c_8967, c_20])).
% 8.22/2.90  tff(c_9025, plain, ('#skF_16'!='#skF_14'), inference(demodulation, [status(thm), theory('equality')], [c_8985, c_89])).
% 8.22/2.90  tff(c_9093, plain, (![A_617, B_618]: (r2_hidden('#skF_10'(A_617, B_618), A_617) | r2_hidden('#skF_11'(A_617, B_618), B_618) | k3_tarski(A_617)=B_618)), inference(cnfTransformation, [status(thm)], [f_73])).
% 8.22/2.90  tff(c_8872, plain, (![F_448]: (~r2_hidden(F_448, '#skF_14'))), inference(splitRight, [status(thm)], [c_4971])).
% 8.22/2.90  tff(c_11736, plain, (![A_725]: (r2_hidden('#skF_10'(A_725, '#skF_14'), A_725) | k3_tarski(A_725)='#skF_14')), inference(resolution, [status(thm)], [c_9093, c_8872])).
% 8.22/2.90  tff(c_10902, plain, (![A_686, B_687, D_688]: (r2_hidden('#skF_7'(A_686, B_687, k2_zfmisc_1(A_686, B_687), D_688), A_686) | ~r2_hidden(D_688, k2_zfmisc_1(A_686, B_687)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 8.22/2.90  tff(c_9026, plain, ('#skF_15'!='#skF_14'), inference(demodulation, [status(thm), theory('equality')], [c_8985, c_88])).
% 8.22/2.90  tff(c_10316, plain, (![A_672]: (r2_hidden('#skF_10'(A_672, '#skF_14'), A_672) | k3_tarski(A_672)='#skF_14')), inference(resolution, [status(thm)], [c_9093, c_8872])).
% 8.22/2.90  tff(c_9480, plain, (![A_633, B_634, D_635]: (r2_hidden('#skF_7'(A_633, B_634, k2_zfmisc_1(A_633, B_634), D_635), A_633) | ~r2_hidden(D_635, k2_zfmisc_1(A_633, B_634)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 8.22/2.90  tff(c_4883, plain, (![E_437, F_438]: (r2_hidden(k4_tarski(E_437, F_438), k1_xboole_0) | ~r2_hidden(F_438, '#skF_16') | ~r2_hidden(E_437, '#skF_15'))), inference(superposition, [status(thm), theory('equality')], [c_4416, c_4870])).
% 8.22/2.90  tff(c_9376, plain, (![E_437, F_438]: (r2_hidden(k4_tarski(E_437, F_438), '#skF_14') | ~r2_hidden(F_438, '#skF_16') | ~r2_hidden(E_437, '#skF_15'))), inference(demodulation, [status(thm), theory('equality')], [c_8985, c_4883])).
% 8.22/2.90  tff(c_9377, plain, (![F_438, E_437]: (~r2_hidden(F_438, '#skF_16') | ~r2_hidden(E_437, '#skF_15'))), inference(negUnitSimplification, [status(thm)], [c_8872, c_9376])).
% 8.22/2.90  tff(c_9378, plain, (![E_437]: (~r2_hidden(E_437, '#skF_15'))), inference(splitLeft, [status(thm)], [c_9377])).
% 8.22/2.90  tff(c_9523, plain, (![D_635, B_634]: (~r2_hidden(D_635, k2_zfmisc_1('#skF_15', B_634)))), inference(resolution, [status(thm)], [c_9480, c_9378])).
% 8.22/2.90  tff(c_10361, plain, (![B_634]: (k3_tarski(k2_zfmisc_1('#skF_15', B_634))='#skF_14')), inference(resolution, [status(thm)], [c_10316, c_9523])).
% 8.22/2.90  tff(c_9379, plain, (![E_630]: (~r2_hidden(E_630, '#skF_15'))), inference(splitLeft, [status(thm)], [c_9377])).
% 8.22/2.90  tff(c_10760, plain, (![A_682]: (r2_hidden('#skF_10'(A_682, '#skF_15'), A_682) | k3_tarski(A_682)='#skF_15')), inference(resolution, [status(thm)], [c_62, c_9379])).
% 8.22/2.90  tff(c_10764, plain, (![B_634]: (k3_tarski(k2_zfmisc_1('#skF_15', B_634))='#skF_15')), inference(resolution, [status(thm)], [c_10760, c_9523])).
% 8.22/2.90  tff(c_10797, plain, ('#skF_15'='#skF_14'), inference(demodulation, [status(thm), theory('equality')], [c_10361, c_10764])).
% 8.22/2.90  tff(c_10799, plain, $false, inference(negUnitSimplification, [status(thm)], [c_9026, c_10797])).
% 8.22/2.90  tff(c_10800, plain, (![F_438]: (~r2_hidden(F_438, '#skF_16'))), inference(splitRight, [status(thm)], [c_9377])).
% 8.22/2.90  tff(c_10945, plain, (![D_688, B_687]: (~r2_hidden(D_688, k2_zfmisc_1('#skF_16', B_687)))), inference(resolution, [status(thm)], [c_10902, c_10800])).
% 8.22/2.90  tff(c_11781, plain, (![B_687]: (k3_tarski(k2_zfmisc_1('#skF_16', B_687))='#skF_14')), inference(resolution, [status(thm)], [c_11736, c_10945])).
% 8.22/2.90  tff(c_10801, plain, (![F_683]: (~r2_hidden(F_683, '#skF_16'))), inference(splitRight, [status(thm)], [c_9377])).
% 8.22/2.90  tff(c_12180, plain, (![A_735]: (r2_hidden('#skF_10'(A_735, '#skF_16'), A_735) | k3_tarski(A_735)='#skF_16')), inference(resolution, [status(thm)], [c_62, c_10801])).
% 8.22/2.90  tff(c_12184, plain, (![B_687]: (k3_tarski(k2_zfmisc_1('#skF_16', B_687))='#skF_16')), inference(resolution, [status(thm)], [c_12180, c_10945])).
% 8.22/2.90  tff(c_12217, plain, ('#skF_16'='#skF_14'), inference(demodulation, [status(thm), theory('equality')], [c_11781, c_12184])).
% 8.22/2.90  tff(c_12219, plain, $false, inference(negUnitSimplification, [status(thm)], [c_9025, c_12217])).
% 8.22/2.90  tff(c_12221, plain, (k1_xboole_0='#skF_16'), inference(splitRight, [status(thm)], [c_66])).
% 8.22/2.90  tff(c_68, plain, (k1_xboole_0='#skF_14' | k1_xboole_0='#skF_13' | k1_xboole_0!='#skF_16'), inference(cnfTransformation, [status(thm)], [f_80])).
% 8.22/2.90  tff(c_12240, plain, ('#skF_16'='#skF_14' | '#skF_16'='#skF_13'), inference(demodulation, [status(thm), theory('equality')], [c_12221, c_12221, c_12221, c_68])).
% 8.22/2.90  tff(c_12241, plain, ('#skF_16'='#skF_13'), inference(splitLeft, [status(thm)], [c_12240])).
% 8.22/2.90  tff(c_12224, plain, (v1_xboole_0('#skF_16')), inference(demodulation, [status(thm), theory('equality')], [c_12221, c_12])).
% 8.22/2.90  tff(c_12244, plain, (v1_xboole_0('#skF_13')), inference(demodulation, [status(thm), theory('equality')], [c_12241, c_12224])).
% 8.22/2.90  tff(c_12223, plain, (![A_14]: (k4_xboole_0(A_14, '#skF_16')=A_14)), inference(demodulation, [status(thm), theory('equality')], [c_12221, c_20])).
% 8.22/2.90  tff(c_12242, plain, (![A_14]: (k4_xboole_0(A_14, '#skF_13')=A_14)), inference(demodulation, [status(thm), theory('equality')], [c_12241, c_12223])).
% 8.22/2.90  tff(c_12246, plain, (k1_xboole_0='#skF_13'), inference(demodulation, [status(thm), theory('equality')], [c_12241, c_12221])).
% 8.22/2.90  tff(c_14, plain, (![A_10, B_11]: (r1_tarski(A_10, B_11) | k4_xboole_0(A_10, B_11)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.22/2.90  tff(c_12271, plain, (![A_10, B_11]: (r1_tarski(A_10, B_11) | k4_xboole_0(A_10, B_11)!='#skF_13')), inference(demodulation, [status(thm), theory('equality')], [c_12246, c_14])).
% 8.22/2.90  tff(c_12273, plain, (![A_741, B_742]: (k2_xboole_0(A_741, B_742)=B_742 | ~r1_tarski(A_741, B_742))), inference(cnfTransformation, [status(thm)], [f_47])).
% 8.22/2.90  tff(c_12499, plain, (![A_771, B_772]: (k2_xboole_0(A_771, B_772)=B_772 | k4_xboole_0(A_771, B_772)!='#skF_13')), inference(resolution, [status(thm)], [c_12271, c_12273])).
% 8.22/2.90  tff(c_12519, plain, (![A_773]: (k2_xboole_0(A_773, '#skF_13')='#skF_13' | A_773!='#skF_13')), inference(superposition, [status(thm), theory('equality')], [c_12242, c_12499])).
% 8.22/2.90  tff(c_12539, plain, (![A_773]: (r1_tarski(A_773, '#skF_13') | A_773!='#skF_13')), inference(superposition, [status(thm), theory('equality')], [c_12519, c_22])).
% 8.22/2.90  tff(c_12385, plain, (![C_759, B_760, A_761]: (r2_hidden(C_759, B_760) | ~r2_hidden(C_759, A_761) | ~r1_tarski(A_761, B_760))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.22/2.90  tff(c_12585, plain, (![A_777, B_778]: (r2_hidden('#skF_1'(A_777), B_778) | ~r1_tarski(A_777, B_778) | v1_xboole_0(A_777))), inference(resolution, [status(thm)], [c_4, c_12385])).
% 8.22/2.90  tff(c_12596, plain, (![B_779, A_780]: (~v1_xboole_0(B_779) | ~r1_tarski(A_780, B_779) | v1_xboole_0(A_780))), inference(resolution, [status(thm)], [c_12585, c_2])).
% 8.22/2.90  tff(c_12599, plain, (![A_773]: (~v1_xboole_0('#skF_13') | v1_xboole_0(A_773) | A_773!='#skF_13')), inference(resolution, [status(thm)], [c_12539, c_12596])).
% 8.22/2.90  tff(c_12617, plain, (![A_773]: (v1_xboole_0(A_773) | A_773!='#skF_13')), inference(demodulation, [status(thm), theory('equality')], [c_12244, c_12599])).
% 8.22/2.90  tff(c_12653, plain, (![A_784, C_785]: (r2_hidden('#skF_12'(A_784, k3_tarski(A_784), C_785), A_784) | ~r2_hidden(C_785, k3_tarski(A_784)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 8.22/2.90  tff(c_12664, plain, (![A_786, C_787]: (~v1_xboole_0(A_786) | ~r2_hidden(C_787, k3_tarski(A_786)))), inference(resolution, [status(thm)], [c_12653, c_2])).
% 8.22/2.90  tff(c_12692, plain, (![A_789, B_790]: (~v1_xboole_0(A_789) | r1_tarski(k3_tarski(A_789), B_790))), inference(resolution, [status(thm)], [c_10, c_12664])).
% 8.22/2.90  tff(c_12282, plain, (![A_10, B_11]: (k4_xboole_0(A_10, B_11)='#skF_13' | ~r1_tarski(A_10, B_11))), inference(demodulation, [status(thm), theory('equality')], [c_12246, c_16])).
% 8.22/2.90  tff(c_12981, plain, (![A_814, B_815]: (k4_xboole_0(k3_tarski(A_814), B_815)='#skF_13' | ~v1_xboole_0(A_814))), inference(resolution, [status(thm)], [c_12692, c_12282])).
% 8.22/2.90  tff(c_13027, plain, (![A_816]: (k3_tarski(A_816)='#skF_13' | ~v1_xboole_0(A_816))), inference(superposition, [status(thm), theory('equality')], [c_12981, c_12242])).
% 8.22/2.90  tff(c_13061, plain, (k3_tarski('#skF_13')='#skF_13'), inference(resolution, [status(thm)], [c_12617, c_13027])).
% 8.22/2.90  tff(c_13062, plain, (![A_820]: (k3_tarski(A_820)='#skF_13' | A_820!='#skF_13')), inference(resolution, [status(thm)], [c_12617, c_13027])).
% 8.22/2.90  tff(c_12681, plain, (![A_786, C_66]: (~v1_xboole_0(A_786) | ~r2_hidden(C_66, k3_tarski(k3_tarski(A_786))))), inference(resolution, [status(thm)], [c_50, c_12664])).
% 8.22/2.90  tff(c_13086, plain, (![A_820, C_66]: (~v1_xboole_0(A_820) | ~r2_hidden(C_66, k3_tarski('#skF_13')) | A_820!='#skF_13')), inference(superposition, [status(thm), theory('equality')], [c_13062, c_12681])).
% 8.22/2.90  tff(c_13115, plain, (![A_820, C_66]: (~v1_xboole_0(A_820) | ~r2_hidden(C_66, '#skF_13') | A_820!='#skF_13')), inference(demodulation, [status(thm), theory('equality')], [c_13061, c_13086])).
% 8.22/2.90  tff(c_13680, plain, (![A_851]: (~v1_xboole_0(A_851) | A_851!='#skF_13')), inference(splitLeft, [status(thm)], [c_13115])).
% 8.22/2.90  tff(c_13700, plain, (![A_773]: (A_773!='#skF_13')), inference(resolution, [status(thm)], [c_12617, c_13680])).
% 8.22/2.90  tff(c_12334, plain, (![A_754, B_755]: (~r2_hidden('#skF_2'(A_754, B_755), B_755) | r1_tarski(A_754, B_755))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.22/2.90  tff(c_12340, plain, (![A_756]: (r1_tarski(A_756, A_756))), inference(resolution, [status(thm)], [c_10, c_12334])).
% 8.22/2.90  tff(c_12347, plain, (![A_756]: (k4_xboole_0(A_756, A_756)='#skF_13')), inference(resolution, [status(thm)], [c_12340, c_12282])).
% 8.22/2.90  tff(c_13746, plain, $false, inference(negUnitSimplification, [status(thm)], [c_13700, c_12347])).
% 8.22/2.90  tff(c_13748, plain, (![C_855]: (~r2_hidden(C_855, '#skF_13'))), inference(splitRight, [status(thm)], [c_13115])).
% 8.22/2.90  tff(c_13957, plain, (![D_863, B_864]: (~r2_hidden(D_863, k2_zfmisc_1('#skF_13', B_864)))), inference(resolution, [status(thm)], [c_30, c_13748])).
% 8.22/2.90  tff(c_14055, plain, (![B_871, B_872]: (r1_tarski(k2_zfmisc_1('#skF_13', B_871), B_872))), inference(resolution, [status(thm)], [c_10, c_13957])).
% 8.22/2.90  tff(c_14286, plain, (![B_878, B_879]: (k4_xboole_0(k2_zfmisc_1('#skF_13', B_878), B_879)='#skF_13')), inference(resolution, [status(thm)], [c_14055, c_12282])).
% 8.22/2.90  tff(c_14304, plain, (![B_878]: (k2_zfmisc_1('#skF_13', B_878)='#skF_13')), inference(superposition, [status(thm), theory('equality')], [c_14286, c_12242])).
% 8.22/2.90  tff(c_12220, plain, (k2_zfmisc_1('#skF_13', '#skF_14')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_66])).
% 8.22/2.90  tff(c_12229, plain, (k2_zfmisc_1('#skF_13', '#skF_14')!='#skF_16'), inference(demodulation, [status(thm), theory('equality')], [c_12221, c_12220])).
% 8.22/2.90  tff(c_12243, plain, (k2_zfmisc_1('#skF_13', '#skF_14')!='#skF_13'), inference(demodulation, [status(thm), theory('equality')], [c_12241, c_12229])).
% 8.22/2.90  tff(c_14341, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14304, c_12243])).
% 8.22/2.90  tff(c_14342, plain, ('#skF_16'='#skF_14'), inference(splitRight, [status(thm)], [c_12240])).
% 8.22/2.90  tff(c_14346, plain, (v1_xboole_0('#skF_14')), inference(demodulation, [status(thm), theory('equality')], [c_14342, c_12224])).
% 8.22/2.90  tff(c_14689, plain, (![A_920, C_921]: (r2_hidden('#skF_12'(A_920, k3_tarski(A_920), C_921), A_920) | ~r2_hidden(C_921, k3_tarski(A_920)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 8.22/2.90  tff(c_14700, plain, (![A_922, C_923]: (~v1_xboole_0(A_922) | ~r2_hidden(C_923, k3_tarski(A_922)))), inference(resolution, [status(thm)], [c_14689, c_2])).
% 8.22/2.90  tff(c_14716, plain, (![A_924]: (~v1_xboole_0(A_924) | v1_xboole_0(k3_tarski(A_924)))), inference(resolution, [status(thm)], [c_4, c_14700])).
% 8.22/2.90  tff(c_14406, plain, (![A_892, B_893]: (r2_hidden('#skF_2'(A_892, B_893), A_892) | r1_tarski(A_892, B_893))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.22/2.90  tff(c_14466, plain, (![A_900, B_901]: (~v1_xboole_0(A_900) | r1_tarski(A_900, B_901))), inference(resolution, [status(thm)], [c_14406, c_2])).
% 8.22/2.90  tff(c_14348, plain, (k1_xboole_0='#skF_14'), inference(demodulation, [status(thm), theory('equality')], [c_14342, c_12221])).
% 8.22/2.90  tff(c_14385, plain, (![A_10, B_11]: (k4_xboole_0(A_10, B_11)='#skF_14' | ~r1_tarski(A_10, B_11))), inference(demodulation, [status(thm), theory('equality')], [c_14348, c_16])).
% 8.22/2.90  tff(c_14473, plain, (![A_900, B_901]: (k4_xboole_0(A_900, B_901)='#skF_14' | ~v1_xboole_0(A_900))), inference(resolution, [status(thm)], [c_14466, c_14385])).
% 8.22/2.90  tff(c_14875, plain, (![A_938, B_939]: (k4_xboole_0(k3_tarski(A_938), B_939)='#skF_14' | ~v1_xboole_0(A_938))), inference(resolution, [status(thm)], [c_14716, c_14473])).
% 8.22/2.90  tff(c_14344, plain, (![A_14]: (k4_xboole_0(A_14, '#skF_14')=A_14)), inference(demodulation, [status(thm), theory('equality')], [c_14342, c_12223])).
% 8.22/2.90  tff(c_14912, plain, (![A_940]: (k3_tarski(A_940)='#skF_14' | ~v1_xboole_0(A_940))), inference(superposition, [status(thm), theory('equality')], [c_14875, c_14344])).
% 8.22/2.90  tff(c_14924, plain, (k3_tarski('#skF_14')='#skF_14'), inference(resolution, [status(thm)], [c_14346, c_14912])).
% 8.22/2.90  tff(c_14713, plain, (![A_922, C_66]: (~v1_xboole_0(A_922) | ~r2_hidden(C_66, k3_tarski(k3_tarski(A_922))))), inference(resolution, [status(thm)], [c_50, c_14700])).
% 8.22/2.90  tff(c_14940, plain, (![C_66]: (~v1_xboole_0('#skF_14') | ~r2_hidden(C_66, k3_tarski('#skF_14')))), inference(superposition, [status(thm), theory('equality')], [c_14924, c_14713])).
% 8.22/2.90  tff(c_14967, plain, (![C_66]: (~r2_hidden(C_66, '#skF_14'))), inference(demodulation, [status(thm), theory('equality')], [c_14924, c_14346, c_14940])).
% 8.22/2.90  tff(c_15269, plain, (![D_959, A_960]: (~r2_hidden(D_959, k2_zfmisc_1(A_960, '#skF_14')))), inference(resolution, [status(thm)], [c_15238, c_14967])).
% 8.22/2.90  tff(c_15315, plain, (![A_961]: (v1_xboole_0(k2_zfmisc_1(A_961, '#skF_14')))), inference(resolution, [status(thm)], [c_4, c_15269])).
% 8.22/2.90  tff(c_15622, plain, (![A_978, B_979]: (k4_xboole_0(k2_zfmisc_1(A_978, '#skF_14'), B_979)='#skF_14')), inference(resolution, [status(thm)], [c_15315, c_14473])).
% 8.22/2.90  tff(c_15637, plain, (![A_978]: (k2_zfmisc_1(A_978, '#skF_14')='#skF_14')), inference(superposition, [status(thm), theory('equality')], [c_15622, c_14344])).
% 8.22/2.90  tff(c_14345, plain, (k2_zfmisc_1('#skF_13', '#skF_14')!='#skF_14'), inference(demodulation, [status(thm), theory('equality')], [c_14342, c_12229])).
% 8.22/2.90  tff(c_15675, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_15637, c_14345])).
% 8.22/2.90  tff(c_15677, plain, (k1_xboole_0='#skF_15'), inference(splitRight, [status(thm)], [c_70])).
% 8.22/2.90  tff(c_72, plain, (k1_xboole_0='#skF_14' | k1_xboole_0='#skF_13' | k1_xboole_0!='#skF_15'), inference(cnfTransformation, [status(thm)], [f_80])).
% 8.22/2.90  tff(c_15703, plain, ('#skF_15'='#skF_14' | '#skF_15'='#skF_13'), inference(demodulation, [status(thm), theory('equality')], [c_15677, c_15677, c_15677, c_72])).
% 8.22/2.90  tff(c_15704, plain, ('#skF_15'='#skF_13'), inference(splitLeft, [status(thm)], [c_15703])).
% 8.22/2.90  tff(c_15679, plain, (v1_xboole_0('#skF_15')), inference(demodulation, [status(thm), theory('equality')], [c_15677, c_12])).
% 8.22/2.90  tff(c_15708, plain, (v1_xboole_0('#skF_13')), inference(demodulation, [status(thm), theory('equality')], [c_15704, c_15679])).
% 8.22/2.90  tff(c_15678, plain, (![A_14]: (k4_xboole_0(A_14, '#skF_15')=A_14)), inference(demodulation, [status(thm), theory('equality')], [c_15677, c_20])).
% 8.22/2.90  tff(c_15706, plain, (![A_14]: (k4_xboole_0(A_14, '#skF_13')=A_14)), inference(demodulation, [status(thm), theory('equality')], [c_15704, c_15678])).
% 8.22/2.90  tff(c_15709, plain, (k1_xboole_0='#skF_13'), inference(demodulation, [status(thm), theory('equality')], [c_15704, c_15677])).
% 8.22/2.90  tff(c_15747, plain, (![A_989, B_990]: (r1_tarski(A_989, B_990) | k4_xboole_0(A_989, B_990)!='#skF_13')), inference(demodulation, [status(thm), theory('equality')], [c_15709, c_14])).
% 8.22/2.90  tff(c_15966, plain, (![A_1017, B_1018]: (k2_xboole_0(A_1017, B_1018)=B_1018 | k4_xboole_0(A_1017, B_1018)!='#skF_13')), inference(resolution, [status(thm)], [c_15747, c_18])).
% 8.22/2.90  tff(c_15986, plain, (![A_1019]: (k2_xboole_0(A_1019, '#skF_13')='#skF_13' | A_1019!='#skF_13')), inference(superposition, [status(thm), theory('equality')], [c_15706, c_15966])).
% 8.22/2.90  tff(c_16006, plain, (![A_1019]: (r1_tarski(A_1019, '#skF_13') | A_1019!='#skF_13')), inference(superposition, [status(thm), theory('equality')], [c_15986, c_22])).
% 8.22/2.90  tff(c_15810, plain, (![C_998, B_999, A_1000]: (r2_hidden(C_998, B_999) | ~r2_hidden(C_998, A_1000) | ~r1_tarski(A_1000, B_999))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.22/2.90  tff(c_16041, plain, (![A_1021, B_1022]: (r2_hidden('#skF_1'(A_1021), B_1022) | ~r1_tarski(A_1021, B_1022) | v1_xboole_0(A_1021))), inference(resolution, [status(thm)], [c_4, c_15810])).
% 8.22/2.90  tff(c_16111, plain, (![B_1034, A_1035]: (~v1_xboole_0(B_1034) | ~r1_tarski(A_1035, B_1034) | v1_xboole_0(A_1035))), inference(resolution, [status(thm)], [c_16041, c_2])).
% 8.22/2.90  tff(c_16117, plain, (![A_1019]: (~v1_xboole_0('#skF_13') | v1_xboole_0(A_1019) | A_1019!='#skF_13')), inference(resolution, [status(thm)], [c_16006, c_16111])).
% 8.22/2.90  tff(c_16136, plain, (![A_1019]: (v1_xboole_0(A_1019) | A_1019!='#skF_13')), inference(demodulation, [status(thm), theory('equality')], [c_15708, c_16117])).
% 8.22/2.90  tff(c_16052, plain, (![A_1023, C_1024]: (r2_hidden('#skF_12'(A_1023, k3_tarski(A_1023), C_1024), A_1023) | ~r2_hidden(C_1024, k3_tarski(A_1023)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 8.22/2.90  tff(c_16063, plain, (![A_1025, C_1026]: (~v1_xboole_0(A_1025) | ~r2_hidden(C_1026, k3_tarski(A_1025)))), inference(resolution, [status(thm)], [c_16052, c_2])).
% 8.22/2.90  tff(c_16083, plain, (![A_1025]: (~v1_xboole_0(A_1025) | v1_xboole_0(k3_tarski(A_1025)))), inference(resolution, [status(thm)], [c_4, c_16063])).
% 8.22/2.90  tff(c_16084, plain, (![A_1027]: (~v1_xboole_0(A_1027) | v1_xboole_0(k3_tarski(A_1027)))), inference(resolution, [status(thm)], [c_4, c_16063])).
% 8.22/2.90  tff(c_15758, plain, (![A_993, B_994]: (r2_hidden('#skF_2'(A_993, B_994), A_993) | r1_tarski(A_993, B_994))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.22/2.90  tff(c_15818, plain, (![A_1001, B_1002]: (~v1_xboole_0(A_1001) | r1_tarski(A_1001, B_1002))), inference(resolution, [status(thm)], [c_15758, c_2])).
% 8.22/2.90  tff(c_15727, plain, (![A_10, B_11]: (k4_xboole_0(A_10, B_11)='#skF_13' | ~r1_tarski(A_10, B_11))), inference(demodulation, [status(thm), theory('equality')], [c_15709, c_16])).
% 8.22/2.90  tff(c_15826, plain, (![A_1001, B_1002]: (k4_xboole_0(A_1001, B_1002)='#skF_13' | ~v1_xboole_0(A_1001))), inference(resolution, [status(thm)], [c_15818, c_15727])).
% 8.22/2.90  tff(c_16613, plain, (![A_1080, B_1081]: (k4_xboole_0(k3_tarski(A_1080), B_1081)='#skF_13' | ~v1_xboole_0(A_1080))), inference(resolution, [status(thm)], [c_16084, c_15826])).
% 8.22/2.90  tff(c_16659, plain, (![A_1082]: (k3_tarski(A_1082)='#skF_13' | ~v1_xboole_0(A_1082))), inference(superposition, [status(thm), theory('equality')], [c_16613, c_15706])).
% 8.22/2.90  tff(c_16749, plain, (![A_1086]: (k3_tarski(k3_tarski(A_1086))='#skF_13' | ~v1_xboole_0(A_1086))), inference(resolution, [status(thm)], [c_16083, c_16659])).
% 8.22/2.90  tff(c_16080, plain, (![A_1025, C_66]: (~v1_xboole_0(A_1025) | ~r2_hidden(C_66, k3_tarski(k3_tarski(A_1025))))), inference(resolution, [status(thm)], [c_50, c_16063])).
% 8.22/2.90  tff(c_16782, plain, (![A_1086, C_66]: (~v1_xboole_0(A_1086) | ~r2_hidden(C_66, '#skF_13') | ~v1_xboole_0(A_1086))), inference(superposition, [status(thm), theory('equality')], [c_16749, c_16080])).
% 8.22/2.90  tff(c_17160, plain, (![A_1098]: (~v1_xboole_0(A_1098) | ~v1_xboole_0(A_1098))), inference(splitLeft, [status(thm)], [c_16782])).
% 8.22/2.90  tff(c_17177, plain, (![A_1099]: (~v1_xboole_0(A_1099) | A_1099!='#skF_13')), inference(resolution, [status(thm)], [c_16136, c_17160])).
% 8.22/2.90  tff(c_17196, plain, (![A_1019]: (A_1019!='#skF_13')), inference(resolution, [status(thm)], [c_16136, c_17177])).
% 8.22/2.90  tff(c_8, plain, (![A_5, B_6]: (~r2_hidden('#skF_2'(A_5, B_6), B_6) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.22/2.90  tff(c_15768, plain, (![A_995]: (r1_tarski(A_995, A_995))), inference(resolution, [status(thm)], [c_15758, c_8])).
% 8.22/2.90  tff(c_15776, plain, (![A_995]: (k4_xboole_0(A_995, A_995)='#skF_13')), inference(resolution, [status(thm)], [c_15768, c_15727])).
% 8.22/2.90  tff(c_17223, plain, $false, inference(negUnitSimplification, [status(thm)], [c_17196, c_15776])).
% 8.22/2.90  tff(c_17225, plain, (![C_1103]: (~r2_hidden(C_1103, '#skF_13'))), inference(splitRight, [status(thm)], [c_16782])).
% 8.22/2.90  tff(c_17283, plain, (![D_1104, B_1105]: (~r2_hidden(D_1104, k2_zfmisc_1('#skF_13', B_1105)))), inference(resolution, [status(thm)], [c_30, c_17225])).
% 8.22/2.90  tff(c_17481, plain, (![B_1114, B_1115]: (r1_tarski(k2_zfmisc_1('#skF_13', B_1114), B_1115))), inference(resolution, [status(thm)], [c_10, c_17283])).
% 8.22/2.90  tff(c_17876, plain, (![B_1128, B_1129]: (k4_xboole_0(k2_zfmisc_1('#skF_13', B_1128), B_1129)='#skF_13')), inference(resolution, [status(thm)], [c_17481, c_15727])).
% 8.22/2.90  tff(c_17894, plain, (![B_1128]: (k2_zfmisc_1('#skF_13', B_1128)='#skF_13')), inference(superposition, [status(thm), theory('equality')], [c_17876, c_15706])).
% 8.22/2.90  tff(c_15676, plain, (k2_zfmisc_1('#skF_13', '#skF_14')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_70])).
% 8.22/2.90  tff(c_15684, plain, (k2_zfmisc_1('#skF_13', '#skF_14')!='#skF_15'), inference(demodulation, [status(thm), theory('equality')], [c_15677, c_15676])).
% 8.22/2.90  tff(c_15707, plain, (k2_zfmisc_1('#skF_13', '#skF_14')!='#skF_13'), inference(demodulation, [status(thm), theory('equality')], [c_15704, c_15684])).
% 8.22/2.90  tff(c_17931, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_17894, c_15707])).
% 8.22/2.90  tff(c_17932, plain, ('#skF_15'='#skF_14'), inference(splitRight, [status(thm)], [c_15703])).
% 8.22/2.90  tff(c_17938, plain, (v1_xboole_0('#skF_14')), inference(demodulation, [status(thm), theory('equality')], [c_17932, c_15679])).
% 8.22/2.90  tff(c_18216, plain, (![A_1167, C_1168]: (r2_hidden('#skF_12'(A_1167, k3_tarski(A_1167), C_1168), A_1167) | ~r2_hidden(C_1168, k3_tarski(A_1167)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 8.22/2.90  tff(c_18227, plain, (![A_1169, C_1170]: (~v1_xboole_0(A_1169) | ~r2_hidden(C_1170, k3_tarski(A_1169)))), inference(resolution, [status(thm)], [c_18216, c_2])).
% 8.22/2.90  tff(c_18306, plain, (![A_1174, B_1175]: (~v1_xboole_0(A_1174) | r1_tarski(k3_tarski(A_1174), B_1175))), inference(resolution, [status(thm)], [c_10, c_18227])).
% 8.22/2.90  tff(c_17939, plain, (k1_xboole_0='#skF_14'), inference(demodulation, [status(thm), theory('equality')], [c_17932, c_15677])).
% 8.22/2.90  tff(c_17971, plain, (![A_10, B_11]: (k4_xboole_0(A_10, B_11)='#skF_14' | ~r1_tarski(A_10, B_11))), inference(demodulation, [status(thm), theory('equality')], [c_17939, c_16])).
% 8.22/2.90  tff(c_18359, plain, (![A_1181, B_1182]: (k4_xboole_0(k3_tarski(A_1181), B_1182)='#skF_14' | ~v1_xboole_0(A_1181))), inference(resolution, [status(thm)], [c_18306, c_17971])).
% 8.22/2.90  tff(c_17936, plain, (![A_14]: (k4_xboole_0(A_14, '#skF_14')=A_14)), inference(demodulation, [status(thm), theory('equality')], [c_17932, c_15678])).
% 8.22/2.90  tff(c_18437, plain, (![A_1185]: (k3_tarski(A_1185)='#skF_14' | ~v1_xboole_0(A_1185))), inference(superposition, [status(thm), theory('equality')], [c_18359, c_17936])).
% 8.22/2.90  tff(c_18449, plain, (k3_tarski('#skF_14')='#skF_14'), inference(resolution, [status(thm)], [c_17938, c_18437])).
% 8.22/2.90  tff(c_18240, plain, (![A_1169, C_66]: (~v1_xboole_0(A_1169) | ~r2_hidden(C_66, k3_tarski(k3_tarski(A_1169))))), inference(resolution, [status(thm)], [c_50, c_18227])).
% 8.22/2.90  tff(c_18459, plain, (![C_66]: (~v1_xboole_0('#skF_14') | ~r2_hidden(C_66, k3_tarski('#skF_14')))), inference(superposition, [status(thm), theory('equality')], [c_18449, c_18240])).
% 8.22/2.90  tff(c_18482, plain, (![C_66]: (~r2_hidden(C_66, '#skF_14'))), inference(demodulation, [status(thm), theory('equality')], [c_18449, c_17938, c_18459])).
% 8.22/2.90  tff(c_18676, plain, (![D_1197, A_1198]: (~r2_hidden(D_1197, k2_zfmisc_1(A_1198, '#skF_14')))), inference(resolution, [status(thm)], [c_18650, c_18482])).
% 8.22/2.90  tff(c_18728, plain, (![A_1200, B_1201]: (r1_tarski(k2_zfmisc_1(A_1200, '#skF_14'), B_1201))), inference(resolution, [status(thm)], [c_10, c_18676])).
% 8.22/2.90  tff(c_18967, plain, (![A_1214, B_1215]: (k4_xboole_0(k2_zfmisc_1(A_1214, '#skF_14'), B_1215)='#skF_14')), inference(resolution, [status(thm)], [c_18728, c_17971])).
% 8.22/2.90  tff(c_18982, plain, (![A_1214]: (k2_zfmisc_1(A_1214, '#skF_14')='#skF_14')), inference(superposition, [status(thm), theory('equality')], [c_18967, c_17936])).
% 8.22/2.90  tff(c_17937, plain, (k2_zfmisc_1('#skF_13', '#skF_14')!='#skF_14'), inference(demodulation, [status(thm), theory('equality')], [c_17932, c_15684])).
% 8.22/2.90  tff(c_19013, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18982, c_17937])).
% 8.22/2.90  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.22/2.90  
% 8.22/2.90  Inference rules
% 8.22/2.90  ----------------------
% 8.22/2.90  #Ref     : 0
% 8.22/2.90  #Sup     : 4160
% 8.22/2.90  #Fact    : 0
% 8.22/2.90  #Define  : 0
% 8.22/2.90  #Split   : 16
% 8.22/2.90  #Chain   : 0
% 8.22/2.90  #Close   : 0
% 8.22/2.90  
% 8.22/2.90  Ordering : KBO
% 8.22/2.90  
% 8.22/2.90  Simplification rules
% 8.22/2.90  ----------------------
% 8.22/2.90  #Subsume      : 664
% 8.22/2.90  #Demod        : 1750
% 8.22/2.90  #Tautology    : 1855
% 8.22/2.90  #SimpNegUnit  : 97
% 8.22/2.90  #BackRed      : 217
% 8.22/2.90  
% 8.22/2.90  #Partial instantiations: 0
% 8.22/2.90  #Strategies tried      : 1
% 8.22/2.90  
% 8.22/2.90  Timing (in seconds)
% 8.22/2.90  ----------------------
% 8.22/2.90  Preprocessing        : 0.34
% 8.22/2.90  Parsing              : 0.17
% 8.22/2.90  CNF conversion       : 0.03
% 8.22/2.90  Main loop            : 1.66
% 8.22/2.90  Inferencing          : 0.59
% 8.22/2.90  Reduction            : 0.50
% 8.22/2.90  Demodulation         : 0.33
% 8.22/2.90  BG Simplification    : 0.07
% 8.22/2.90  Subsumption          : 0.32
% 8.22/2.90  Abstraction          : 0.09
% 8.22/2.90  MUC search           : 0.00
% 8.22/2.90  Cooper               : 0.00
% 8.22/2.90  Total                : 2.11
% 8.22/2.90  Index Insertion      : 0.00
% 8.22/2.90  Index Deletion       : 0.00
% 8.22/2.90  Index Matching       : 0.00
% 8.22/2.90  BG Taut test         : 0.00
%------------------------------------------------------------------------------
