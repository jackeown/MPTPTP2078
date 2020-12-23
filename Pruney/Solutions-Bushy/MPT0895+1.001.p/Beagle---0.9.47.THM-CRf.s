%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0895+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:02 EST 2020

% Result     : Theorem 3.68s
% Output     : CNFRefutation 3.91s
% Verified   : 
% Statistics : Number of formulae       :  275 (2546 expanded)
%              Number of leaves         :   19 ( 738 expanded)
%              Depth                    :   10
%              Number of atoms          :  345 (6775 expanded)
%              Number of equality atoms :  317 (6747 expanded)
%              Maximal formula depth    :   11 (   3 average)
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

tff(f_26,axiom,(
    ! [A,B,C,D] : k4_zfmisc_1(A,B,C,D) = k2_zfmisc_1(k3_zfmisc_1(A,B,C),D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).

tff(f_60,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( A != k1_xboole_0
          & B != k1_xboole_0
          & C != k1_xboole_0
          & D != k1_xboole_0 )
      <=> k4_zfmisc_1(A,B,C,D) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_mcart_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0 )
    <=> k3_zfmisc_1(A,B,C) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_mcart_1)).

tff(c_3815,plain,(
    ! [A_448,B_449,C_450,D_451] : k2_zfmisc_1(k3_zfmisc_1(A_448,B_449,C_450),D_451) = k4_zfmisc_1(A_448,B_449,C_450,D_451) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_3013,plain,(
    ! [A_355,B_356,C_357,D_358] : k2_zfmisc_1(k3_zfmisc_1(A_355,B_356,C_357),D_358) = k4_zfmisc_1(A_355,B_356,C_357,D_358) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_36,plain,
    ( k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k1_xboole_0
    | k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_104,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_32,plain,
    ( k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k1_xboole_0
    | k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_105,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_28,plain,
    ( k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k1_xboole_0
    | k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_106,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_24,plain,
    ( k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k1_xboole_0
    | k1_xboole_0 != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_107,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_18,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1'
    | k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_266,plain,(
    k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_18])).

tff(c_119,plain,(
    ! [A_20,B_21,C_22,D_23] : k2_zfmisc_1(k3_zfmisc_1(A_20,B_21,C_22),D_23) = k4_zfmisc_1(A_20,B_21,C_22,D_23) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_4,plain,(
    ! [B_6,A_5] :
      ( k1_xboole_0 = B_6
      | k1_xboole_0 = A_5
      | k2_zfmisc_1(A_5,B_6) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_125,plain,(
    ! [D_23,A_20,B_21,C_22] :
      ( k1_xboole_0 = D_23
      | k3_zfmisc_1(A_20,B_21,C_22) = k1_xboole_0
      | k4_zfmisc_1(A_20,B_21,C_22,D_23) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_4])).

tff(c_270,plain,
    ( k1_xboole_0 = '#skF_8'
    | k3_zfmisc_1('#skF_5','#skF_6','#skF_7') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_266,c_125])).

tff(c_275,plain,(
    k3_zfmisc_1('#skF_5','#skF_6','#skF_7') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_107,c_270])).

tff(c_10,plain,(
    ! [A_7,B_8,C_9] :
      ( k3_zfmisc_1(A_7,B_8,C_9) != k1_xboole_0
      | k1_xboole_0 = C_9
      | k1_xboole_0 = B_8
      | k1_xboole_0 = A_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_280,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_275,c_10])).

tff(c_289,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_105,c_106,c_280])).

tff(c_290,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_292,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_290])).

tff(c_6,plain,(
    ! [A_5] : k2_zfmisc_1(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_322,plain,(
    ! [A_44] : k2_zfmisc_1(A_44,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_292,c_292,c_6])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3,D_4] : k2_zfmisc_1(k3_zfmisc_1(A_1,B_2,C_3),D_4) = k4_zfmisc_1(A_1,B_2,C_3,D_4) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_331,plain,(
    ! [A_1,B_2,C_3] : k4_zfmisc_1(A_1,B_2,C_3,'#skF_4') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_322,c_2])).

tff(c_20,plain,
    ( k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k1_xboole_0
    | k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_151,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_20])).

tff(c_300,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_292,c_151])).

tff(c_440,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_331,c_300])).

tff(c_441,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_290])).

tff(c_443,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_441])).

tff(c_8,plain,(
    ! [B_6] : k2_zfmisc_1(k1_xboole_0,B_6) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_462,plain,(
    ! [B_6] : k2_zfmisc_1('#skF_1',B_6) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_443,c_443,c_8])).

tff(c_16,plain,(
    ! [B_8,C_9] : k3_zfmisc_1(k1_xboole_0,B_8,C_9) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_527,plain,(
    ! [B_65,C_66] : k3_zfmisc_1('#skF_1',B_65,C_66) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_443,c_443,c_16])).

tff(c_538,plain,(
    ! [B_65,C_66,D_4] : k4_zfmisc_1('#skF_1',B_65,C_66,D_4) = k2_zfmisc_1('#skF_1',D_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_527,c_2])).

tff(c_550,plain,(
    ! [B_65,C_66,D_4] : k4_zfmisc_1('#skF_1',B_65,C_66,D_4) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_462,c_538])).

tff(c_452,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_443,c_151])).

tff(c_556,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_550,c_452])).

tff(c_557,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_441])).

tff(c_559,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_557])).

tff(c_12,plain,(
    ! [A_7,B_8] : k3_zfmisc_1(A_7,B_8,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_138,plain,(
    ! [A_7,B_8,D_23] : k4_zfmisc_1(A_7,B_8,k1_xboole_0,D_23) = k2_zfmisc_1(k1_xboole_0,D_23) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_119])).

tff(c_149,plain,(
    ! [A_7,B_8,D_23] : k4_zfmisc_1(A_7,B_8,k1_xboole_0,D_23) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_138])).

tff(c_564,plain,(
    ! [A_7,B_8,D_23] : k4_zfmisc_1(A_7,B_8,'#skF_3',D_23) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_559,c_559,c_149])).

tff(c_569,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_559,c_151])).

tff(c_696,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_564,c_569])).

tff(c_697,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_557])).

tff(c_14,plain,(
    ! [A_7,C_9] : k3_zfmisc_1(A_7,k1_xboole_0,C_9) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_135,plain,(
    ! [A_7,C_9,D_23] : k4_zfmisc_1(A_7,k1_xboole_0,C_9,D_23) = k2_zfmisc_1(k1_xboole_0,D_23) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_119])).

tff(c_148,plain,(
    ! [A_7,C_9,D_23] : k4_zfmisc_1(A_7,k1_xboole_0,C_9,D_23) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_135])).

tff(c_706,plain,(
    ! [A_7,C_9,D_23] : k4_zfmisc_1(A_7,'#skF_2',C_9,D_23) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_697,c_697,c_148])).

tff(c_709,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_697,c_151])).

tff(c_820,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_706,c_709])).

tff(c_821,plain,(
    k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_925,plain,(
    ! [D_107,A_108,B_109,C_110] :
      ( k1_xboole_0 = D_107
      | k3_zfmisc_1(A_108,B_109,C_110) = k1_xboole_0
      | k4_zfmisc_1(A_108,B_109,C_110,D_107) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_4])).

tff(c_943,plain,
    ( k1_xboole_0 = '#skF_8'
    | k3_zfmisc_1('#skF_5','#skF_6','#skF_7') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_821,c_925])).

tff(c_955,plain,(
    k3_zfmisc_1('#skF_5','#skF_6','#skF_7') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_107,c_943])).

tff(c_959,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_955,c_10])).

tff(c_968,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_105,c_106,c_959])).

tff(c_970,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_978,plain,(
    ! [B_6] : k2_zfmisc_1('#skF_8',B_6) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_970,c_970,c_8])).

tff(c_975,plain,(
    ! [A_7,B_8] : k3_zfmisc_1(A_7,B_8,'#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_970,c_970,c_12])).

tff(c_1407,plain,(
    ! [A_164,B_165,C_166,D_167] : k2_zfmisc_1(k3_zfmisc_1(A_164,B_165,C_166),D_167) = k4_zfmisc_1(A_164,B_165,C_166,D_167) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_1429,plain,(
    ! [A_7,B_8,D_167] : k4_zfmisc_1(A_7,B_8,'#skF_8',D_167) = k2_zfmisc_1('#skF_8',D_167) ),
    inference(superposition,[status(thm),theory(equality)],[c_975,c_1407])).

tff(c_1438,plain,(
    ! [A_7,B_8,D_167] : k4_zfmisc_1(A_7,B_8,'#skF_8',D_167) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_978,c_1429])).

tff(c_974,plain,(
    ! [A_7,C_9] : k3_zfmisc_1(A_7,'#skF_8',C_9) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_970,c_970,c_14])).

tff(c_1356,plain,(
    ! [A_157,B_158,C_159,D_160] : k2_zfmisc_1(k3_zfmisc_1(A_157,B_158,C_159),D_160) = k4_zfmisc_1(A_157,B_158,C_159,D_160) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_1372,plain,(
    ! [A_7,C_9,D_160] : k4_zfmisc_1(A_7,'#skF_8',C_9,D_160) = k2_zfmisc_1('#skF_8',D_160) ),
    inference(superposition,[status(thm),theory(equality)],[c_974,c_1356])).

tff(c_1385,plain,(
    ! [A_7,C_9,D_160] : k4_zfmisc_1(A_7,'#skF_8',C_9,D_160) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_978,c_1372])).

tff(c_1294,plain,(
    ! [A_150,B_151,C_152,D_153] : k2_zfmisc_1(k3_zfmisc_1(A_150,B_151,C_152),D_153) = k4_zfmisc_1(A_150,B_151,C_152,D_153) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_976,plain,(
    ! [B_8,C_9] : k3_zfmisc_1('#skF_8',B_8,C_9) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_970,c_970,c_16])).

tff(c_1091,plain,(
    ! [A_124,B_125,C_126,D_127] : k2_zfmisc_1(k3_zfmisc_1(A_124,B_125,C_126),D_127) = k4_zfmisc_1(A_124,B_125,C_126,D_127) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_1110,plain,(
    ! [B_8,C_9,D_127] : k4_zfmisc_1('#skF_8',B_8,C_9,D_127) = k2_zfmisc_1('#skF_8',D_127) ),
    inference(superposition,[status(thm),theory(equality)],[c_976,c_1091])).

tff(c_1121,plain,(
    ! [B_8,C_9,D_127] : k4_zfmisc_1('#skF_8',B_8,C_9,D_127) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_978,c_1110])).

tff(c_22,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1065,plain,
    ( '#skF_8' = '#skF_4'
    | '#skF_3' = '#skF_8'
    | '#skF_2' = '#skF_8'
    | '#skF_1' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_970,c_970,c_970,c_970,c_970,c_22])).

tff(c_1066,plain,(
    '#skF_1' = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_1065])).

tff(c_969,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_1051,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_970,c_969])).

tff(c_1067,plain,(
    k4_zfmisc_1('#skF_8','#skF_2','#skF_3','#skF_4') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1066,c_1051])).

tff(c_1172,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1121,c_1067])).

tff(c_1173,plain,
    ( '#skF_2' = '#skF_8'
    | '#skF_3' = '#skF_8'
    | '#skF_8' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1065])).

tff(c_1176,plain,(
    '#skF_8' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_1173])).

tff(c_977,plain,(
    ! [A_5] : k2_zfmisc_1(A_5,'#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_970,c_970,c_6])).

tff(c_1183,plain,(
    ! [A_5] : k2_zfmisc_1(A_5,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1176,c_1176,c_977])).

tff(c_1304,plain,(
    ! [A_150,B_151,C_152] : k4_zfmisc_1(A_150,B_151,C_152,'#skF_4') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_1294,c_1183])).

tff(c_1179,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1176,c_1051])).

tff(c_1328,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1304,c_1179])).

tff(c_1329,plain,
    ( '#skF_3' = '#skF_8'
    | '#skF_2' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_1173])).

tff(c_1333,plain,(
    '#skF_2' = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_1329])).

tff(c_1334,plain,(
    k4_zfmisc_1('#skF_1','#skF_8','#skF_3','#skF_4') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1333,c_1051])).

tff(c_1397,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1385,c_1334])).

tff(c_1398,plain,(
    '#skF_3' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_1329])).

tff(c_1405,plain,
    ( k4_zfmisc_1('#skF_1','#skF_2','#skF_8','#skF_4') != '#skF_8'
    | k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_970,c_1398,c_970,c_20])).

tff(c_1406,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_8','#skF_4') != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_1405])).

tff(c_1506,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1438,c_1406])).

tff(c_1508,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_8','#skF_4') = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_1405])).

tff(c_1400,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_8','#skF_4') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1398,c_1051])).

tff(c_1514,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1508,c_1400])).

tff(c_1516,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_26,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1614,plain,
    ( '#skF_7' = '#skF_4'
    | '#skF_7' = '#skF_3'
    | '#skF_7' = '#skF_2'
    | '#skF_7' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1516,c_1516,c_1516,c_1516,c_1516,c_26])).

tff(c_1615,plain,(
    '#skF_7' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_1614])).

tff(c_1515,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_1597,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1516,c_1515])).

tff(c_1617,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1615,c_1597])).

tff(c_1523,plain,(
    ! [B_6] : k2_zfmisc_1('#skF_7',B_6) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1516,c_1516,c_8])).

tff(c_1623,plain,(
    ! [B_6] : k2_zfmisc_1('#skF_1',B_6) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1615,c_1615,c_1523])).

tff(c_1521,plain,(
    ! [B_8,C_9] : k3_zfmisc_1('#skF_7',B_8,C_9) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1516,c_1516,c_16])).

tff(c_1620,plain,(
    ! [B_8,C_9] : k3_zfmisc_1('#skF_1',B_8,C_9) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1615,c_1615,c_1521])).

tff(c_1715,plain,(
    ! [A_200,B_201,C_202,D_203] : k2_zfmisc_1(k3_zfmisc_1(A_200,B_201,C_202),D_203) = k4_zfmisc_1(A_200,B_201,C_202,D_203) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_1734,plain,(
    ! [B_8,C_9,D_203] : k4_zfmisc_1('#skF_1',B_8,C_9,D_203) = k2_zfmisc_1('#skF_1',D_203) ),
    inference(superposition,[status(thm),theory(equality)],[c_1620,c_1715])).

tff(c_1745,plain,(
    ! [B_8,C_9,D_203] : k4_zfmisc_1('#skF_1',B_8,C_9,D_203) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1623,c_1734])).

tff(c_1626,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1615,c_1516])).

tff(c_1679,plain,
    ( k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_1'
    | k4_zfmisc_1('#skF_5','#skF_6','#skF_1','#skF_8') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1626,c_1615,c_1626,c_20])).

tff(c_1680,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_1679])).

tff(c_1788,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1745,c_1680])).

tff(c_1790,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1679])).

tff(c_1819,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1617,c_1790])).

tff(c_1820,plain,
    ( '#skF_7' = '#skF_2'
    | '#skF_7' = '#skF_3'
    | '#skF_7' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1614])).

tff(c_1822,plain,(
    '#skF_7' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_1820])).

tff(c_1825,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1822,c_1597])).

tff(c_1834,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1822,c_1516])).

tff(c_1943,plain,(
    ! [A_228,B_229,C_230,D_231] : k2_zfmisc_1(k3_zfmisc_1(A_228,B_229,C_230),D_231) = k4_zfmisc_1(A_228,B_229,C_230,D_231) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_1522,plain,(
    ! [A_5] : k2_zfmisc_1(A_5,'#skF_7') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1516,c_1516,c_6])).

tff(c_1830,plain,(
    ! [A_5] : k2_zfmisc_1(A_5,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1822,c_1822,c_1522])).

tff(c_1953,plain,(
    ! [A_228,B_229,C_230] : k4_zfmisc_1(A_228,B_229,C_230,'#skF_4') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_1943,c_1830])).

tff(c_1839,plain,
    ( k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k1_xboole_0
    | k4_zfmisc_1('#skF_5','#skF_6','#skF_4','#skF_8') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1822,c_20])).

tff(c_1840,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_1839])).

tff(c_1912,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1834,c_1840])).

tff(c_1977,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1953,c_1912])).

tff(c_1979,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1839])).

tff(c_2053,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1834,c_1979])).

tff(c_2054,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1825,c_2053])).

tff(c_2055,plain,
    ( '#skF_7' = '#skF_3'
    | '#skF_7' = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_1820])).

tff(c_2057,plain,(
    '#skF_7' = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_2055])).

tff(c_2061,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2057,c_1597])).

tff(c_2070,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2057,c_1516])).

tff(c_2067,plain,(
    ! [B_6] : k2_zfmisc_1('#skF_2',B_6) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2057,c_2057,c_1523])).

tff(c_1519,plain,(
    ! [A_7,C_9] : k3_zfmisc_1(A_7,'#skF_7',C_9) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1516,c_1516,c_14])).

tff(c_2062,plain,(
    ! [A_7,C_9] : k3_zfmisc_1(A_7,'#skF_2',C_9) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2057,c_2057,c_1519])).

tff(c_2179,plain,(
    ! [A_253,B_254,C_255,D_256] : k2_zfmisc_1(k3_zfmisc_1(A_253,B_254,C_255),D_256) = k4_zfmisc_1(A_253,B_254,C_255,D_256) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_2198,plain,(
    ! [A_7,C_9,D_256] : k4_zfmisc_1(A_7,'#skF_2',C_9,D_256) = k2_zfmisc_1('#skF_2',D_256) ),
    inference(superposition,[status(thm),theory(equality)],[c_2062,c_2179])).

tff(c_2209,plain,(
    ! [A_7,C_9,D_256] : k4_zfmisc_1(A_7,'#skF_2',C_9,D_256) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2067,c_2198])).

tff(c_2075,plain,
    ( k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k1_xboole_0
    | k4_zfmisc_1('#skF_5','#skF_6','#skF_2','#skF_8') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2057,c_20])).

tff(c_2076,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_2075])).

tff(c_2150,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2070,c_2076])).

tff(c_2247,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2209,c_2150])).

tff(c_2249,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_2075])).

tff(c_2328,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2070,c_2249])).

tff(c_2329,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2061,c_2328])).

tff(c_2330,plain,(
    '#skF_7' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_2055])).

tff(c_2335,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2330,c_1597])).

tff(c_2344,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2330,c_1516])).

tff(c_2341,plain,(
    ! [B_6] : k2_zfmisc_1('#skF_3',B_6) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2330,c_2330,c_1523])).

tff(c_1520,plain,(
    ! [A_7,B_8] : k3_zfmisc_1(A_7,B_8,'#skF_7') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1516,c_1516,c_12])).

tff(c_2337,plain,(
    ! [A_7,B_8] : k3_zfmisc_1(A_7,B_8,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2330,c_2330,c_1520])).

tff(c_2437,plain,(
    ! [A_285,B_286,C_287,D_288] : k2_zfmisc_1(k3_zfmisc_1(A_285,B_286,C_287),D_288) = k4_zfmisc_1(A_285,B_286,C_287,D_288) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_2459,plain,(
    ! [A_7,B_8,D_288] : k4_zfmisc_1(A_7,B_8,'#skF_3',D_288) = k2_zfmisc_1('#skF_3',D_288) ),
    inference(superposition,[status(thm),theory(equality)],[c_2337,c_2437])).

tff(c_2468,plain,(
    ! [A_7,B_8,D_288] : k4_zfmisc_1(A_7,B_8,'#skF_3',D_288) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2341,c_2459])).

tff(c_2350,plain,
    ( k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k1_xboole_0
    | k4_zfmisc_1('#skF_5','#skF_6','#skF_3','#skF_8') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2330,c_20])).

tff(c_2351,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_2350])).

tff(c_2425,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2344,c_2351])).

tff(c_2534,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2468,c_2425])).

tff(c_2536,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_2350])).

tff(c_2615,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2344,c_2536])).

tff(c_2616,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2335,c_2615])).

tff(c_2618,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_30,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_2716,plain,
    ( '#skF_6' = '#skF_4'
    | '#skF_6' = '#skF_3'
    | '#skF_6' = '#skF_2'
    | '#skF_6' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2618,c_2618,c_2618,c_2618,c_2618,c_30])).

tff(c_2717,plain,(
    '#skF_6' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_2716])).

tff(c_2624,plain,(
    ! [B_6] : k2_zfmisc_1('#skF_6',B_6) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2618,c_2618,c_8])).

tff(c_2724,plain,(
    ! [B_6] : k2_zfmisc_1('#skF_1',B_6) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2717,c_2717,c_2624])).

tff(c_2622,plain,(
    ! [B_8,C_9] : k3_zfmisc_1('#skF_6',B_8,C_9) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2618,c_2618,c_16])).

tff(c_2723,plain,(
    ! [B_8,C_9] : k3_zfmisc_1('#skF_1',B_8,C_9) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2717,c_2717,c_2622])).

tff(c_2833,plain,(
    ! [A_332,B_333,C_334,D_335] : k2_zfmisc_1(k3_zfmisc_1(A_332,B_333,C_334),D_335) = k4_zfmisc_1(A_332,B_333,C_334,D_335) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_2849,plain,(
    ! [B_8,C_9,D_335] : k4_zfmisc_1('#skF_1',B_8,C_9,D_335) = k2_zfmisc_1('#skF_1',D_335) ),
    inference(superposition,[status(thm),theory(equality)],[c_2723,c_2833])).

tff(c_2862,plain,(
    ! [B_8,C_9,D_335] : k4_zfmisc_1('#skF_1',B_8,C_9,D_335) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2724,c_2849])).

tff(c_2617,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_2698,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2618,c_2617])).

tff(c_2720,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2717,c_2698])).

tff(c_2891,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2862,c_2720])).

tff(c_2892,plain,
    ( '#skF_6' = '#skF_2'
    | '#skF_6' = '#skF_3'
    | '#skF_6' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_2716])).

tff(c_2894,plain,(
    '#skF_6' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_2892])).

tff(c_2623,plain,(
    ! [A_5] : k2_zfmisc_1(A_5,'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2618,c_2618,c_6])).

tff(c_2903,plain,(
    ! [A_5] : k2_zfmisc_1(A_5,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2894,c_2894,c_2623])).

tff(c_3023,plain,(
    ! [A_355,B_356,C_357] : k4_zfmisc_1(A_355,B_356,C_357,'#skF_4') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_3013,c_2903])).

tff(c_2898,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2894,c_2698])).

tff(c_3047,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3023,c_2898])).

tff(c_3048,plain,
    ( '#skF_6' = '#skF_3'
    | '#skF_6' = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_2892])).

tff(c_3050,plain,(
    '#skF_6' = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_3048])).

tff(c_3059,plain,(
    ! [B_6] : k2_zfmisc_1('#skF_2',B_6) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3050,c_3050,c_2624])).

tff(c_2620,plain,(
    ! [A_7,C_9] : k3_zfmisc_1(A_7,'#skF_6',C_9) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2618,c_2618,c_14])).

tff(c_3056,plain,(
    ! [A_7,C_9] : k3_zfmisc_1(A_7,'#skF_2',C_9) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3050,c_3050,c_2620])).

tff(c_3171,plain,(
    ! [A_372,B_373,C_374,D_375] : k2_zfmisc_1(k3_zfmisc_1(A_372,B_373,C_374),D_375) = k4_zfmisc_1(A_372,B_373,C_374,D_375) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_3187,plain,(
    ! [A_7,C_9,D_375] : k4_zfmisc_1(A_7,'#skF_2',C_9,D_375) = k2_zfmisc_1('#skF_2',D_375) ),
    inference(superposition,[status(thm),theory(equality)],[c_3056,c_3171])).

tff(c_3200,plain,(
    ! [A_7,C_9,D_375] : k4_zfmisc_1(A_7,'#skF_2',C_9,D_375) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3059,c_3187])).

tff(c_3063,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3050,c_2618])).

tff(c_3141,plain,
    ( k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_2'
    | k4_zfmisc_1('#skF_5','#skF_2','#skF_7','#skF_8') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3063,c_3050,c_3063,c_20])).

tff(c_3142,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_3141])).

tff(c_3215,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3200,c_3142])).

tff(c_3217,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_3141])).

tff(c_3055,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3050,c_2698])).

tff(c_3229,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3217,c_3055])).

tff(c_3230,plain,(
    '#skF_6' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_3048])).

tff(c_3240,plain,(
    ! [B_6] : k2_zfmisc_1('#skF_3',B_6) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3230,c_3230,c_2624])).

tff(c_2621,plain,(
    ! [A_7,B_8] : k3_zfmisc_1(A_7,B_8,'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2618,c_2618,c_12])).

tff(c_3238,plain,(
    ! [A_7,B_8] : k3_zfmisc_1(A_7,B_8,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3230,c_3230,c_2621])).

tff(c_3352,plain,(
    ! [A_392,B_393,C_394,D_395] : k2_zfmisc_1(k3_zfmisc_1(A_392,B_393,C_394),D_395) = k4_zfmisc_1(A_392,B_393,C_394,D_395) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_3368,plain,(
    ! [A_7,B_8,D_395] : k4_zfmisc_1(A_7,B_8,'#skF_3',D_395) = k2_zfmisc_1('#skF_3',D_395) ),
    inference(superposition,[status(thm),theory(equality)],[c_3238,c_3352])).

tff(c_3381,plain,(
    ! [A_7,B_8,D_395] : k4_zfmisc_1(A_7,B_8,'#skF_3',D_395) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3240,c_3368])).

tff(c_3236,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3230,c_2698])).

tff(c_3394,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3381,c_3236])).

tff(c_3396,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_34,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_3495,plain,
    ( '#skF_5' = '#skF_4'
    | '#skF_5' = '#skF_3'
    | '#skF_5' = '#skF_2'
    | '#skF_5' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3396,c_3396,c_3396,c_3396,c_3396,c_34])).

tff(c_3496,plain,(
    '#skF_5' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_3495])).

tff(c_3401,plain,(
    ! [B_6] : k2_zfmisc_1('#skF_5',B_6) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3396,c_3396,c_8])).

tff(c_3505,plain,(
    ! [B_6] : k2_zfmisc_1('#skF_1',B_6) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3496,c_3496,c_3401])).

tff(c_3399,plain,(
    ! [B_8,C_9] : k3_zfmisc_1('#skF_5',B_8,C_9) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3396,c_3396,c_16])).

tff(c_3502,plain,(
    ! [B_8,C_9] : k3_zfmisc_1('#skF_1',B_8,C_9) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3496,c_3496,c_3399])).

tff(c_3612,plain,(
    ! [A_422,B_423,C_424,D_425] : k2_zfmisc_1(k3_zfmisc_1(A_422,B_423,C_424),D_425) = k4_zfmisc_1(A_422,B_423,C_424,D_425) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_3631,plain,(
    ! [B_8,C_9,D_425] : k4_zfmisc_1('#skF_1',B_8,C_9,D_425) = k2_zfmisc_1('#skF_1',D_425) ),
    inference(superposition,[status(thm),theory(equality)],[c_3502,c_3612])).

tff(c_3642,plain,(
    ! [B_8,C_9,D_425] : k4_zfmisc_1('#skF_1',B_8,C_9,D_425) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3505,c_3631])).

tff(c_3395,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_3475,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3396,c_3395])).

tff(c_3500,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3496,c_3475])).

tff(c_3693,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3642,c_3500])).

tff(c_3694,plain,
    ( '#skF_5' = '#skF_2'
    | '#skF_5' = '#skF_3'
    | '#skF_5' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_3495])).

tff(c_3696,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_3694])).

tff(c_3400,plain,(
    ! [A_5] : k2_zfmisc_1(A_5,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3396,c_3396,c_6])).

tff(c_3707,plain,(
    ! [A_5] : k2_zfmisc_1(A_5,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3696,c_3696,c_3400])).

tff(c_3825,plain,(
    ! [A_448,B_449,C_450] : k4_zfmisc_1(A_448,B_449,C_450,'#skF_4') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_3815,c_3707])).

tff(c_3701,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3696,c_3475])).

tff(c_3849,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3825,c_3701])).

tff(c_3850,plain,
    ( '#skF_5' = '#skF_3'
    | '#skF_5' = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_3694])).

tff(c_3852,plain,(
    '#skF_5' = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_3850])).

tff(c_3863,plain,(
    ! [B_6] : k2_zfmisc_1('#skF_2',B_6) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3852,c_3852,c_3401])).

tff(c_3397,plain,(
    ! [A_7,C_9] : k3_zfmisc_1(A_7,'#skF_5',C_9) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3396,c_3396,c_14])).

tff(c_3862,plain,(
    ! [A_7,C_9] : k3_zfmisc_1(A_7,'#skF_2',C_9) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3852,c_3852,c_3397])).

tff(c_3972,plain,(
    ! [A_465,B_466,C_467,D_468] : k2_zfmisc_1(k3_zfmisc_1(A_465,B_466,C_467),D_468) = k4_zfmisc_1(A_465,B_466,C_467,D_468) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_3994,plain,(
    ! [A_7,C_9,D_468] : k4_zfmisc_1(A_7,'#skF_2',C_9,D_468) = k2_zfmisc_1('#skF_2',D_468) ),
    inference(superposition,[status(thm),theory(equality)],[c_3862,c_3972])).

tff(c_4003,plain,(
    ! [A_7,C_9,D_468] : k4_zfmisc_1(A_7,'#skF_2',C_9,D_468) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3863,c_3994])).

tff(c_3858,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3852,c_3475])).

tff(c_4054,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4003,c_3858])).

tff(c_4055,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_3850])).

tff(c_4069,plain,(
    ! [B_6] : k2_zfmisc_1('#skF_3',B_6) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4055,c_4055,c_3401])).

tff(c_3398,plain,(
    ! [A_7,B_8] : k3_zfmisc_1(A_7,B_8,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3396,c_3396,c_12])).

tff(c_4065,plain,(
    ! [A_7,B_8] : k3_zfmisc_1(A_7,B_8,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4055,c_4055,c_3398])).

tff(c_4161,plain,(
    ! [A_488,B_489,C_490,D_491] : k2_zfmisc_1(k3_zfmisc_1(A_488,B_489,C_490),D_491) = k4_zfmisc_1(A_488,B_489,C_490,D_491) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_4177,plain,(
    ! [A_7,B_8,D_491] : k4_zfmisc_1(A_7,B_8,'#skF_3',D_491) = k2_zfmisc_1('#skF_3',D_491) ),
    inference(superposition,[status(thm),theory(equality)],[c_4065,c_4161])).

tff(c_4190,plain,(
    ! [A_7,B_8,D_491] : k4_zfmisc_1(A_7,B_8,'#skF_3',D_491) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4069,c_4177])).

tff(c_4064,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4055,c_3475])).

tff(c_4220,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4190,c_4064])).

%------------------------------------------------------------------------------
