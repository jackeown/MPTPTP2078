%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:45 EST 2020

% Result     : Theorem 3.63s
% Output     : CNFRefutation 3.98s
% Verified   : 
% Statistics : Number of formulae       :  252 (2191 expanded)
%              Number of leaves         :   19 ( 638 expanded)
%              Depth                    :   10
%              Number of atoms          :  318 (5808 expanded)
%              Number of equality atoms :  294 (5784 expanded)
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

tff(f_33,axiom,(
    ! [A,B,C,D] : k4_zfmisc_1(A,B,C,D) = k2_zfmisc_1(k3_zfmisc_1(A,B,C),D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_zfmisc_1)).

tff(f_61,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( A != k1_xboole_0
          & B != k1_xboole_0
          & C != k1_xboole_0
          & D != k1_xboole_0 )
      <=> k4_zfmisc_1(A,B,C,D) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_mcart_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0 )
    <=> k3_zfmisc_1(A,B,C) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_mcart_1)).

tff(c_3634,plain,(
    ! [A_428,B_429,C_430,D_431] : k2_zfmisc_1(k3_zfmisc_1(A_428,B_429,C_430),D_431) = k4_zfmisc_1(A_428,B_429,C_430,D_431) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2821,plain,(
    ! [A_328,B_329,C_330,D_331] : k2_zfmisc_1(k3_zfmisc_1(A_328,B_329,C_330),D_331) = k4_zfmisc_1(A_328,B_329,C_330,D_331) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1926,plain,(
    ! [A_224,B_225,C_226,D_227] : k2_zfmisc_1(k3_zfmisc_1(A_224,B_225,C_226),D_227) = k4_zfmisc_1(A_224,B_225,C_226,D_227) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_36,plain,
    ( k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k1_xboole_0
    | k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_104,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_32,plain,
    ( k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k1_xboole_0
    | k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_105,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_28,plain,
    ( k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k1_xboole_0
    | k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_106,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_24,plain,
    ( k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k1_xboole_0
    | k1_xboole_0 != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_107,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_18,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1'
    | k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_191,plain,(
    k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_18])).

tff(c_136,plain,(
    ! [A_23,B_24,C_25,D_26] : k2_zfmisc_1(k3_zfmisc_1(A_23,B_24,C_25),D_26) = k4_zfmisc_1(A_23,B_24,C_25,D_26) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( k1_xboole_0 = B_2
      | k1_xboole_0 = A_1
      | k2_zfmisc_1(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_250,plain,(
    ! [D_39,A_40,B_41,C_42] :
      ( k1_xboole_0 = D_39
      | k3_zfmisc_1(A_40,B_41,C_42) = k1_xboole_0
      | k4_zfmisc_1(A_40,B_41,C_42,D_39) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_2])).

tff(c_259,plain,
    ( k1_xboole_0 = '#skF_8'
    | k3_zfmisc_1('#skF_5','#skF_6','#skF_7') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_191,c_250])).

tff(c_272,plain,(
    k3_zfmisc_1('#skF_5','#skF_6','#skF_7') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_107,c_259])).

tff(c_10,plain,(
    ! [A_7,B_8,C_9] :
      ( k3_zfmisc_1(A_7,B_8,C_9) != k1_xboole_0
      | k1_xboole_0 = C_9
      | k1_xboole_0 = B_8
      | k1_xboole_0 = A_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_283,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_272,c_10])).

tff(c_290,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_105,c_106,c_283])).

tff(c_291,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_347,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_291])).

tff(c_4,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_376,plain,(
    ! [A_50] : k2_zfmisc_1(A_50,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_347,c_347,c_4])).

tff(c_8,plain,(
    ! [A_3,B_4,C_5,D_6] : k2_zfmisc_1(k3_zfmisc_1(A_3,B_4,C_5),D_6) = k4_zfmisc_1(A_3,B_4,C_5,D_6) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_385,plain,(
    ! [A_3,B_4,C_5] : k4_zfmisc_1(A_3,B_4,C_5,'#skF_4') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_376,c_8])).

tff(c_20,plain,
    ( k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k1_xboole_0
    | k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_135,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_20])).

tff(c_353,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_347,c_135])).

tff(c_458,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_385,c_353])).

tff(c_459,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_291])).

tff(c_461,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_459])).

tff(c_6,plain,(
    ! [B_2] : k2_zfmisc_1(k1_xboole_0,B_2) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_479,plain,(
    ! [B_2] : k2_zfmisc_1('#skF_1',B_2) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_461,c_461,c_6])).

tff(c_16,plain,(
    ! [B_8,C_9] : k3_zfmisc_1(k1_xboole_0,B_8,C_9) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_525,plain,(
    ! [B_61,C_62] : k3_zfmisc_1('#skF_1',B_61,C_62) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_461,c_461,c_16])).

tff(c_533,plain,(
    ! [B_61,C_62,D_6] : k4_zfmisc_1('#skF_1',B_61,C_62,D_6) = k2_zfmisc_1('#skF_1',D_6) ),
    inference(superposition,[status(thm),theory(equality)],[c_525,c_8])).

tff(c_541,plain,(
    ! [B_61,C_62,D_6] : k4_zfmisc_1('#skF_1',B_61,C_62,D_6) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_479,c_533])).

tff(c_468,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_461,c_135])).

tff(c_632,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_541,c_468])).

tff(c_633,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_459])).

tff(c_635,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_633])).

tff(c_654,plain,(
    ! [B_2] : k2_zfmisc_1('#skF_3',B_2) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_635,c_635,c_6])).

tff(c_12,plain,(
    ! [A_7,B_8] : k3_zfmisc_1(A_7,B_8,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_719,plain,(
    ! [A_82,B_83] : k3_zfmisc_1(A_82,B_83,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_635,c_635,c_12])).

tff(c_730,plain,(
    ! [A_82,B_83,D_6] : k4_zfmisc_1(A_82,B_83,'#skF_3',D_6) = k2_zfmisc_1('#skF_3',D_6) ),
    inference(superposition,[status(thm),theory(equality)],[c_719,c_8])).

tff(c_742,plain,(
    ! [A_82,B_83,D_6] : k4_zfmisc_1(A_82,B_83,'#skF_3',D_6) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_654,c_730])).

tff(c_643,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_635,c_135])).

tff(c_748,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_742,c_643])).

tff(c_749,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_633])).

tff(c_14,plain,(
    ! [A_7,C_9] : k3_zfmisc_1(A_7,k1_xboole_0,C_9) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_155,plain,(
    ! [A_7,C_9,D_26] : k4_zfmisc_1(A_7,k1_xboole_0,C_9,D_26) = k2_zfmisc_1(k1_xboole_0,D_26) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_136])).

tff(c_166,plain,(
    ! [A_7,C_9,D_26] : k4_zfmisc_1(A_7,k1_xboole_0,C_9,D_26) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_155])).

tff(c_755,plain,(
    ! [A_7,C_9,D_26] : k4_zfmisc_1(A_7,'#skF_2',C_9,D_26) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_749,c_749,c_166])).

tff(c_759,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_749,c_135])).

tff(c_871,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_755,c_759])).

tff(c_872,plain,(
    k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_882,plain,(
    ! [A_95,B_96,C_97,D_98] : k2_zfmisc_1(k3_zfmisc_1(A_95,B_96,C_97),D_98) = k4_zfmisc_1(A_95,B_96,C_97,D_98) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_992,plain,(
    ! [D_111,A_112,B_113,C_114] :
      ( k1_xboole_0 = D_111
      | k3_zfmisc_1(A_112,B_113,C_114) = k1_xboole_0
      | k4_zfmisc_1(A_112,B_113,C_114,D_111) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_882,c_2])).

tff(c_1010,plain,
    ( k1_xboole_0 = '#skF_8'
    | k3_zfmisc_1('#skF_5','#skF_6','#skF_7') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_872,c_992])).

tff(c_1022,plain,(
    k3_zfmisc_1('#skF_5','#skF_6','#skF_7') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_107,c_1010])).

tff(c_1029,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_1022,c_10])).

tff(c_1036,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_105,c_106,c_1029])).

tff(c_1038,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_1046,plain,(
    ! [B_2] : k2_zfmisc_1('#skF_8',B_2) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1038,c_1038,c_6])).

tff(c_1042,plain,(
    ! [A_7,B_8] : k3_zfmisc_1(A_7,B_8,'#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1038,c_1038,c_12])).

tff(c_1456,plain,(
    ! [A_165,B_166,C_167,D_168] : k2_zfmisc_1(k3_zfmisc_1(A_165,B_166,C_167),D_168) = k4_zfmisc_1(A_165,B_166,C_167,D_168) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1472,plain,(
    ! [A_7,B_8,D_168] : k4_zfmisc_1(A_7,B_8,'#skF_8',D_168) = k2_zfmisc_1('#skF_8',D_168) ),
    inference(superposition,[status(thm),theory(equality)],[c_1042,c_1456])).

tff(c_1485,plain,(
    ! [A_7,B_8,D_168] : k4_zfmisc_1(A_7,B_8,'#skF_8',D_168) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1046,c_1472])).

tff(c_1043,plain,(
    ! [A_7,C_9] : k3_zfmisc_1(A_7,'#skF_8',C_9) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1038,c_1038,c_14])).

tff(c_1386,plain,(
    ! [A_155,B_156,C_157,D_158] : k2_zfmisc_1(k3_zfmisc_1(A_155,B_156,C_157),D_158) = k4_zfmisc_1(A_155,B_156,C_157,D_158) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1408,plain,(
    ! [A_7,C_9,D_158] : k4_zfmisc_1(A_7,'#skF_8',C_9,D_158) = k2_zfmisc_1('#skF_8',D_158) ),
    inference(superposition,[status(thm),theory(equality)],[c_1043,c_1386])).

tff(c_1417,plain,(
    ! [A_7,C_9,D_158] : k4_zfmisc_1(A_7,'#skF_8',C_9,D_158) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1046,c_1408])).

tff(c_1322,plain,(
    ! [A_148,B_149,C_150,D_151] : k2_zfmisc_1(k3_zfmisc_1(A_148,B_149,C_150),D_151) = k4_zfmisc_1(A_148,B_149,C_150,D_151) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1044,plain,(
    ! [B_8,C_9] : k3_zfmisc_1('#skF_8',B_8,C_9) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1038,c_1038,c_16])).

tff(c_1142,plain,(
    ! [A_125,B_126,C_127,D_128] : k2_zfmisc_1(k3_zfmisc_1(A_125,B_126,C_127),D_128) = k4_zfmisc_1(A_125,B_126,C_127,D_128) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1161,plain,(
    ! [B_8,C_9,D_128] : k4_zfmisc_1('#skF_8',B_8,C_9,D_128) = k2_zfmisc_1('#skF_8',D_128) ),
    inference(superposition,[status(thm),theory(equality)],[c_1044,c_1142])).

tff(c_1172,plain,(
    ! [B_8,C_9,D_128] : k4_zfmisc_1('#skF_8',B_8,C_9,D_128) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1046,c_1161])).

tff(c_22,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1133,plain,
    ( '#skF_8' = '#skF_4'
    | '#skF_3' = '#skF_8'
    | '#skF_2' = '#skF_8'
    | '#skF_1' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1038,c_1038,c_1038,c_1038,c_1038,c_22])).

tff(c_1134,plain,(
    '#skF_1' = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_1133])).

tff(c_1037,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_1119,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1038,c_1037])).

tff(c_1135,plain,(
    k4_zfmisc_1('#skF_8','#skF_2','#skF_3','#skF_4') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1134,c_1119])).

tff(c_1216,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1172,c_1135])).

tff(c_1217,plain,
    ( '#skF_2' = '#skF_8'
    | '#skF_3' = '#skF_8'
    | '#skF_8' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1133])).

tff(c_1219,plain,(
    '#skF_8' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_1217])).

tff(c_1045,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,'#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1038,c_1038,c_4])).

tff(c_1228,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1219,c_1219,c_1045])).

tff(c_1332,plain,(
    ! [A_148,B_149,C_150] : k4_zfmisc_1(A_148,B_149,C_150,'#skF_4') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_1322,c_1228])).

tff(c_1224,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1219,c_1119])).

tff(c_1373,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1332,c_1224])).

tff(c_1374,plain,
    ( '#skF_3' = '#skF_8'
    | '#skF_2' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_1217])).

tff(c_1376,plain,(
    '#skF_2' = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_1374])).

tff(c_1379,plain,(
    k4_zfmisc_1('#skF_1','#skF_8','#skF_3','#skF_4') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1376,c_1119])).

tff(c_1444,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1417,c_1379])).

tff(c_1445,plain,(
    '#skF_3' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_1374])).

tff(c_1447,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_8','#skF_4') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1445,c_1119])).

tff(c_1530,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1485,c_1447])).

tff(c_1532,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_26,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1629,plain,
    ( '#skF_7' = '#skF_4'
    | '#skF_7' = '#skF_3'
    | '#skF_7' = '#skF_2'
    | '#skF_7' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1532,c_1532,c_1532,c_1532,c_1532,c_26])).

tff(c_1630,plain,(
    '#skF_7' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_1629])).

tff(c_1539,plain,(
    ! [B_2] : k2_zfmisc_1('#skF_7',B_2) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1532,c_1532,c_6])).

tff(c_1636,plain,(
    ! [B_2] : k2_zfmisc_1('#skF_1',B_2) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1630,c_1630,c_1539])).

tff(c_1537,plain,(
    ! [B_8,C_9] : k3_zfmisc_1('#skF_7',B_8,C_9) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1532,c_1532,c_16])).

tff(c_1635,plain,(
    ! [B_8,C_9] : k3_zfmisc_1('#skF_1',B_8,C_9) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1630,c_1630,c_1537])).

tff(c_1746,plain,(
    ! [A_201,B_202,C_203,D_204] : k2_zfmisc_1(k3_zfmisc_1(A_201,B_202,C_203),D_204) = k4_zfmisc_1(A_201,B_202,C_203,D_204) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1762,plain,(
    ! [B_8,C_9,D_204] : k4_zfmisc_1('#skF_1',B_8,C_9,D_204) = k2_zfmisc_1('#skF_1',D_204) ),
    inference(superposition,[status(thm),theory(equality)],[c_1635,c_1746])).

tff(c_1775,plain,(
    ! [B_8,C_9,D_204] : k4_zfmisc_1('#skF_1',B_8,C_9,D_204) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1636,c_1762])).

tff(c_1531,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_1613,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1532,c_1531])).

tff(c_1632,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1630,c_1613])).

tff(c_1804,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1775,c_1632])).

tff(c_1805,plain,
    ( '#skF_7' = '#skF_2'
    | '#skF_7' = '#skF_3'
    | '#skF_7' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1629])).

tff(c_1807,plain,(
    '#skF_7' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_1805])).

tff(c_1538,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,'#skF_7') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1532,c_1532,c_4])).

tff(c_1815,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1807,c_1807,c_1538])).

tff(c_1936,plain,(
    ! [A_224,B_225,C_226] : k4_zfmisc_1(A_224,B_225,C_226,'#skF_4') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_1926,c_1815])).

tff(c_1810,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1807,c_1613])).

tff(c_1960,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1936,c_1810])).

tff(c_1961,plain,
    ( '#skF_7' = '#skF_3'
    | '#skF_7' = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_1805])).

tff(c_1963,plain,(
    '#skF_7' = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_1961])).

tff(c_1971,plain,(
    ! [B_2] : k2_zfmisc_1('#skF_2',B_2) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1963,c_1963,c_1539])).

tff(c_1536,plain,(
    ! [A_7,C_9] : k3_zfmisc_1(A_7,'#skF_7',C_9) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1532,c_1532,c_14])).

tff(c_1969,plain,(
    ! [A_7,C_9] : k3_zfmisc_1(A_7,'#skF_2',C_9) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1963,c_1963,c_1536])).

tff(c_2084,plain,(
    ! [A_241,B_242,C_243,D_244] : k2_zfmisc_1(k3_zfmisc_1(A_241,B_242,C_243),D_244) = k4_zfmisc_1(A_241,B_242,C_243,D_244) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2100,plain,(
    ! [A_7,C_9,D_244] : k4_zfmisc_1(A_7,'#skF_2',C_9,D_244) = k2_zfmisc_1('#skF_2',D_244) ),
    inference(superposition,[status(thm),theory(equality)],[c_1969,c_2084])).

tff(c_2113,plain,(
    ! [A_7,C_9,D_244] : k4_zfmisc_1(A_7,'#skF_2',C_9,D_244) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1971,c_2100])).

tff(c_1976,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1963,c_1532])).

tff(c_2054,plain,
    ( k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_2'
    | k4_zfmisc_1('#skF_5','#skF_6','#skF_2','#skF_8') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1976,c_1963,c_1976,c_20])).

tff(c_2055,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_2054])).

tff(c_2128,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2113,c_2055])).

tff(c_2130,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_2054])).

tff(c_1967,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1963,c_1613])).

tff(c_2142,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2130,c_1967])).

tff(c_2143,plain,(
    '#skF_7' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1961])).

tff(c_2152,plain,(
    ! [B_2] : k2_zfmisc_1('#skF_3',B_2) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2143,c_2143,c_1539])).

tff(c_1535,plain,(
    ! [A_7,B_8] : k3_zfmisc_1(A_7,B_8,'#skF_7') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1532,c_1532,c_12])).

tff(c_2149,plain,(
    ! [A_7,B_8] : k3_zfmisc_1(A_7,B_8,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2143,c_2143,c_1535])).

tff(c_2265,plain,(
    ! [A_261,B_262,C_263,D_264] : k2_zfmisc_1(k3_zfmisc_1(A_261,B_262,C_263),D_264) = k4_zfmisc_1(A_261,B_262,C_263,D_264) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2284,plain,(
    ! [A_7,B_8,D_264] : k4_zfmisc_1(A_7,B_8,'#skF_3',D_264) = k2_zfmisc_1('#skF_3',D_264) ),
    inference(superposition,[status(thm),theory(equality)],[c_2149,c_2265])).

tff(c_2295,plain,(
    ! [A_7,B_8,D_264] : k4_zfmisc_1(A_7,B_8,'#skF_3',D_264) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2152,c_2284])).

tff(c_2148,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2143,c_1613])).

tff(c_2324,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2295,c_2148])).

tff(c_2326,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_30,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_2425,plain,
    ( '#skF_6' = '#skF_4'
    | '#skF_6' = '#skF_3'
    | '#skF_6' = '#skF_2'
    | '#skF_6' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2326,c_2326,c_2326,c_2326,c_2326,c_30])).

tff(c_2426,plain,(
    '#skF_6' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_2425])).

tff(c_2325,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_2406,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2326,c_2325])).

tff(c_2429,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2426,c_2406])).

tff(c_2332,plain,(
    ! [B_2] : k2_zfmisc_1('#skF_6',B_2) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2326,c_2326,c_6])).

tff(c_2434,plain,(
    ! [B_2] : k2_zfmisc_1('#skF_1',B_2) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2426,c_2426,c_2332])).

tff(c_2330,plain,(
    ! [B_8,C_9] : k3_zfmisc_1('#skF_6',B_8,C_9) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2326,c_2326,c_16])).

tff(c_2432,plain,(
    ! [B_8,C_9] : k3_zfmisc_1('#skF_1',B_8,C_9) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2426,c_2426,c_2330])).

tff(c_2544,plain,(
    ! [A_294,B_295,C_296,D_297] : k2_zfmisc_1(k3_zfmisc_1(A_294,B_295,C_296),D_297) = k4_zfmisc_1(A_294,B_295,C_296,D_297) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2560,plain,(
    ! [B_8,C_9,D_297] : k4_zfmisc_1('#skF_1',B_8,C_9,D_297) = k2_zfmisc_1('#skF_1',D_297) ),
    inference(superposition,[status(thm),theory(equality)],[c_2432,c_2544])).

tff(c_2573,plain,(
    ! [B_8,C_9,D_297] : k4_zfmisc_1('#skF_1',B_8,C_9,D_297) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2434,c_2560])).

tff(c_2437,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2426,c_2326])).

tff(c_2446,plain,
    ( k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_1'
    | k4_zfmisc_1('#skF_5','#skF_1','#skF_7','#skF_8') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2437,c_2426,c_2437,c_20])).

tff(c_2447,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_2446])).

tff(c_2624,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2573,c_2447])).

tff(c_2626,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_2446])).

tff(c_2699,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2429,c_2626])).

tff(c_2700,plain,
    ( '#skF_6' = '#skF_2'
    | '#skF_6' = '#skF_3'
    | '#skF_6' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_2425])).

tff(c_2702,plain,(
    '#skF_6' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_2700])).

tff(c_2331,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2326,c_2326,c_4])).

tff(c_2711,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2702,c_2702,c_2331])).

tff(c_2831,plain,(
    ! [A_328,B_329,C_330] : k4_zfmisc_1(A_328,B_329,C_330,'#skF_4') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_2821,c_2711])).

tff(c_2707,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2702,c_2406])).

tff(c_2855,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2831,c_2707])).

tff(c_2856,plain,
    ( '#skF_6' = '#skF_3'
    | '#skF_6' = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_2700])).

tff(c_2858,plain,(
    '#skF_6' = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_2856])).

tff(c_2869,plain,(
    ! [B_2] : k2_zfmisc_1('#skF_2',B_2) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2858,c_2858,c_2332])).

tff(c_2329,plain,(
    ! [A_7,C_9] : k3_zfmisc_1(A_7,'#skF_6',C_9) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2326,c_2326,c_14])).

tff(c_2866,plain,(
    ! [A_7,C_9] : k3_zfmisc_1(A_7,'#skF_2',C_9) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2858,c_2858,c_2329])).

tff(c_2978,plain,(
    ! [A_345,B_346,C_347,D_348] : k2_zfmisc_1(k3_zfmisc_1(A_345,B_346,C_347),D_348) = k4_zfmisc_1(A_345,B_346,C_347,D_348) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2994,plain,(
    ! [A_7,C_9,D_348] : k4_zfmisc_1(A_7,'#skF_2',C_9,D_348) = k2_zfmisc_1('#skF_2',D_348) ),
    inference(superposition,[status(thm),theory(equality)],[c_2866,c_2978])).

tff(c_3007,plain,(
    ! [A_7,C_9,D_348] : k4_zfmisc_1(A_7,'#skF_2',C_9,D_348) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2869,c_2994])).

tff(c_2864,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2858,c_2406])).

tff(c_3074,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3007,c_2864])).

tff(c_3075,plain,(
    '#skF_6' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_2856])).

tff(c_3086,plain,(
    ! [B_2] : k2_zfmisc_1('#skF_3',B_2) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3075,c_3075,c_2332])).

tff(c_2328,plain,(
    ! [A_7,B_8] : k3_zfmisc_1(A_7,B_8,'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2326,c_2326,c_12])).

tff(c_3082,plain,(
    ! [A_7,B_8] : k3_zfmisc_1(A_7,B_8,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3075,c_3075,c_2328])).

tff(c_3198,plain,(
    ! [A_375,B_376,C_377,D_378] : k2_zfmisc_1(k3_zfmisc_1(A_375,B_376,C_377),D_378) = k4_zfmisc_1(A_375,B_376,C_377,D_378) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_3214,plain,(
    ! [A_7,B_8,D_378] : k4_zfmisc_1(A_7,B_8,'#skF_3',D_378) = k2_zfmisc_1('#skF_3',D_378) ),
    inference(superposition,[status(thm),theory(equality)],[c_3082,c_3198])).

tff(c_3227,plain,(
    ! [A_7,B_8,D_378] : k4_zfmisc_1(A_7,B_8,'#skF_3',D_378) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3086,c_3214])).

tff(c_3081,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3075,c_2406])).

tff(c_3255,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3227,c_3081])).

tff(c_3257,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_34,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_3354,plain,
    ( '#skF_5' = '#skF_4'
    | '#skF_5' = '#skF_3'
    | '#skF_5' = '#skF_2'
    | '#skF_5' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3257,c_3257,c_3257,c_3257,c_3257,c_34])).

tff(c_3355,plain,(
    '#skF_5' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_3354])).

tff(c_3262,plain,(
    ! [B_2] : k2_zfmisc_1('#skF_5',B_2) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3257,c_3257,c_6])).

tff(c_3362,plain,(
    ! [B_2] : k2_zfmisc_1('#skF_1',B_2) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3355,c_3355,c_3262])).

tff(c_3260,plain,(
    ! [B_8,C_9] : k3_zfmisc_1('#skF_5',B_8,C_9) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3257,c_3257,c_16])).

tff(c_3359,plain,(
    ! [B_8,C_9] : k3_zfmisc_1('#skF_1',B_8,C_9) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3355,c_3355,c_3260])).

tff(c_3454,plain,(
    ! [A_405,B_406,C_407,D_408] : k2_zfmisc_1(k3_zfmisc_1(A_405,B_406,C_407),D_408) = k4_zfmisc_1(A_405,B_406,C_407,D_408) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_3473,plain,(
    ! [B_8,C_9,D_408] : k4_zfmisc_1('#skF_1',B_8,C_9,D_408) = k2_zfmisc_1('#skF_1',D_408) ),
    inference(superposition,[status(thm),theory(equality)],[c_3359,c_3454])).

tff(c_3484,plain,(
    ! [B_8,C_9,D_408] : k4_zfmisc_1('#skF_1',B_8,C_9,D_408) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3362,c_3473])).

tff(c_3256,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_3336,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3257,c_3256])).

tff(c_3358,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3355,c_3336])).

tff(c_3512,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3484,c_3358])).

tff(c_3513,plain,
    ( '#skF_5' = '#skF_2'
    | '#skF_5' = '#skF_3'
    | '#skF_5' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_3354])).

tff(c_3515,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_3513])).

tff(c_3261,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3257,c_3257,c_4])).

tff(c_3525,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3515,c_3515,c_3261])).

tff(c_3644,plain,(
    ! [A_428,B_429,C_430] : k4_zfmisc_1(A_428,B_429,C_430,'#skF_4') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_3634,c_3525])).

tff(c_3519,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3515,c_3336])).

tff(c_3669,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3644,c_3519])).

tff(c_3670,plain,
    ( '#skF_5' = '#skF_3'
    | '#skF_5' = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_3513])).

tff(c_3672,plain,(
    '#skF_5' = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_3670])).

tff(c_3681,plain,(
    ! [B_2] : k2_zfmisc_1('#skF_2',B_2) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3672,c_3672,c_3262])).

tff(c_3259,plain,(
    ! [A_7,C_9] : k3_zfmisc_1(A_7,'#skF_5',C_9) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3257,c_3257,c_14])).

tff(c_3679,plain,(
    ! [A_7,C_9] : k3_zfmisc_1(A_7,'#skF_2',C_9) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3672,c_3672,c_3259])).

tff(c_3793,plain,(
    ! [A_445,B_446,C_447,D_448] : k2_zfmisc_1(k3_zfmisc_1(A_445,B_446,C_447),D_448) = k4_zfmisc_1(A_445,B_446,C_447,D_448) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_3815,plain,(
    ! [A_7,C_9,D_448] : k4_zfmisc_1(A_7,'#skF_2',C_9,D_448) = k2_zfmisc_1('#skF_2',D_448) ),
    inference(superposition,[status(thm),theory(equality)],[c_3679,c_3793])).

tff(c_3824,plain,(
    ! [A_7,C_9,D_448] : k4_zfmisc_1(A_7,'#skF_2',C_9,D_448) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3681,c_3815])).

tff(c_3677,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3672,c_3336])).

tff(c_3875,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3824,c_3677])).

tff(c_3876,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_3670])).

tff(c_3886,plain,(
    ! [B_2] : k2_zfmisc_1('#skF_3',B_2) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3876,c_3876,c_3262])).

tff(c_3258,plain,(
    ! [A_7,B_8] : k3_zfmisc_1(A_7,B_8,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3257,c_3257,c_12])).

tff(c_3885,plain,(
    ! [A_7,B_8] : k3_zfmisc_1(A_7,B_8,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3876,c_3876,c_3258])).

tff(c_3981,plain,(
    ! [A_468,B_469,C_470,D_471] : k2_zfmisc_1(k3_zfmisc_1(A_468,B_469,C_470),D_471) = k4_zfmisc_1(A_468,B_469,C_470,D_471) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_4003,plain,(
    ! [A_7,B_8,D_471] : k4_zfmisc_1(A_7,B_8,'#skF_3',D_471) = k2_zfmisc_1('#skF_3',D_471) ),
    inference(superposition,[status(thm),theory(equality)],[c_3885,c_3981])).

tff(c_4012,plain,(
    ! [A_7,B_8,D_471] : k4_zfmisc_1(A_7,B_8,'#skF_3',D_471) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3886,c_4003])).

tff(c_3882,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3876,c_3336])).

tff(c_4056,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4012,c_3882])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:51:53 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.63/1.87  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.63/1.91  
% 3.63/1.91  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.63/1.91  %$ k4_zfmisc_1 > k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4
% 3.63/1.91  
% 3.63/1.91  %Foreground sorts:
% 3.63/1.91  
% 3.63/1.91  
% 3.63/1.91  %Background operators:
% 3.63/1.91  
% 3.63/1.91  
% 3.63/1.91  %Foreground operators:
% 3.63/1.91  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.63/1.91  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.63/1.91  tff(k4_zfmisc_1, type, k4_zfmisc_1: ($i * $i * $i * $i) > $i).
% 3.63/1.91  tff('#skF_7', type, '#skF_7': $i).
% 3.63/1.91  tff('#skF_5', type, '#skF_5': $i).
% 3.63/1.91  tff('#skF_6', type, '#skF_6': $i).
% 3.63/1.91  tff('#skF_2', type, '#skF_2': $i).
% 3.63/1.91  tff('#skF_3', type, '#skF_3': $i).
% 3.63/1.91  tff('#skF_1', type, '#skF_1': $i).
% 3.63/1.91  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 3.63/1.91  tff('#skF_8', type, '#skF_8': $i).
% 3.63/1.91  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.63/1.91  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.63/1.91  tff('#skF_4', type, '#skF_4': $i).
% 3.63/1.91  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.63/1.91  
% 3.98/1.94  tff(f_33, axiom, (![A, B, C, D]: (k4_zfmisc_1(A, B, C, D) = k2_zfmisc_1(k3_zfmisc_1(A, B, C), D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_zfmisc_1)).
% 3.98/1.94  tff(f_61, negated_conjecture, ~(![A, B, C, D]: ((((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(D = k1_xboole_0)) <=> ~(k4_zfmisc_1(A, B, C, D) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_mcart_1)).
% 3.98/1.94  tff(f_31, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.98/1.94  tff(f_45, axiom, (![A, B, C]: (((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) <=> ~(k3_zfmisc_1(A, B, C) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_mcart_1)).
% 3.98/1.94  tff(c_3634, plain, (![A_428, B_429, C_430, D_431]: (k2_zfmisc_1(k3_zfmisc_1(A_428, B_429, C_430), D_431)=k4_zfmisc_1(A_428, B_429, C_430, D_431))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.98/1.94  tff(c_2821, plain, (![A_328, B_329, C_330, D_331]: (k2_zfmisc_1(k3_zfmisc_1(A_328, B_329, C_330), D_331)=k4_zfmisc_1(A_328, B_329, C_330, D_331))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.98/1.94  tff(c_1926, plain, (![A_224, B_225, C_226, D_227]: (k2_zfmisc_1(k3_zfmisc_1(A_224, B_225, C_226), D_227)=k4_zfmisc_1(A_224, B_225, C_226, D_227))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.98/1.94  tff(c_36, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0 | k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.98/1.94  tff(c_104, plain, (k1_xboole_0!='#skF_5'), inference(splitLeft, [status(thm)], [c_36])).
% 3.98/1.94  tff(c_32, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0 | k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.98/1.94  tff(c_105, plain, (k1_xboole_0!='#skF_6'), inference(splitLeft, [status(thm)], [c_32])).
% 3.98/1.94  tff(c_28, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0 | k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.98/1.94  tff(c_106, plain, (k1_xboole_0!='#skF_7'), inference(splitLeft, [status(thm)], [c_28])).
% 3.98/1.94  tff(c_24, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0 | k1_xboole_0!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.98/1.94  tff(c_107, plain, (k1_xboole_0!='#skF_8'), inference(splitLeft, [status(thm)], [c_24])).
% 3.98/1.94  tff(c_18, plain, (k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1' | k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.98/1.94  tff(c_191, plain, (k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_18])).
% 3.98/1.94  tff(c_136, plain, (![A_23, B_24, C_25, D_26]: (k2_zfmisc_1(k3_zfmisc_1(A_23, B_24, C_25), D_26)=k4_zfmisc_1(A_23, B_24, C_25, D_26))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.98/1.94  tff(c_2, plain, (![B_2, A_1]: (k1_xboole_0=B_2 | k1_xboole_0=A_1 | k2_zfmisc_1(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.98/1.94  tff(c_250, plain, (![D_39, A_40, B_41, C_42]: (k1_xboole_0=D_39 | k3_zfmisc_1(A_40, B_41, C_42)=k1_xboole_0 | k4_zfmisc_1(A_40, B_41, C_42, D_39)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_136, c_2])).
% 3.98/1.94  tff(c_259, plain, (k1_xboole_0='#skF_8' | k3_zfmisc_1('#skF_5', '#skF_6', '#skF_7')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_191, c_250])).
% 3.98/1.94  tff(c_272, plain, (k3_zfmisc_1('#skF_5', '#skF_6', '#skF_7')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_107, c_259])).
% 3.98/1.94  tff(c_10, plain, (![A_7, B_8, C_9]: (k3_zfmisc_1(A_7, B_8, C_9)!=k1_xboole_0 | k1_xboole_0=C_9 | k1_xboole_0=B_8 | k1_xboole_0=A_7)), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.98/1.94  tff(c_283, plain, (k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_272, c_10])).
% 3.98/1.94  tff(c_290, plain, $false, inference(negUnitSimplification, [status(thm)], [c_104, c_105, c_106, c_283])).
% 3.98/1.94  tff(c_291, plain, (k1_xboole_0='#skF_1' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_18])).
% 3.98/1.94  tff(c_347, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_291])).
% 3.98/1.94  tff(c_4, plain, (![A_1]: (k2_zfmisc_1(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.98/1.94  tff(c_376, plain, (![A_50]: (k2_zfmisc_1(A_50, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_347, c_347, c_4])).
% 3.98/1.94  tff(c_8, plain, (![A_3, B_4, C_5, D_6]: (k2_zfmisc_1(k3_zfmisc_1(A_3, B_4, C_5), D_6)=k4_zfmisc_1(A_3, B_4, C_5, D_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.98/1.94  tff(c_385, plain, (![A_3, B_4, C_5]: (k4_zfmisc_1(A_3, B_4, C_5, '#skF_4')='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_376, c_8])).
% 3.98/1.94  tff(c_20, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0 | k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.98/1.94  tff(c_135, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_20])).
% 3.98/1.94  tff(c_353, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_347, c_135])).
% 3.98/1.94  tff(c_458, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_385, c_353])).
% 3.98/1.94  tff(c_459, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_291])).
% 3.98/1.94  tff(c_461, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_459])).
% 3.98/1.94  tff(c_6, plain, (![B_2]: (k2_zfmisc_1(k1_xboole_0, B_2)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.98/1.94  tff(c_479, plain, (![B_2]: (k2_zfmisc_1('#skF_1', B_2)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_461, c_461, c_6])).
% 3.98/1.94  tff(c_16, plain, (![B_8, C_9]: (k3_zfmisc_1(k1_xboole_0, B_8, C_9)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.98/1.94  tff(c_525, plain, (![B_61, C_62]: (k3_zfmisc_1('#skF_1', B_61, C_62)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_461, c_461, c_16])).
% 3.98/1.94  tff(c_533, plain, (![B_61, C_62, D_6]: (k4_zfmisc_1('#skF_1', B_61, C_62, D_6)=k2_zfmisc_1('#skF_1', D_6))), inference(superposition, [status(thm), theory('equality')], [c_525, c_8])).
% 3.98/1.94  tff(c_541, plain, (![B_61, C_62, D_6]: (k4_zfmisc_1('#skF_1', B_61, C_62, D_6)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_479, c_533])).
% 3.98/1.94  tff(c_468, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_461, c_135])).
% 3.98/1.94  tff(c_632, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_541, c_468])).
% 3.98/1.94  tff(c_633, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_459])).
% 3.98/1.94  tff(c_635, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_633])).
% 3.98/1.94  tff(c_654, plain, (![B_2]: (k2_zfmisc_1('#skF_3', B_2)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_635, c_635, c_6])).
% 3.98/1.94  tff(c_12, plain, (![A_7, B_8]: (k3_zfmisc_1(A_7, B_8, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.98/1.94  tff(c_719, plain, (![A_82, B_83]: (k3_zfmisc_1(A_82, B_83, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_635, c_635, c_12])).
% 3.98/1.94  tff(c_730, plain, (![A_82, B_83, D_6]: (k4_zfmisc_1(A_82, B_83, '#skF_3', D_6)=k2_zfmisc_1('#skF_3', D_6))), inference(superposition, [status(thm), theory('equality')], [c_719, c_8])).
% 3.98/1.94  tff(c_742, plain, (![A_82, B_83, D_6]: (k4_zfmisc_1(A_82, B_83, '#skF_3', D_6)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_654, c_730])).
% 3.98/1.94  tff(c_643, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_635, c_135])).
% 3.98/1.94  tff(c_748, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_742, c_643])).
% 3.98/1.94  tff(c_749, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_633])).
% 3.98/1.94  tff(c_14, plain, (![A_7, C_9]: (k3_zfmisc_1(A_7, k1_xboole_0, C_9)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.98/1.94  tff(c_155, plain, (![A_7, C_9, D_26]: (k4_zfmisc_1(A_7, k1_xboole_0, C_9, D_26)=k2_zfmisc_1(k1_xboole_0, D_26))), inference(superposition, [status(thm), theory('equality')], [c_14, c_136])).
% 3.98/1.94  tff(c_166, plain, (![A_7, C_9, D_26]: (k4_zfmisc_1(A_7, k1_xboole_0, C_9, D_26)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_155])).
% 3.98/1.94  tff(c_755, plain, (![A_7, C_9, D_26]: (k4_zfmisc_1(A_7, '#skF_2', C_9, D_26)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_749, c_749, c_166])).
% 3.98/1.94  tff(c_759, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_749, c_135])).
% 3.98/1.94  tff(c_871, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_755, c_759])).
% 3.98/1.94  tff(c_872, plain, (k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')=k1_xboole_0), inference(splitRight, [status(thm)], [c_20])).
% 3.98/1.94  tff(c_882, plain, (![A_95, B_96, C_97, D_98]: (k2_zfmisc_1(k3_zfmisc_1(A_95, B_96, C_97), D_98)=k4_zfmisc_1(A_95, B_96, C_97, D_98))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.98/1.94  tff(c_992, plain, (![D_111, A_112, B_113, C_114]: (k1_xboole_0=D_111 | k3_zfmisc_1(A_112, B_113, C_114)=k1_xboole_0 | k4_zfmisc_1(A_112, B_113, C_114, D_111)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_882, c_2])).
% 3.98/1.94  tff(c_1010, plain, (k1_xboole_0='#skF_8' | k3_zfmisc_1('#skF_5', '#skF_6', '#skF_7')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_872, c_992])).
% 3.98/1.94  tff(c_1022, plain, (k3_zfmisc_1('#skF_5', '#skF_6', '#skF_7')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_107, c_1010])).
% 3.98/1.94  tff(c_1029, plain, (k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_1022, c_10])).
% 3.98/1.94  tff(c_1036, plain, $false, inference(negUnitSimplification, [status(thm)], [c_104, c_105, c_106, c_1029])).
% 3.98/1.94  tff(c_1038, plain, (k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_24])).
% 3.98/1.94  tff(c_1046, plain, (![B_2]: (k2_zfmisc_1('#skF_8', B_2)='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1038, c_1038, c_6])).
% 3.98/1.94  tff(c_1042, plain, (![A_7, B_8]: (k3_zfmisc_1(A_7, B_8, '#skF_8')='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1038, c_1038, c_12])).
% 3.98/1.94  tff(c_1456, plain, (![A_165, B_166, C_167, D_168]: (k2_zfmisc_1(k3_zfmisc_1(A_165, B_166, C_167), D_168)=k4_zfmisc_1(A_165, B_166, C_167, D_168))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.98/1.94  tff(c_1472, plain, (![A_7, B_8, D_168]: (k4_zfmisc_1(A_7, B_8, '#skF_8', D_168)=k2_zfmisc_1('#skF_8', D_168))), inference(superposition, [status(thm), theory('equality')], [c_1042, c_1456])).
% 3.98/1.94  tff(c_1485, plain, (![A_7, B_8, D_168]: (k4_zfmisc_1(A_7, B_8, '#skF_8', D_168)='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1046, c_1472])).
% 3.98/1.94  tff(c_1043, plain, (![A_7, C_9]: (k3_zfmisc_1(A_7, '#skF_8', C_9)='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1038, c_1038, c_14])).
% 3.98/1.94  tff(c_1386, plain, (![A_155, B_156, C_157, D_158]: (k2_zfmisc_1(k3_zfmisc_1(A_155, B_156, C_157), D_158)=k4_zfmisc_1(A_155, B_156, C_157, D_158))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.98/1.94  tff(c_1408, plain, (![A_7, C_9, D_158]: (k4_zfmisc_1(A_7, '#skF_8', C_9, D_158)=k2_zfmisc_1('#skF_8', D_158))), inference(superposition, [status(thm), theory('equality')], [c_1043, c_1386])).
% 3.98/1.94  tff(c_1417, plain, (![A_7, C_9, D_158]: (k4_zfmisc_1(A_7, '#skF_8', C_9, D_158)='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1046, c_1408])).
% 3.98/1.94  tff(c_1322, plain, (![A_148, B_149, C_150, D_151]: (k2_zfmisc_1(k3_zfmisc_1(A_148, B_149, C_150), D_151)=k4_zfmisc_1(A_148, B_149, C_150, D_151))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.98/1.94  tff(c_1044, plain, (![B_8, C_9]: (k3_zfmisc_1('#skF_8', B_8, C_9)='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1038, c_1038, c_16])).
% 3.98/1.94  tff(c_1142, plain, (![A_125, B_126, C_127, D_128]: (k2_zfmisc_1(k3_zfmisc_1(A_125, B_126, C_127), D_128)=k4_zfmisc_1(A_125, B_126, C_127, D_128))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.98/1.94  tff(c_1161, plain, (![B_8, C_9, D_128]: (k4_zfmisc_1('#skF_8', B_8, C_9, D_128)=k2_zfmisc_1('#skF_8', D_128))), inference(superposition, [status(thm), theory('equality')], [c_1044, c_1142])).
% 3.98/1.94  tff(c_1172, plain, (![B_8, C_9, D_128]: (k4_zfmisc_1('#skF_8', B_8, C_9, D_128)='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1046, c_1161])).
% 3.98/1.94  tff(c_22, plain, (k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.98/1.94  tff(c_1133, plain, ('#skF_8'='#skF_4' | '#skF_3'='#skF_8' | '#skF_2'='#skF_8' | '#skF_1'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_1038, c_1038, c_1038, c_1038, c_1038, c_22])).
% 3.98/1.94  tff(c_1134, plain, ('#skF_1'='#skF_8'), inference(splitLeft, [status(thm)], [c_1133])).
% 3.98/1.94  tff(c_1037, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_24])).
% 3.98/1.94  tff(c_1119, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_1038, c_1037])).
% 3.98/1.94  tff(c_1135, plain, (k4_zfmisc_1('#skF_8', '#skF_2', '#skF_3', '#skF_4')!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_1134, c_1119])).
% 3.98/1.94  tff(c_1216, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1172, c_1135])).
% 3.98/1.94  tff(c_1217, plain, ('#skF_2'='#skF_8' | '#skF_3'='#skF_8' | '#skF_8'='#skF_4'), inference(splitRight, [status(thm)], [c_1133])).
% 3.98/1.94  tff(c_1219, plain, ('#skF_8'='#skF_4'), inference(splitLeft, [status(thm)], [c_1217])).
% 3.98/1.94  tff(c_1045, plain, (![A_1]: (k2_zfmisc_1(A_1, '#skF_8')='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1038, c_1038, c_4])).
% 3.98/1.94  tff(c_1228, plain, (![A_1]: (k2_zfmisc_1(A_1, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1219, c_1219, c_1045])).
% 3.98/1.94  tff(c_1332, plain, (![A_148, B_149, C_150]: (k4_zfmisc_1(A_148, B_149, C_150, '#skF_4')='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1322, c_1228])).
% 3.98/1.94  tff(c_1224, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1219, c_1119])).
% 3.98/1.94  tff(c_1373, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1332, c_1224])).
% 3.98/1.94  tff(c_1374, plain, ('#skF_3'='#skF_8' | '#skF_2'='#skF_8'), inference(splitRight, [status(thm)], [c_1217])).
% 3.98/1.94  tff(c_1376, plain, ('#skF_2'='#skF_8'), inference(splitLeft, [status(thm)], [c_1374])).
% 3.98/1.94  tff(c_1379, plain, (k4_zfmisc_1('#skF_1', '#skF_8', '#skF_3', '#skF_4')!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_1376, c_1119])).
% 3.98/1.94  tff(c_1444, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1417, c_1379])).
% 3.98/1.94  tff(c_1445, plain, ('#skF_3'='#skF_8'), inference(splitRight, [status(thm)], [c_1374])).
% 3.98/1.94  tff(c_1447, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_8', '#skF_4')!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_1445, c_1119])).
% 3.98/1.94  tff(c_1530, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1485, c_1447])).
% 3.98/1.94  tff(c_1532, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_28])).
% 3.98/1.94  tff(c_26, plain, (k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.98/1.94  tff(c_1629, plain, ('#skF_7'='#skF_4' | '#skF_7'='#skF_3' | '#skF_7'='#skF_2' | '#skF_7'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1532, c_1532, c_1532, c_1532, c_1532, c_26])).
% 3.98/1.94  tff(c_1630, plain, ('#skF_7'='#skF_1'), inference(splitLeft, [status(thm)], [c_1629])).
% 3.98/1.94  tff(c_1539, plain, (![B_2]: (k2_zfmisc_1('#skF_7', B_2)='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_1532, c_1532, c_6])).
% 3.98/1.94  tff(c_1636, plain, (![B_2]: (k2_zfmisc_1('#skF_1', B_2)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1630, c_1630, c_1539])).
% 3.98/1.94  tff(c_1537, plain, (![B_8, C_9]: (k3_zfmisc_1('#skF_7', B_8, C_9)='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_1532, c_1532, c_16])).
% 3.98/1.94  tff(c_1635, plain, (![B_8, C_9]: (k3_zfmisc_1('#skF_1', B_8, C_9)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1630, c_1630, c_1537])).
% 3.98/1.94  tff(c_1746, plain, (![A_201, B_202, C_203, D_204]: (k2_zfmisc_1(k3_zfmisc_1(A_201, B_202, C_203), D_204)=k4_zfmisc_1(A_201, B_202, C_203, D_204))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.98/1.94  tff(c_1762, plain, (![B_8, C_9, D_204]: (k4_zfmisc_1('#skF_1', B_8, C_9, D_204)=k2_zfmisc_1('#skF_1', D_204))), inference(superposition, [status(thm), theory('equality')], [c_1635, c_1746])).
% 3.98/1.94  tff(c_1775, plain, (![B_8, C_9, D_204]: (k4_zfmisc_1('#skF_1', B_8, C_9, D_204)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1636, c_1762])).
% 3.98/1.94  tff(c_1531, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_28])).
% 3.98/1.94  tff(c_1613, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_1532, c_1531])).
% 3.98/1.94  tff(c_1632, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1630, c_1613])).
% 3.98/1.94  tff(c_1804, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1775, c_1632])).
% 3.98/1.94  tff(c_1805, plain, ('#skF_7'='#skF_2' | '#skF_7'='#skF_3' | '#skF_7'='#skF_4'), inference(splitRight, [status(thm)], [c_1629])).
% 3.98/1.94  tff(c_1807, plain, ('#skF_7'='#skF_4'), inference(splitLeft, [status(thm)], [c_1805])).
% 3.98/1.94  tff(c_1538, plain, (![A_1]: (k2_zfmisc_1(A_1, '#skF_7')='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_1532, c_1532, c_4])).
% 3.98/1.94  tff(c_1815, plain, (![A_1]: (k2_zfmisc_1(A_1, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1807, c_1807, c_1538])).
% 3.98/1.94  tff(c_1936, plain, (![A_224, B_225, C_226]: (k4_zfmisc_1(A_224, B_225, C_226, '#skF_4')='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1926, c_1815])).
% 3.98/1.94  tff(c_1810, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1807, c_1613])).
% 3.98/1.94  tff(c_1960, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1936, c_1810])).
% 3.98/1.94  tff(c_1961, plain, ('#skF_7'='#skF_3' | '#skF_7'='#skF_2'), inference(splitRight, [status(thm)], [c_1805])).
% 3.98/1.94  tff(c_1963, plain, ('#skF_7'='#skF_2'), inference(splitLeft, [status(thm)], [c_1961])).
% 3.98/1.94  tff(c_1971, plain, (![B_2]: (k2_zfmisc_1('#skF_2', B_2)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1963, c_1963, c_1539])).
% 3.98/1.94  tff(c_1536, plain, (![A_7, C_9]: (k3_zfmisc_1(A_7, '#skF_7', C_9)='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_1532, c_1532, c_14])).
% 3.98/1.94  tff(c_1969, plain, (![A_7, C_9]: (k3_zfmisc_1(A_7, '#skF_2', C_9)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1963, c_1963, c_1536])).
% 3.98/1.94  tff(c_2084, plain, (![A_241, B_242, C_243, D_244]: (k2_zfmisc_1(k3_zfmisc_1(A_241, B_242, C_243), D_244)=k4_zfmisc_1(A_241, B_242, C_243, D_244))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.98/1.94  tff(c_2100, plain, (![A_7, C_9, D_244]: (k4_zfmisc_1(A_7, '#skF_2', C_9, D_244)=k2_zfmisc_1('#skF_2', D_244))), inference(superposition, [status(thm), theory('equality')], [c_1969, c_2084])).
% 3.98/1.94  tff(c_2113, plain, (![A_7, C_9, D_244]: (k4_zfmisc_1(A_7, '#skF_2', C_9, D_244)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1971, c_2100])).
% 3.98/1.94  tff(c_1976, plain, (k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1963, c_1532])).
% 3.98/1.94  tff(c_2054, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_2' | k4_zfmisc_1('#skF_5', '#skF_6', '#skF_2', '#skF_8')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1976, c_1963, c_1976, c_20])).
% 3.98/1.94  tff(c_2055, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_2'), inference(splitLeft, [status(thm)], [c_2054])).
% 3.98/1.94  tff(c_2128, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2113, c_2055])).
% 3.98/1.94  tff(c_2130, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_2'), inference(splitRight, [status(thm)], [c_2054])).
% 3.98/1.94  tff(c_1967, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1963, c_1613])).
% 3.98/1.94  tff(c_2142, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2130, c_1967])).
% 3.98/1.94  tff(c_2143, plain, ('#skF_7'='#skF_3'), inference(splitRight, [status(thm)], [c_1961])).
% 3.98/1.94  tff(c_2152, plain, (![B_2]: (k2_zfmisc_1('#skF_3', B_2)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2143, c_2143, c_1539])).
% 3.98/1.94  tff(c_1535, plain, (![A_7, B_8]: (k3_zfmisc_1(A_7, B_8, '#skF_7')='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_1532, c_1532, c_12])).
% 3.98/1.94  tff(c_2149, plain, (![A_7, B_8]: (k3_zfmisc_1(A_7, B_8, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2143, c_2143, c_1535])).
% 3.98/1.94  tff(c_2265, plain, (![A_261, B_262, C_263, D_264]: (k2_zfmisc_1(k3_zfmisc_1(A_261, B_262, C_263), D_264)=k4_zfmisc_1(A_261, B_262, C_263, D_264))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.98/1.94  tff(c_2284, plain, (![A_7, B_8, D_264]: (k4_zfmisc_1(A_7, B_8, '#skF_3', D_264)=k2_zfmisc_1('#skF_3', D_264))), inference(superposition, [status(thm), theory('equality')], [c_2149, c_2265])).
% 3.98/1.94  tff(c_2295, plain, (![A_7, B_8, D_264]: (k4_zfmisc_1(A_7, B_8, '#skF_3', D_264)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2152, c_2284])).
% 3.98/1.94  tff(c_2148, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2143, c_1613])).
% 3.98/1.94  tff(c_2324, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2295, c_2148])).
% 3.98/1.94  tff(c_2326, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_32])).
% 3.98/1.94  tff(c_30, plain, (k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.98/1.94  tff(c_2425, plain, ('#skF_6'='#skF_4' | '#skF_6'='#skF_3' | '#skF_6'='#skF_2' | '#skF_6'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2326, c_2326, c_2326, c_2326, c_2326, c_30])).
% 3.98/1.94  tff(c_2426, plain, ('#skF_6'='#skF_1'), inference(splitLeft, [status(thm)], [c_2425])).
% 3.98/1.94  tff(c_2325, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_32])).
% 3.98/1.94  tff(c_2406, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_2326, c_2325])).
% 3.98/1.94  tff(c_2429, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2426, c_2406])).
% 3.98/1.94  tff(c_2332, plain, (![B_2]: (k2_zfmisc_1('#skF_6', B_2)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2326, c_2326, c_6])).
% 3.98/1.94  tff(c_2434, plain, (![B_2]: (k2_zfmisc_1('#skF_1', B_2)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2426, c_2426, c_2332])).
% 3.98/1.94  tff(c_2330, plain, (![B_8, C_9]: (k3_zfmisc_1('#skF_6', B_8, C_9)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2326, c_2326, c_16])).
% 3.98/1.94  tff(c_2432, plain, (![B_8, C_9]: (k3_zfmisc_1('#skF_1', B_8, C_9)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2426, c_2426, c_2330])).
% 3.98/1.94  tff(c_2544, plain, (![A_294, B_295, C_296, D_297]: (k2_zfmisc_1(k3_zfmisc_1(A_294, B_295, C_296), D_297)=k4_zfmisc_1(A_294, B_295, C_296, D_297))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.98/1.94  tff(c_2560, plain, (![B_8, C_9, D_297]: (k4_zfmisc_1('#skF_1', B_8, C_9, D_297)=k2_zfmisc_1('#skF_1', D_297))), inference(superposition, [status(thm), theory('equality')], [c_2432, c_2544])).
% 3.98/1.94  tff(c_2573, plain, (![B_8, C_9, D_297]: (k4_zfmisc_1('#skF_1', B_8, C_9, D_297)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2434, c_2560])).
% 3.98/1.94  tff(c_2437, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2426, c_2326])).
% 3.98/1.94  tff(c_2446, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_1' | k4_zfmisc_1('#skF_5', '#skF_1', '#skF_7', '#skF_8')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2437, c_2426, c_2437, c_20])).
% 3.98/1.94  tff(c_2447, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_1'), inference(splitLeft, [status(thm)], [c_2446])).
% 3.98/1.94  tff(c_2624, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2573, c_2447])).
% 3.98/1.94  tff(c_2626, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_1'), inference(splitRight, [status(thm)], [c_2446])).
% 3.98/1.94  tff(c_2699, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2429, c_2626])).
% 3.98/1.94  tff(c_2700, plain, ('#skF_6'='#skF_2' | '#skF_6'='#skF_3' | '#skF_6'='#skF_4'), inference(splitRight, [status(thm)], [c_2425])).
% 3.98/1.94  tff(c_2702, plain, ('#skF_6'='#skF_4'), inference(splitLeft, [status(thm)], [c_2700])).
% 3.98/1.94  tff(c_2331, plain, (![A_1]: (k2_zfmisc_1(A_1, '#skF_6')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2326, c_2326, c_4])).
% 3.98/1.94  tff(c_2711, plain, (![A_1]: (k2_zfmisc_1(A_1, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2702, c_2702, c_2331])).
% 3.98/1.94  tff(c_2831, plain, (![A_328, B_329, C_330]: (k4_zfmisc_1(A_328, B_329, C_330, '#skF_4')='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2821, c_2711])).
% 3.98/1.94  tff(c_2707, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2702, c_2406])).
% 3.98/1.94  tff(c_2855, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2831, c_2707])).
% 3.98/1.94  tff(c_2856, plain, ('#skF_6'='#skF_3' | '#skF_6'='#skF_2'), inference(splitRight, [status(thm)], [c_2700])).
% 3.98/1.94  tff(c_2858, plain, ('#skF_6'='#skF_2'), inference(splitLeft, [status(thm)], [c_2856])).
% 3.98/1.94  tff(c_2869, plain, (![B_2]: (k2_zfmisc_1('#skF_2', B_2)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2858, c_2858, c_2332])).
% 3.98/1.94  tff(c_2329, plain, (![A_7, C_9]: (k3_zfmisc_1(A_7, '#skF_6', C_9)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2326, c_2326, c_14])).
% 3.98/1.94  tff(c_2866, plain, (![A_7, C_9]: (k3_zfmisc_1(A_7, '#skF_2', C_9)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2858, c_2858, c_2329])).
% 3.98/1.94  tff(c_2978, plain, (![A_345, B_346, C_347, D_348]: (k2_zfmisc_1(k3_zfmisc_1(A_345, B_346, C_347), D_348)=k4_zfmisc_1(A_345, B_346, C_347, D_348))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.98/1.94  tff(c_2994, plain, (![A_7, C_9, D_348]: (k4_zfmisc_1(A_7, '#skF_2', C_9, D_348)=k2_zfmisc_1('#skF_2', D_348))), inference(superposition, [status(thm), theory('equality')], [c_2866, c_2978])).
% 3.98/1.94  tff(c_3007, plain, (![A_7, C_9, D_348]: (k4_zfmisc_1(A_7, '#skF_2', C_9, D_348)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2869, c_2994])).
% 3.98/1.94  tff(c_2864, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2858, c_2406])).
% 3.98/1.94  tff(c_3074, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3007, c_2864])).
% 3.98/1.94  tff(c_3075, plain, ('#skF_6'='#skF_3'), inference(splitRight, [status(thm)], [c_2856])).
% 3.98/1.94  tff(c_3086, plain, (![B_2]: (k2_zfmisc_1('#skF_3', B_2)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3075, c_3075, c_2332])).
% 3.98/1.94  tff(c_2328, plain, (![A_7, B_8]: (k3_zfmisc_1(A_7, B_8, '#skF_6')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2326, c_2326, c_12])).
% 3.98/1.94  tff(c_3082, plain, (![A_7, B_8]: (k3_zfmisc_1(A_7, B_8, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3075, c_3075, c_2328])).
% 3.98/1.94  tff(c_3198, plain, (![A_375, B_376, C_377, D_378]: (k2_zfmisc_1(k3_zfmisc_1(A_375, B_376, C_377), D_378)=k4_zfmisc_1(A_375, B_376, C_377, D_378))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.98/1.94  tff(c_3214, plain, (![A_7, B_8, D_378]: (k4_zfmisc_1(A_7, B_8, '#skF_3', D_378)=k2_zfmisc_1('#skF_3', D_378))), inference(superposition, [status(thm), theory('equality')], [c_3082, c_3198])).
% 3.98/1.94  tff(c_3227, plain, (![A_7, B_8, D_378]: (k4_zfmisc_1(A_7, B_8, '#skF_3', D_378)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3086, c_3214])).
% 3.98/1.94  tff(c_3081, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_3075, c_2406])).
% 3.98/1.94  tff(c_3255, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3227, c_3081])).
% 3.98/1.94  tff(c_3257, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_36])).
% 3.98/1.94  tff(c_34, plain, (k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.98/1.94  tff(c_3354, plain, ('#skF_5'='#skF_4' | '#skF_5'='#skF_3' | '#skF_5'='#skF_2' | '#skF_5'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3257, c_3257, c_3257, c_3257, c_3257, c_34])).
% 3.98/1.94  tff(c_3355, plain, ('#skF_5'='#skF_1'), inference(splitLeft, [status(thm)], [c_3354])).
% 3.98/1.94  tff(c_3262, plain, (![B_2]: (k2_zfmisc_1('#skF_5', B_2)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_3257, c_3257, c_6])).
% 3.98/1.94  tff(c_3362, plain, (![B_2]: (k2_zfmisc_1('#skF_1', B_2)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3355, c_3355, c_3262])).
% 3.98/1.94  tff(c_3260, plain, (![B_8, C_9]: (k3_zfmisc_1('#skF_5', B_8, C_9)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_3257, c_3257, c_16])).
% 3.98/1.94  tff(c_3359, plain, (![B_8, C_9]: (k3_zfmisc_1('#skF_1', B_8, C_9)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3355, c_3355, c_3260])).
% 3.98/1.94  tff(c_3454, plain, (![A_405, B_406, C_407, D_408]: (k2_zfmisc_1(k3_zfmisc_1(A_405, B_406, C_407), D_408)=k4_zfmisc_1(A_405, B_406, C_407, D_408))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.98/1.94  tff(c_3473, plain, (![B_8, C_9, D_408]: (k4_zfmisc_1('#skF_1', B_8, C_9, D_408)=k2_zfmisc_1('#skF_1', D_408))), inference(superposition, [status(thm), theory('equality')], [c_3359, c_3454])).
% 3.98/1.94  tff(c_3484, plain, (![B_8, C_9, D_408]: (k4_zfmisc_1('#skF_1', B_8, C_9, D_408)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3362, c_3473])).
% 3.98/1.94  tff(c_3256, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_36])).
% 3.98/1.94  tff(c_3336, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_3257, c_3256])).
% 3.98/1.94  tff(c_3358, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3355, c_3336])).
% 3.98/1.94  tff(c_3512, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3484, c_3358])).
% 3.98/1.94  tff(c_3513, plain, ('#skF_5'='#skF_2' | '#skF_5'='#skF_3' | '#skF_5'='#skF_4'), inference(splitRight, [status(thm)], [c_3354])).
% 3.98/1.94  tff(c_3515, plain, ('#skF_5'='#skF_4'), inference(splitLeft, [status(thm)], [c_3513])).
% 3.98/1.94  tff(c_3261, plain, (![A_1]: (k2_zfmisc_1(A_1, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_3257, c_3257, c_4])).
% 3.98/1.94  tff(c_3525, plain, (![A_1]: (k2_zfmisc_1(A_1, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3515, c_3515, c_3261])).
% 3.98/1.94  tff(c_3644, plain, (![A_428, B_429, C_430]: (k4_zfmisc_1(A_428, B_429, C_430, '#skF_4')='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3634, c_3525])).
% 3.98/1.94  tff(c_3519, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3515, c_3336])).
% 3.98/1.94  tff(c_3669, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3644, c_3519])).
% 3.98/1.94  tff(c_3670, plain, ('#skF_5'='#skF_3' | '#skF_5'='#skF_2'), inference(splitRight, [status(thm)], [c_3513])).
% 3.98/1.94  tff(c_3672, plain, ('#skF_5'='#skF_2'), inference(splitLeft, [status(thm)], [c_3670])).
% 3.98/1.94  tff(c_3681, plain, (![B_2]: (k2_zfmisc_1('#skF_2', B_2)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3672, c_3672, c_3262])).
% 3.98/1.94  tff(c_3259, plain, (![A_7, C_9]: (k3_zfmisc_1(A_7, '#skF_5', C_9)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_3257, c_3257, c_14])).
% 3.98/1.94  tff(c_3679, plain, (![A_7, C_9]: (k3_zfmisc_1(A_7, '#skF_2', C_9)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3672, c_3672, c_3259])).
% 3.98/1.94  tff(c_3793, plain, (![A_445, B_446, C_447, D_448]: (k2_zfmisc_1(k3_zfmisc_1(A_445, B_446, C_447), D_448)=k4_zfmisc_1(A_445, B_446, C_447, D_448))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.98/1.94  tff(c_3815, plain, (![A_7, C_9, D_448]: (k4_zfmisc_1(A_7, '#skF_2', C_9, D_448)=k2_zfmisc_1('#skF_2', D_448))), inference(superposition, [status(thm), theory('equality')], [c_3679, c_3793])).
% 3.98/1.94  tff(c_3824, plain, (![A_7, C_9, D_448]: (k4_zfmisc_1(A_7, '#skF_2', C_9, D_448)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3681, c_3815])).
% 3.98/1.94  tff(c_3677, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_3672, c_3336])).
% 3.98/1.94  tff(c_3875, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3824, c_3677])).
% 3.98/1.94  tff(c_3876, plain, ('#skF_5'='#skF_3'), inference(splitRight, [status(thm)], [c_3670])).
% 3.98/1.94  tff(c_3886, plain, (![B_2]: (k2_zfmisc_1('#skF_3', B_2)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3876, c_3876, c_3262])).
% 3.98/1.94  tff(c_3258, plain, (![A_7, B_8]: (k3_zfmisc_1(A_7, B_8, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_3257, c_3257, c_12])).
% 3.98/1.94  tff(c_3885, plain, (![A_7, B_8]: (k3_zfmisc_1(A_7, B_8, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3876, c_3876, c_3258])).
% 3.98/1.94  tff(c_3981, plain, (![A_468, B_469, C_470, D_471]: (k2_zfmisc_1(k3_zfmisc_1(A_468, B_469, C_470), D_471)=k4_zfmisc_1(A_468, B_469, C_470, D_471))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.98/1.94  tff(c_4003, plain, (![A_7, B_8, D_471]: (k4_zfmisc_1(A_7, B_8, '#skF_3', D_471)=k2_zfmisc_1('#skF_3', D_471))), inference(superposition, [status(thm), theory('equality')], [c_3885, c_3981])).
% 3.98/1.94  tff(c_4012, plain, (![A_7, B_8, D_471]: (k4_zfmisc_1(A_7, B_8, '#skF_3', D_471)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3886, c_4003])).
% 3.98/1.94  tff(c_3882, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_3876, c_3336])).
% 3.98/1.94  tff(c_4056, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4012, c_3882])).
% 3.98/1.94  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.98/1.94  
% 3.98/1.94  Inference rules
% 3.98/1.94  ----------------------
% 3.98/1.94  #Ref     : 0
% 3.98/1.94  #Sup     : 923
% 3.98/1.94  #Fact    : 0
% 3.98/1.94  #Define  : 0
% 3.98/1.94  #Split   : 32
% 3.98/1.94  #Chain   : 0
% 3.98/1.94  #Close   : 0
% 3.98/1.94  
% 3.98/1.94  Ordering : KBO
% 3.98/1.94  
% 3.98/1.94  Simplification rules
% 3.98/1.94  ----------------------
% 3.98/1.94  #Subsume      : 39
% 3.98/1.94  #Demod        : 864
% 3.98/1.94  #Tautology    : 812
% 3.98/1.94  #SimpNegUnit  : 24
% 3.98/1.94  #BackRed      : 280
% 3.98/1.94  
% 3.98/1.94  #Partial instantiations: 0
% 3.98/1.94  #Strategies tried      : 1
% 3.98/1.94  
% 3.98/1.94  Timing (in seconds)
% 3.98/1.94  ----------------------
% 3.98/1.95  Preprocessing        : 0.36
% 3.98/1.95  Parsing              : 0.20
% 3.98/1.95  CNF conversion       : 0.02
% 3.98/1.95  Main loop            : 0.72
% 3.98/1.95  Inferencing          : 0.26
% 3.98/1.95  Reduction            : 0.23
% 3.98/1.95  Demodulation         : 0.16
% 3.98/1.95  BG Simplification    : 0.03
% 3.98/1.95  Subsumption          : 0.10
% 3.98/1.95  Abstraction          : 0.04
% 3.98/1.95  MUC search           : 0.00
% 3.98/1.95  Cooper               : 0.00
% 3.98/1.95  Total                : 1.16
% 3.98/1.95  Index Insertion      : 0.00
% 3.98/1.95  Index Deletion       : 0.00
% 3.98/1.95  Index Matching       : 0.00
% 3.98/1.95  BG Taut test         : 0.00
%------------------------------------------------------------------------------
