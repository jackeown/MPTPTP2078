%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:28 EST 2020

% Result     : Theorem 2.78s
% Output     : CNFRefutation 2.87s
% Verified   : 
% Statistics : Number of formulae       :  154 (1145 expanded)
%              Number of leaves         :   15 ( 337 expanded)
%              Depth                    :    9
%              Number of atoms          :  187 (2597 expanded)
%              Number of equality atoms :  171 (2581 expanded)
%              Maximal formula depth    :    9 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_33,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_46,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( A != k1_xboole_0
          & B != k1_xboole_0
          & C != k1_xboole_0 )
      <=> k3_zfmisc_1(A,B,C) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_mcart_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(c_1178,plain,(
    ! [A_108,B_109,C_110] : k2_zfmisc_1(k2_zfmisc_1(A_108,B_109),C_110) = k3_zfmisc_1(A_108,B_109,C_110) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_745,plain,(
    ! [A_69,B_70,C_71] : k2_zfmisc_1(k2_zfmisc_1(A_69,B_70),C_71) = k3_zfmisc_1(A_69,B_70,C_71) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_24,plain,
    ( k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != k1_xboole_0
    | k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_47,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_20,plain,
    ( k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != k1_xboole_0
    | k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_49,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_20])).

tff(c_16,plain,
    ( k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != k1_xboole_0
    | k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_48,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_16])).

tff(c_10,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1'
    | k3_zfmisc_1('#skF_4','#skF_5','#skF_6') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_142,plain,(
    k3_zfmisc_1('#skF_4','#skF_5','#skF_6') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_10])).

tff(c_61,plain,(
    ! [A_10,B_11,C_12] : k2_zfmisc_1(k2_zfmisc_1(A_10,B_11),C_12) = k3_zfmisc_1(A_10,B_11,C_12) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( k1_xboole_0 = B_2
      | k1_xboole_0 = A_1
      | k2_zfmisc_1(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_147,plain,(
    ! [C_19,A_20,B_21] :
      ( k1_xboole_0 = C_19
      | k2_zfmisc_1(A_20,B_21) = k1_xboole_0
      | k3_zfmisc_1(A_20,B_21,C_19) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_2])).

tff(c_150,plain,
    ( k1_xboole_0 = '#skF_6'
    | k2_zfmisc_1('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_142,c_147])).

tff(c_162,plain,(
    k2_zfmisc_1('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_150])).

tff(c_175,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_162,c_2])).

tff(c_182,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_47,c_49,c_175])).

tff(c_183,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_10])).

tff(c_185,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_183])).

tff(c_4,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_201,plain,(
    ! [A_22] : k2_zfmisc_1(A_22,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_185,c_4])).

tff(c_8,plain,(
    ! [A_3,B_4,C_5] : k2_zfmisc_1(k2_zfmisc_1(A_3,B_4),C_5) = k3_zfmisc_1(A_3,B_4,C_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_210,plain,(
    ! [A_3,B_4] : k3_zfmisc_1(A_3,B_4,'#skF_3') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_201,c_8])).

tff(c_12,plain,
    ( k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != k1_xboole_0
    | k3_zfmisc_1('#skF_4','#skF_5','#skF_6') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_103,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_12])).

tff(c_189,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_103])).

tff(c_262,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_210,c_189])).

tff(c_263,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_183])).

tff(c_265,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_263])).

tff(c_6,plain,(
    ! [B_2] : k2_zfmisc_1(k1_xboole_0,B_2) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_90,plain,(
    ! [B_2,C_12] : k3_zfmisc_1(k1_xboole_0,B_2,C_12) = k2_zfmisc_1(k1_xboole_0,C_12) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_61])).

tff(c_94,plain,(
    ! [B_2,C_12] : k3_zfmisc_1(k1_xboole_0,B_2,C_12) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_90])).

tff(c_268,plain,(
    ! [B_2,C_12] : k3_zfmisc_1('#skF_1',B_2,C_12) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_265,c_265,c_94])).

tff(c_270,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_265,c_103])).

tff(c_347,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_268,c_270])).

tff(c_348,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_263])).

tff(c_362,plain,(
    ! [B_2] : k2_zfmisc_1('#skF_2',B_2) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_348,c_348,c_6])).

tff(c_378,plain,(
    ! [A_35] : k2_zfmisc_1(A_35,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_348,c_348,c_4])).

tff(c_386,plain,(
    ! [A_35,C_5] : k3_zfmisc_1(A_35,'#skF_2',C_5) = k2_zfmisc_1('#skF_2',C_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_378,c_8])).

tff(c_402,plain,(
    ! [A_35,C_5] : k3_zfmisc_1(A_35,'#skF_2',C_5) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_362,c_386])).

tff(c_355,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_348,c_103])).

tff(c_456,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_402,c_355])).

tff(c_457,plain,(
    k3_zfmisc_1('#skF_4','#skF_5','#skF_6') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_12])).

tff(c_506,plain,(
    ! [C_49,A_50,B_51] :
      ( k1_xboole_0 = C_49
      | k2_zfmisc_1(A_50,B_51) = k1_xboole_0
      | k3_zfmisc_1(A_50,B_51,C_49) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_2])).

tff(c_518,plain,
    ( k1_xboole_0 = '#skF_6'
    | k2_zfmisc_1('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_457,c_506])).

tff(c_529,plain,(
    k2_zfmisc_1('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_518])).

tff(c_538,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_529,c_2])).

tff(c_545,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_47,c_49,c_538])).

tff(c_547,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_18,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_595,plain,
    ( '#skF_5' = '#skF_3'
    | '#skF_5' = '#skF_2'
    | '#skF_5' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_547,c_547,c_547,c_547,c_18])).

tff(c_596,plain,(
    '#skF_5' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_595])).

tff(c_551,plain,(
    ! [B_2] : k2_zfmisc_1('#skF_5',B_2) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_547,c_547,c_6])).

tff(c_601,plain,(
    ! [B_2] : k2_zfmisc_1('#skF_1',B_2) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_596,c_596,c_551])).

tff(c_646,plain,(
    ! [A_60,B_61,C_62] : k2_zfmisc_1(k2_zfmisc_1(A_60,B_61),C_62) = k3_zfmisc_1(A_60,B_61,C_62) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_675,plain,(
    ! [B_2,C_62] : k3_zfmisc_1('#skF_1',B_2,C_62) = k2_zfmisc_1('#skF_1',C_62) ),
    inference(superposition,[status(thm),theory(equality)],[c_601,c_646])).

tff(c_679,plain,(
    ! [B_2,C_62] : k3_zfmisc_1('#skF_1',B_2,C_62) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_601,c_675])).

tff(c_546,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_580,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_547,c_546])).

tff(c_599,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_596,c_580])).

tff(c_690,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_679,c_599])).

tff(c_691,plain,
    ( '#skF_5' = '#skF_2'
    | '#skF_5' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_595])).

tff(c_693,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_691])).

tff(c_550,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_547,c_547,c_4])).

tff(c_697,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_693,c_693,c_550])).

tff(c_758,plain,(
    ! [A_69,B_70] : k3_zfmisc_1(A_69,B_70,'#skF_3') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_745,c_697])).

tff(c_701,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_693,c_547])).

tff(c_710,plain,
    ( k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != '#skF_3'
    | k3_zfmisc_1('#skF_4','#skF_3','#skF_6') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_701,c_693,c_701,c_12])).

tff(c_711,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_710])).

tff(c_781,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_758,c_711])).

tff(c_783,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_710])).

tff(c_696,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_693,c_580])).

tff(c_813,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_783,c_696])).

tff(c_814,plain,(
    '#skF_5' = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_691])).

tff(c_820,plain,(
    ! [B_2] : k2_zfmisc_1('#skF_2',B_2) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_814,c_814,c_551])).

tff(c_819,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_814,c_814,c_550])).

tff(c_868,plain,(
    ! [A_78,B_79,C_80] : k2_zfmisc_1(k2_zfmisc_1(A_78,B_79),C_80) = k3_zfmisc_1(A_78,B_79,C_80) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_893,plain,(
    ! [A_1,C_80] : k3_zfmisc_1(A_1,'#skF_2',C_80) = k2_zfmisc_1('#skF_2',C_80) ),
    inference(superposition,[status(thm),theory(equality)],[c_819,c_868])).

tff(c_901,plain,(
    ! [A_1,C_80] : k3_zfmisc_1(A_1,'#skF_2',C_80) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_820,c_893])).

tff(c_823,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_814,c_547])).

tff(c_840,plain,
    ( k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | k3_zfmisc_1('#skF_4','#skF_2','#skF_6') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_823,c_814,c_823,c_12])).

tff(c_841,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_840])).

tff(c_940,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_901,c_841])).

tff(c_942,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_840])).

tff(c_818,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_814,c_580])).

tff(c_963,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_942,c_818])).

tff(c_965,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_16])).

tff(c_14,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1011,plain,
    ( '#skF_6' = '#skF_3'
    | '#skF_6' = '#skF_2'
    | '#skF_6' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_965,c_965,c_965,c_965,c_14])).

tff(c_1012,plain,(
    '#skF_6' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_1011])).

tff(c_968,plain,(
    ! [B_2] : k2_zfmisc_1('#skF_6',B_2) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_965,c_965,c_6])).

tff(c_1016,plain,(
    ! [B_2] : k2_zfmisc_1('#skF_1',B_2) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1012,c_1012,c_968])).

tff(c_1061,plain,(
    ! [A_97,B_98,C_99] : k2_zfmisc_1(k2_zfmisc_1(A_97,B_98),C_99) = k3_zfmisc_1(A_97,B_98,C_99) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1083,plain,(
    ! [B_2,C_99] : k3_zfmisc_1('#skF_1',B_2,C_99) = k2_zfmisc_1('#skF_1',C_99) ),
    inference(superposition,[status(thm),theory(equality)],[c_1016,c_1061])).

tff(c_1093,plain,(
    ! [B_2,C_99] : k3_zfmisc_1('#skF_1',B_2,C_99) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1016,c_1083])).

tff(c_964,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_16])).

tff(c_995,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_965,c_964])).

tff(c_1014,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1012,c_995])).

tff(c_1121,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1093,c_1014])).

tff(c_1122,plain,
    ( '#skF_6' = '#skF_2'
    | '#skF_6' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1011])).

tff(c_1124,plain,(
    '#skF_6' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_1122])).

tff(c_967,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_965,c_965,c_4])).

tff(c_1131,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1124,c_1124,c_967])).

tff(c_1191,plain,(
    ! [A_108,B_109] : k3_zfmisc_1(A_108,B_109,'#skF_3') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_1178,c_1131])).

tff(c_1130,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1124,c_995])).

tff(c_1214,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1191,c_1130])).

tff(c_1215,plain,(
    '#skF_6' = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_1122])).

tff(c_1221,plain,(
    ! [B_2] : k2_zfmisc_1('#skF_2',B_2) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1215,c_1215,c_968])).

tff(c_1220,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1215,c_1215,c_967])).

tff(c_1268,plain,(
    ! [A_115,B_116,C_117] : k2_zfmisc_1(k2_zfmisc_1(A_115,B_116),C_117) = k3_zfmisc_1(A_115,B_116,C_117) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1290,plain,(
    ! [A_1,C_117] : k3_zfmisc_1(A_1,'#skF_2',C_117) = k2_zfmisc_1('#skF_2',C_117) ),
    inference(superposition,[status(thm),theory(equality)],[c_1220,c_1268])).

tff(c_1300,plain,(
    ! [A_1,C_117] : k3_zfmisc_1(A_1,'#skF_2',C_117) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1221,c_1290])).

tff(c_1219,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1215,c_995])).

tff(c_1328,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1300,c_1219])).

tff(c_1330,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_1332,plain,(
    ! [B_2] : k2_zfmisc_1('#skF_4',B_2) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1330,c_1330,c_6])).

tff(c_1331,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1330,c_1330,c_4])).

tff(c_1515,plain,(
    ! [A_138,B_139,C_140] : k2_zfmisc_1(k2_zfmisc_1(A_138,B_139),C_140) = k3_zfmisc_1(A_138,B_139,C_140) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1537,plain,(
    ! [A_1,C_140] : k3_zfmisc_1(A_1,'#skF_4',C_140) = k2_zfmisc_1('#skF_4',C_140) ),
    inference(superposition,[status(thm),theory(equality)],[c_1331,c_1515])).

tff(c_1547,plain,(
    ! [A_1,C_140] : k3_zfmisc_1(A_1,'#skF_4',C_140) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1332,c_1537])).

tff(c_1454,plain,(
    ! [A_133,B_134,C_135] : k2_zfmisc_1(k2_zfmisc_1(A_133,B_134),C_135) = k3_zfmisc_1(A_133,B_134,C_135) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1467,plain,(
    ! [A_133,B_134] : k3_zfmisc_1(A_133,B_134,'#skF_4') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_1454,c_1331])).

tff(c_1385,plain,(
    ! [A_126,B_127,C_128] : k2_zfmisc_1(k2_zfmisc_1(A_126,B_127),C_128) = k3_zfmisc_1(A_126,B_127,C_128) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1414,plain,(
    ! [B_2,C_128] : k3_zfmisc_1('#skF_4',B_2,C_128) = k2_zfmisc_1('#skF_4',C_128) ),
    inference(superposition,[status(thm),theory(equality)],[c_1332,c_1385])).

tff(c_1418,plain,(
    ! [B_2,C_128] : k3_zfmisc_1('#skF_4',B_2,C_128) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1332,c_1414])).

tff(c_22,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1364,plain,
    ( '#skF_3' = '#skF_4'
    | '#skF_2' = '#skF_4'
    | '#skF_1' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1330,c_1330,c_1330,c_1330,c_22])).

tff(c_1365,plain,(
    '#skF_1' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_1364])).

tff(c_1329,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_1361,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1330,c_1329])).

tff(c_1366,plain,(
    k3_zfmisc_1('#skF_4','#skF_2','#skF_3') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1365,c_1361])).

tff(c_1429,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1418,c_1366])).

tff(c_1430,plain,
    ( '#skF_2' = '#skF_4'
    | '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1364])).

tff(c_1432,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_1430])).

tff(c_1433,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1432,c_1361])).

tff(c_1490,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1467,c_1433])).

tff(c_1491,plain,(
    '#skF_2' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1430])).

tff(c_1493,plain,(
    k3_zfmisc_1('#skF_1','#skF_4','#skF_3') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1491,c_1361])).

tff(c_1576,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1547,c_1493])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:43:27 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.78/1.47  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.87/1.49  
% 2.87/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.87/1.49  %$ k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.87/1.49  
% 2.87/1.49  %Foreground sorts:
% 2.87/1.49  
% 2.87/1.49  
% 2.87/1.49  %Background operators:
% 2.87/1.49  
% 2.87/1.49  
% 2.87/1.49  %Foreground operators:
% 2.87/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.87/1.49  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.87/1.49  tff('#skF_5', type, '#skF_5': $i).
% 2.87/1.49  tff('#skF_6', type, '#skF_6': $i).
% 2.87/1.49  tff('#skF_2', type, '#skF_2': $i).
% 2.87/1.49  tff('#skF_3', type, '#skF_3': $i).
% 2.87/1.49  tff('#skF_1', type, '#skF_1': $i).
% 2.87/1.49  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 2.87/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.87/1.49  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.87/1.49  tff('#skF_4', type, '#skF_4': $i).
% 2.87/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.87/1.49  
% 2.87/1.51  tff(f_33, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 2.87/1.51  tff(f_46, negated_conjecture, ~(![A, B, C]: (((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) <=> ~(k3_zfmisc_1(A, B, C) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_mcart_1)).
% 2.87/1.51  tff(f_31, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.87/1.51  tff(c_1178, plain, (![A_108, B_109, C_110]: (k2_zfmisc_1(k2_zfmisc_1(A_108, B_109), C_110)=k3_zfmisc_1(A_108, B_109, C_110))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.87/1.51  tff(c_745, plain, (![A_69, B_70, C_71]: (k2_zfmisc_1(k2_zfmisc_1(A_69, B_70), C_71)=k3_zfmisc_1(A_69, B_70, C_71))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.87/1.51  tff(c_24, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')!=k1_xboole_0 | k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.87/1.51  tff(c_47, plain, (k1_xboole_0!='#skF_4'), inference(splitLeft, [status(thm)], [c_24])).
% 2.87/1.51  tff(c_20, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')!=k1_xboole_0 | k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.87/1.51  tff(c_49, plain, (k1_xboole_0!='#skF_5'), inference(splitLeft, [status(thm)], [c_20])).
% 2.87/1.51  tff(c_16, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')!=k1_xboole_0 | k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.87/1.51  tff(c_48, plain, (k1_xboole_0!='#skF_6'), inference(splitLeft, [status(thm)], [c_16])).
% 2.87/1.51  tff(c_10, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1' | k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.87/1.51  tff(c_142, plain, (k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_10])).
% 2.87/1.51  tff(c_61, plain, (![A_10, B_11, C_12]: (k2_zfmisc_1(k2_zfmisc_1(A_10, B_11), C_12)=k3_zfmisc_1(A_10, B_11, C_12))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.87/1.51  tff(c_2, plain, (![B_2, A_1]: (k1_xboole_0=B_2 | k1_xboole_0=A_1 | k2_zfmisc_1(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.87/1.51  tff(c_147, plain, (![C_19, A_20, B_21]: (k1_xboole_0=C_19 | k2_zfmisc_1(A_20, B_21)=k1_xboole_0 | k3_zfmisc_1(A_20, B_21, C_19)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_61, c_2])).
% 2.87/1.51  tff(c_150, plain, (k1_xboole_0='#skF_6' | k2_zfmisc_1('#skF_4', '#skF_5')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_142, c_147])).
% 2.87/1.51  tff(c_162, plain, (k2_zfmisc_1('#skF_4', '#skF_5')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_48, c_150])).
% 2.87/1.51  tff(c_175, plain, (k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_162, c_2])).
% 2.87/1.51  tff(c_182, plain, $false, inference(negUnitSimplification, [status(thm)], [c_47, c_49, c_175])).
% 2.87/1.51  tff(c_183, plain, (k1_xboole_0='#skF_1' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_10])).
% 2.87/1.51  tff(c_185, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_183])).
% 2.87/1.51  tff(c_4, plain, (![A_1]: (k2_zfmisc_1(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.87/1.51  tff(c_201, plain, (![A_22]: (k2_zfmisc_1(A_22, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_185, c_185, c_4])).
% 2.87/1.51  tff(c_8, plain, (![A_3, B_4, C_5]: (k2_zfmisc_1(k2_zfmisc_1(A_3, B_4), C_5)=k3_zfmisc_1(A_3, B_4, C_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.87/1.51  tff(c_210, plain, (![A_3, B_4]: (k3_zfmisc_1(A_3, B_4, '#skF_3')='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_201, c_8])).
% 2.87/1.51  tff(c_12, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')!=k1_xboole_0 | k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.87/1.51  tff(c_103, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_12])).
% 2.87/1.51  tff(c_189, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_185, c_103])).
% 2.87/1.51  tff(c_262, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_210, c_189])).
% 2.87/1.51  tff(c_263, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_183])).
% 2.87/1.51  tff(c_265, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_263])).
% 2.87/1.51  tff(c_6, plain, (![B_2]: (k2_zfmisc_1(k1_xboole_0, B_2)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.87/1.51  tff(c_90, plain, (![B_2, C_12]: (k3_zfmisc_1(k1_xboole_0, B_2, C_12)=k2_zfmisc_1(k1_xboole_0, C_12))), inference(superposition, [status(thm), theory('equality')], [c_6, c_61])).
% 2.87/1.51  tff(c_94, plain, (![B_2, C_12]: (k3_zfmisc_1(k1_xboole_0, B_2, C_12)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_90])).
% 2.87/1.51  tff(c_268, plain, (![B_2, C_12]: (k3_zfmisc_1('#skF_1', B_2, C_12)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_265, c_265, c_94])).
% 2.87/1.51  tff(c_270, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_265, c_103])).
% 2.87/1.51  tff(c_347, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_268, c_270])).
% 2.87/1.51  tff(c_348, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_263])).
% 2.87/1.51  tff(c_362, plain, (![B_2]: (k2_zfmisc_1('#skF_2', B_2)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_348, c_348, c_6])).
% 2.87/1.51  tff(c_378, plain, (![A_35]: (k2_zfmisc_1(A_35, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_348, c_348, c_4])).
% 2.87/1.51  tff(c_386, plain, (![A_35, C_5]: (k3_zfmisc_1(A_35, '#skF_2', C_5)=k2_zfmisc_1('#skF_2', C_5))), inference(superposition, [status(thm), theory('equality')], [c_378, c_8])).
% 2.87/1.51  tff(c_402, plain, (![A_35, C_5]: (k3_zfmisc_1(A_35, '#skF_2', C_5)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_362, c_386])).
% 2.87/1.51  tff(c_355, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_348, c_103])).
% 2.87/1.51  tff(c_456, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_402, c_355])).
% 2.87/1.51  tff(c_457, plain, (k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')=k1_xboole_0), inference(splitRight, [status(thm)], [c_12])).
% 2.87/1.51  tff(c_506, plain, (![C_49, A_50, B_51]: (k1_xboole_0=C_49 | k2_zfmisc_1(A_50, B_51)=k1_xboole_0 | k3_zfmisc_1(A_50, B_51, C_49)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_61, c_2])).
% 2.87/1.51  tff(c_518, plain, (k1_xboole_0='#skF_6' | k2_zfmisc_1('#skF_4', '#skF_5')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_457, c_506])).
% 2.87/1.51  tff(c_529, plain, (k2_zfmisc_1('#skF_4', '#skF_5')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_48, c_518])).
% 2.87/1.51  tff(c_538, plain, (k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_529, c_2])).
% 2.87/1.51  tff(c_545, plain, $false, inference(negUnitSimplification, [status(thm)], [c_47, c_49, c_538])).
% 2.87/1.51  tff(c_547, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_20])).
% 2.87/1.51  tff(c_18, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.87/1.51  tff(c_595, plain, ('#skF_5'='#skF_3' | '#skF_5'='#skF_2' | '#skF_5'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_547, c_547, c_547, c_547, c_18])).
% 2.87/1.51  tff(c_596, plain, ('#skF_5'='#skF_1'), inference(splitLeft, [status(thm)], [c_595])).
% 2.87/1.51  tff(c_551, plain, (![B_2]: (k2_zfmisc_1('#skF_5', B_2)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_547, c_547, c_6])).
% 2.87/1.51  tff(c_601, plain, (![B_2]: (k2_zfmisc_1('#skF_1', B_2)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_596, c_596, c_551])).
% 2.87/1.51  tff(c_646, plain, (![A_60, B_61, C_62]: (k2_zfmisc_1(k2_zfmisc_1(A_60, B_61), C_62)=k3_zfmisc_1(A_60, B_61, C_62))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.87/1.51  tff(c_675, plain, (![B_2, C_62]: (k3_zfmisc_1('#skF_1', B_2, C_62)=k2_zfmisc_1('#skF_1', C_62))), inference(superposition, [status(thm), theory('equality')], [c_601, c_646])).
% 2.87/1.51  tff(c_679, plain, (![B_2, C_62]: (k3_zfmisc_1('#skF_1', B_2, C_62)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_601, c_675])).
% 2.87/1.51  tff(c_546, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_20])).
% 2.87/1.51  tff(c_580, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_547, c_546])).
% 2.87/1.51  tff(c_599, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_596, c_580])).
% 2.87/1.51  tff(c_690, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_679, c_599])).
% 2.87/1.51  tff(c_691, plain, ('#skF_5'='#skF_2' | '#skF_5'='#skF_3'), inference(splitRight, [status(thm)], [c_595])).
% 2.87/1.51  tff(c_693, plain, ('#skF_5'='#skF_3'), inference(splitLeft, [status(thm)], [c_691])).
% 2.87/1.51  tff(c_550, plain, (![A_1]: (k2_zfmisc_1(A_1, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_547, c_547, c_4])).
% 2.87/1.51  tff(c_697, plain, (![A_1]: (k2_zfmisc_1(A_1, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_693, c_693, c_550])).
% 2.87/1.51  tff(c_758, plain, (![A_69, B_70]: (k3_zfmisc_1(A_69, B_70, '#skF_3')='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_745, c_697])).
% 2.87/1.51  tff(c_701, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_693, c_547])).
% 2.87/1.51  tff(c_710, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')!='#skF_3' | k3_zfmisc_1('#skF_4', '#skF_3', '#skF_6')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_701, c_693, c_701, c_12])).
% 2.87/1.51  tff(c_711, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')!='#skF_3'), inference(splitLeft, [status(thm)], [c_710])).
% 2.87/1.51  tff(c_781, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_758, c_711])).
% 2.87/1.51  tff(c_783, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_710])).
% 2.87/1.51  tff(c_696, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_693, c_580])).
% 2.87/1.51  tff(c_813, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_783, c_696])).
% 2.87/1.51  tff(c_814, plain, ('#skF_5'='#skF_2'), inference(splitRight, [status(thm)], [c_691])).
% 2.87/1.51  tff(c_820, plain, (![B_2]: (k2_zfmisc_1('#skF_2', B_2)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_814, c_814, c_551])).
% 2.87/1.51  tff(c_819, plain, (![A_1]: (k2_zfmisc_1(A_1, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_814, c_814, c_550])).
% 2.87/1.51  tff(c_868, plain, (![A_78, B_79, C_80]: (k2_zfmisc_1(k2_zfmisc_1(A_78, B_79), C_80)=k3_zfmisc_1(A_78, B_79, C_80))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.87/1.51  tff(c_893, plain, (![A_1, C_80]: (k3_zfmisc_1(A_1, '#skF_2', C_80)=k2_zfmisc_1('#skF_2', C_80))), inference(superposition, [status(thm), theory('equality')], [c_819, c_868])).
% 2.87/1.51  tff(c_901, plain, (![A_1, C_80]: (k3_zfmisc_1(A_1, '#skF_2', C_80)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_820, c_893])).
% 2.87/1.51  tff(c_823, plain, (k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_814, c_547])).
% 2.87/1.51  tff(c_840, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | k3_zfmisc_1('#skF_4', '#skF_2', '#skF_6')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_823, c_814, c_823, c_12])).
% 2.87/1.51  tff(c_841, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2'), inference(splitLeft, [status(thm)], [c_840])).
% 2.87/1.51  tff(c_940, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_901, c_841])).
% 2.87/1.51  tff(c_942, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(splitRight, [status(thm)], [c_840])).
% 2.87/1.51  tff(c_818, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_814, c_580])).
% 2.87/1.51  tff(c_963, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_942, c_818])).
% 2.87/1.51  tff(c_965, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_16])).
% 2.87/1.51  tff(c_14, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.87/1.51  tff(c_1011, plain, ('#skF_6'='#skF_3' | '#skF_6'='#skF_2' | '#skF_6'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_965, c_965, c_965, c_965, c_14])).
% 2.87/1.51  tff(c_1012, plain, ('#skF_6'='#skF_1'), inference(splitLeft, [status(thm)], [c_1011])).
% 2.87/1.51  tff(c_968, plain, (![B_2]: (k2_zfmisc_1('#skF_6', B_2)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_965, c_965, c_6])).
% 2.87/1.51  tff(c_1016, plain, (![B_2]: (k2_zfmisc_1('#skF_1', B_2)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1012, c_1012, c_968])).
% 2.87/1.51  tff(c_1061, plain, (![A_97, B_98, C_99]: (k2_zfmisc_1(k2_zfmisc_1(A_97, B_98), C_99)=k3_zfmisc_1(A_97, B_98, C_99))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.87/1.51  tff(c_1083, plain, (![B_2, C_99]: (k3_zfmisc_1('#skF_1', B_2, C_99)=k2_zfmisc_1('#skF_1', C_99))), inference(superposition, [status(thm), theory('equality')], [c_1016, c_1061])).
% 2.87/1.51  tff(c_1093, plain, (![B_2, C_99]: (k3_zfmisc_1('#skF_1', B_2, C_99)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1016, c_1083])).
% 2.87/1.51  tff(c_964, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_16])).
% 2.87/1.51  tff(c_995, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_965, c_964])).
% 2.87/1.51  tff(c_1014, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1012, c_995])).
% 2.87/1.51  tff(c_1121, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1093, c_1014])).
% 2.87/1.51  tff(c_1122, plain, ('#skF_6'='#skF_2' | '#skF_6'='#skF_3'), inference(splitRight, [status(thm)], [c_1011])).
% 2.87/1.51  tff(c_1124, plain, ('#skF_6'='#skF_3'), inference(splitLeft, [status(thm)], [c_1122])).
% 2.87/1.51  tff(c_967, plain, (![A_1]: (k2_zfmisc_1(A_1, '#skF_6')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_965, c_965, c_4])).
% 2.87/1.51  tff(c_1131, plain, (![A_1]: (k2_zfmisc_1(A_1, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1124, c_1124, c_967])).
% 2.87/1.51  tff(c_1191, plain, (![A_108, B_109]: (k3_zfmisc_1(A_108, B_109, '#skF_3')='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1178, c_1131])).
% 2.87/1.51  tff(c_1130, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1124, c_995])).
% 2.87/1.51  tff(c_1214, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1191, c_1130])).
% 2.87/1.51  tff(c_1215, plain, ('#skF_6'='#skF_2'), inference(splitRight, [status(thm)], [c_1122])).
% 2.87/1.51  tff(c_1221, plain, (![B_2]: (k2_zfmisc_1('#skF_2', B_2)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1215, c_1215, c_968])).
% 2.87/1.51  tff(c_1220, plain, (![A_1]: (k2_zfmisc_1(A_1, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1215, c_1215, c_967])).
% 2.87/1.51  tff(c_1268, plain, (![A_115, B_116, C_117]: (k2_zfmisc_1(k2_zfmisc_1(A_115, B_116), C_117)=k3_zfmisc_1(A_115, B_116, C_117))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.87/1.51  tff(c_1290, plain, (![A_1, C_117]: (k3_zfmisc_1(A_1, '#skF_2', C_117)=k2_zfmisc_1('#skF_2', C_117))), inference(superposition, [status(thm), theory('equality')], [c_1220, c_1268])).
% 2.87/1.51  tff(c_1300, plain, (![A_1, C_117]: (k3_zfmisc_1(A_1, '#skF_2', C_117)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1221, c_1290])).
% 2.87/1.51  tff(c_1219, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1215, c_995])).
% 2.87/1.51  tff(c_1328, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1300, c_1219])).
% 2.87/1.51  tff(c_1330, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_24])).
% 2.87/1.51  tff(c_1332, plain, (![B_2]: (k2_zfmisc_1('#skF_4', B_2)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1330, c_1330, c_6])).
% 2.87/1.51  tff(c_1331, plain, (![A_1]: (k2_zfmisc_1(A_1, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1330, c_1330, c_4])).
% 2.87/1.51  tff(c_1515, plain, (![A_138, B_139, C_140]: (k2_zfmisc_1(k2_zfmisc_1(A_138, B_139), C_140)=k3_zfmisc_1(A_138, B_139, C_140))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.87/1.51  tff(c_1537, plain, (![A_1, C_140]: (k3_zfmisc_1(A_1, '#skF_4', C_140)=k2_zfmisc_1('#skF_4', C_140))), inference(superposition, [status(thm), theory('equality')], [c_1331, c_1515])).
% 2.87/1.51  tff(c_1547, plain, (![A_1, C_140]: (k3_zfmisc_1(A_1, '#skF_4', C_140)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1332, c_1537])).
% 2.87/1.51  tff(c_1454, plain, (![A_133, B_134, C_135]: (k2_zfmisc_1(k2_zfmisc_1(A_133, B_134), C_135)=k3_zfmisc_1(A_133, B_134, C_135))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.87/1.51  tff(c_1467, plain, (![A_133, B_134]: (k3_zfmisc_1(A_133, B_134, '#skF_4')='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1454, c_1331])).
% 2.87/1.51  tff(c_1385, plain, (![A_126, B_127, C_128]: (k2_zfmisc_1(k2_zfmisc_1(A_126, B_127), C_128)=k3_zfmisc_1(A_126, B_127, C_128))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.87/1.51  tff(c_1414, plain, (![B_2, C_128]: (k3_zfmisc_1('#skF_4', B_2, C_128)=k2_zfmisc_1('#skF_4', C_128))), inference(superposition, [status(thm), theory('equality')], [c_1332, c_1385])).
% 2.87/1.51  tff(c_1418, plain, (![B_2, C_128]: (k3_zfmisc_1('#skF_4', B_2, C_128)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1332, c_1414])).
% 2.87/1.51  tff(c_22, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.87/1.51  tff(c_1364, plain, ('#skF_3'='#skF_4' | '#skF_2'='#skF_4' | '#skF_1'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1330, c_1330, c_1330, c_1330, c_22])).
% 2.87/1.51  tff(c_1365, plain, ('#skF_1'='#skF_4'), inference(splitLeft, [status(thm)], [c_1364])).
% 2.87/1.51  tff(c_1329, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_24])).
% 2.87/1.51  tff(c_1361, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1330, c_1329])).
% 2.87/1.51  tff(c_1366, plain, (k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1365, c_1361])).
% 2.87/1.51  tff(c_1429, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1418, c_1366])).
% 2.87/1.51  tff(c_1430, plain, ('#skF_2'='#skF_4' | '#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_1364])).
% 2.87/1.51  tff(c_1432, plain, ('#skF_3'='#skF_4'), inference(splitLeft, [status(thm)], [c_1430])).
% 2.87/1.51  tff(c_1433, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1432, c_1361])).
% 2.87/1.51  tff(c_1490, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1467, c_1433])).
% 2.87/1.51  tff(c_1491, plain, ('#skF_2'='#skF_4'), inference(splitRight, [status(thm)], [c_1430])).
% 2.87/1.51  tff(c_1493, plain, (k3_zfmisc_1('#skF_1', '#skF_4', '#skF_3')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1491, c_1361])).
% 2.87/1.51  tff(c_1576, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1547, c_1493])).
% 2.87/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.87/1.51  
% 2.87/1.51  Inference rules
% 2.87/1.51  ----------------------
% 2.87/1.51  #Ref     : 0
% 2.87/1.51  #Sup     : 357
% 2.87/1.51  #Fact    : 0
% 2.87/1.51  #Define  : 0
% 2.87/1.51  #Split   : 18
% 2.87/1.51  #Chain   : 0
% 2.87/1.51  #Close   : 0
% 2.87/1.51  
% 2.87/1.51  Ordering : KBO
% 2.87/1.51  
% 2.87/1.51  Simplification rules
% 2.87/1.51  ----------------------
% 2.87/1.51  #Subsume      : 18
% 2.87/1.51  #Demod        : 340
% 2.87/1.51  #Tautology    : 285
% 2.87/1.51  #SimpNegUnit  : 13
% 2.87/1.51  #BackRed      : 103
% 2.87/1.51  
% 2.87/1.51  #Partial instantiations: 0
% 2.87/1.51  #Strategies tried      : 1
% 2.87/1.51  
% 2.87/1.51  Timing (in seconds)
% 2.87/1.51  ----------------------
% 2.87/1.51  Preprocessing        : 0.28
% 2.87/1.51  Parsing              : 0.14
% 2.87/1.51  CNF conversion       : 0.02
% 2.87/1.51  Main loop            : 0.38
% 2.87/1.51  Inferencing          : 0.14
% 2.87/1.51  Reduction            : 0.12
% 2.87/1.51  Demodulation         : 0.08
% 2.87/1.52  BG Simplification    : 0.02
% 2.87/1.52  Subsumption          : 0.06
% 2.87/1.52  Abstraction          : 0.02
% 2.87/1.52  MUC search           : 0.00
% 2.87/1.52  Cooper               : 0.00
% 2.87/1.52  Total                : 0.71
% 2.87/1.52  Index Insertion      : 0.00
% 2.87/1.52  Index Deletion       : 0.00
% 2.87/1.52  Index Matching       : 0.00
% 2.87/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
