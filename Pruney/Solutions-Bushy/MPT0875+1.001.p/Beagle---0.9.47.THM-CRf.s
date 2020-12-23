%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0875+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:00 EST 2020

% Result     : Theorem 2.49s
% Output     : CNFRefutation 2.81s
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

tff(f_26,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_45,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( A != k1_xboole_0
          & B != k1_xboole_0
          & C != k1_xboole_0 )
      <=> k3_zfmisc_1(A,B,C) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_mcart_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(c_1373,plain,(
    ! [A_123,B_124,C_125] : k2_zfmisc_1(k2_zfmisc_1(A_123,B_124),C_125) = k3_zfmisc_1(A_123,B_124,C_125) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_745,plain,(
    ! [A_69,B_70,C_71] : k2_zfmisc_1(k2_zfmisc_1(A_69,B_70),C_71) = k3_zfmisc_1(A_69,B_70,C_71) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_24,plain,
    ( k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != k1_xboole_0
    | k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_48,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_20,plain,
    ( k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != k1_xboole_0
    | k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_49,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_20])).

tff(c_16,plain,
    ( k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != k1_xboole_0
    | k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_47,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_16])).

tff(c_10,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1'
    | k3_zfmisc_1('#skF_4','#skF_5','#skF_6') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_142,plain,(
    k3_zfmisc_1('#skF_4','#skF_5','#skF_6') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_10])).

tff(c_61,plain,(
    ! [A_10,B_11,C_12] : k2_zfmisc_1(k2_zfmisc_1(A_10,B_11),C_12) = k3_zfmisc_1(A_10,B_11,C_12) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_4,plain,(
    ! [B_5,A_4] :
      ( k1_xboole_0 = B_5
      | k1_xboole_0 = A_4
      | k2_zfmisc_1(A_4,B_5) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_147,plain,(
    ! [C_19,A_20,B_21] :
      ( k1_xboole_0 = C_19
      | k2_zfmisc_1(A_20,B_21) = k1_xboole_0
      | k3_zfmisc_1(A_20,B_21,C_19) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_4])).

tff(c_150,plain,
    ( k1_xboole_0 = '#skF_6'
    | k2_zfmisc_1('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_142,c_147])).

tff(c_162,plain,(
    k2_zfmisc_1('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_47,c_150])).

tff(c_175,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_162,c_4])).

tff(c_182,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_49,c_175])).

tff(c_183,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_10])).

tff(c_185,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_183])).

tff(c_6,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_201,plain,(
    ! [A_22] : k2_zfmisc_1(A_22,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_185,c_6])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] : k2_zfmisc_1(k2_zfmisc_1(A_1,B_2),C_3) = k3_zfmisc_1(A_1,B_2,C_3) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_210,plain,(
    ! [A_1,B_2] : k3_zfmisc_1(A_1,B_2,'#skF_3') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_201,c_2])).

tff(c_12,plain,
    ( k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != k1_xboole_0
    | k3_zfmisc_1('#skF_4','#skF_5','#skF_6') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

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

tff(c_8,plain,(
    ! [B_5] : k2_zfmisc_1(k1_xboole_0,B_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_90,plain,(
    ! [B_5,C_12] : k3_zfmisc_1(k1_xboole_0,B_5,C_12) = k2_zfmisc_1(k1_xboole_0,C_12) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_61])).

tff(c_94,plain,(
    ! [B_5,C_12] : k3_zfmisc_1(k1_xboole_0,B_5,C_12) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_90])).

tff(c_268,plain,(
    ! [B_5,C_12] : k3_zfmisc_1('#skF_1',B_5,C_12) = '#skF_1' ),
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
    ! [B_5] : k2_zfmisc_1('#skF_2',B_5) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_348,c_348,c_8])).

tff(c_378,plain,(
    ! [A_35] : k2_zfmisc_1(A_35,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_348,c_348,c_6])).

tff(c_386,plain,(
    ! [A_35,C_3] : k3_zfmisc_1(A_35,'#skF_2',C_3) = k2_zfmisc_1('#skF_2',C_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_378,c_2])).

tff(c_402,plain,(
    ! [A_35,C_3] : k3_zfmisc_1(A_35,'#skF_2',C_3) = '#skF_2' ),
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
    inference(superposition,[status(thm),theory(equality)],[c_61,c_4])).

tff(c_518,plain,
    ( k1_xboole_0 = '#skF_6'
    | k2_zfmisc_1('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_457,c_506])).

tff(c_529,plain,(
    k2_zfmisc_1('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_47,c_518])).

tff(c_538,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_529,c_4])).

tff(c_545,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_49,c_538])).

tff(c_547,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_18,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_595,plain,
    ( '#skF_5' = '#skF_3'
    | '#skF_5' = '#skF_2'
    | '#skF_5' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_547,c_547,c_547,c_547,c_18])).

tff(c_596,plain,(
    '#skF_5' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_595])).

tff(c_551,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_5',B_5) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_547,c_547,c_8])).

tff(c_601,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_1',B_5) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_596,c_596,c_551])).

tff(c_646,plain,(
    ! [A_60,B_61,C_62] : k2_zfmisc_1(k2_zfmisc_1(A_60,B_61),C_62) = k3_zfmisc_1(A_60,B_61,C_62) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_675,plain,(
    ! [B_5,C_62] : k3_zfmisc_1('#skF_1',B_5,C_62) = k2_zfmisc_1('#skF_1',C_62) ),
    inference(superposition,[status(thm),theory(equality)],[c_601,c_646])).

tff(c_679,plain,(
    ! [B_5,C_62] : k3_zfmisc_1('#skF_1',B_5,C_62) = '#skF_1' ),
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
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_547,c_547,c_6])).

tff(c_697,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_3') = '#skF_3' ),
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
    ! [B_5] : k2_zfmisc_1('#skF_2',B_5) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_814,c_814,c_551])).

tff(c_819,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_814,c_814,c_550])).

tff(c_868,plain,(
    ! [A_78,B_79,C_80] : k2_zfmisc_1(k2_zfmisc_1(A_78,B_79),C_80) = k3_zfmisc_1(A_78,B_79,C_80) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_893,plain,(
    ! [A_4,C_80] : k3_zfmisc_1(A_4,'#skF_2',C_80) = k2_zfmisc_1('#skF_2',C_80) ),
    inference(superposition,[status(thm),theory(equality)],[c_819,c_868])).

tff(c_901,plain,(
    ! [A_4,C_80] : k3_zfmisc_1(A_4,'#skF_2',C_80) = '#skF_2' ),
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
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_968,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_4',B_5) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_965,c_965,c_8])).

tff(c_967,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_965,c_965,c_6])).

tff(c_1125,plain,(
    ! [A_101,B_102,C_103] : k2_zfmisc_1(k2_zfmisc_1(A_101,B_102),C_103) = k3_zfmisc_1(A_101,B_102,C_103) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_1147,plain,(
    ! [A_4,C_103] : k3_zfmisc_1(A_4,'#skF_4',C_103) = k2_zfmisc_1('#skF_4',C_103) ),
    inference(superposition,[status(thm),theory(equality)],[c_967,c_1125])).

tff(c_1157,plain,(
    ! [A_4,C_103] : k3_zfmisc_1(A_4,'#skF_4',C_103) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_968,c_1147])).

tff(c_1077,plain,(
    ! [A_98,B_99,C_100] : k2_zfmisc_1(k2_zfmisc_1(A_98,B_99),C_100) = k3_zfmisc_1(A_98,B_99,C_100) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_1090,plain,(
    ! [A_98,B_99] : k3_zfmisc_1(A_98,B_99,'#skF_4') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_1077,c_967])).

tff(c_1019,plain,(
    ! [A_93,B_94,C_95] : k2_zfmisc_1(k2_zfmisc_1(A_93,B_94),C_95) = k3_zfmisc_1(A_93,B_94,C_95) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_1048,plain,(
    ! [B_5,C_95] : k3_zfmisc_1('#skF_4',B_5,C_95) = k2_zfmisc_1('#skF_4',C_95) ),
    inference(superposition,[status(thm),theory(equality)],[c_968,c_1019])).

tff(c_1052,plain,(
    ! [B_5,C_95] : k3_zfmisc_1('#skF_4',B_5,C_95) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_968,c_1048])).

tff(c_22,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1010,plain,
    ( '#skF_3' = '#skF_4'
    | '#skF_2' = '#skF_4'
    | '#skF_1' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_965,c_965,c_965,c_965,c_22])).

tff(c_1011,plain,(
    '#skF_1' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_1010])).

tff(c_964,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_995,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_965,c_964])).

tff(c_1012,plain,(
    k3_zfmisc_1('#skF_4','#skF_2','#skF_3') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1011,c_995])).

tff(c_1064,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1052,c_1012])).

tff(c_1065,plain,
    ( '#skF_2' = '#skF_4'
    | '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1010])).

tff(c_1067,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_1065])).

tff(c_1068,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1067,c_995])).

tff(c_1113,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1090,c_1068])).

tff(c_1114,plain,(
    '#skF_2' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1065])).

tff(c_1118,plain,(
    k3_zfmisc_1('#skF_1','#skF_4','#skF_3') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1114,c_995])).

tff(c_1187,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1157,c_1118])).

tff(c_1189,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_16])).

tff(c_14,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1222,plain,
    ( '#skF_6' = '#skF_3'
    | '#skF_6' = '#skF_2'
    | '#skF_6' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1189,c_1189,c_1189,c_1189,c_14])).

tff(c_1223,plain,(
    '#skF_6' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_1222])).

tff(c_1191,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_6',B_5) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1189,c_1189,c_8])).

tff(c_1225,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_1',B_5) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1223,c_1223,c_1191])).

tff(c_1273,plain,(
    ! [A_114,B_115,C_116] : k2_zfmisc_1(k2_zfmisc_1(A_114,B_115),C_116) = k3_zfmisc_1(A_114,B_115,C_116) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_1302,plain,(
    ! [B_5,C_116] : k3_zfmisc_1('#skF_1',B_5,C_116) = k2_zfmisc_1('#skF_1',C_116) ),
    inference(superposition,[status(thm),theory(equality)],[c_1225,c_1273])).

tff(c_1306,plain,(
    ! [B_5,C_116] : k3_zfmisc_1('#skF_1',B_5,C_116) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1225,c_1302])).

tff(c_1188,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_16])).

tff(c_1218,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1189,c_1188])).

tff(c_1224,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1223,c_1218])).

tff(c_1318,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1306,c_1224])).

tff(c_1319,plain,
    ( '#skF_6' = '#skF_2'
    | '#skF_6' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1222])).

tff(c_1321,plain,(
    '#skF_6' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_1319])).

tff(c_1190,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1189,c_1189,c_6])).

tff(c_1325,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1321,c_1321,c_1190])).

tff(c_1386,plain,(
    ! [A_123,B_124] : k3_zfmisc_1(A_123,B_124,'#skF_3') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_1373,c_1325])).

tff(c_1323,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1321,c_1218])).

tff(c_1409,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1386,c_1323])).

tff(c_1410,plain,(
    '#skF_6' = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_1319])).

tff(c_1414,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_2',B_5) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1410,c_1410,c_1191])).

tff(c_1415,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1410,c_1410,c_1190])).

tff(c_1464,plain,(
    ! [A_130,B_131,C_132] : k2_zfmisc_1(k2_zfmisc_1(A_130,B_131),C_132) = k3_zfmisc_1(A_130,B_131,C_132) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_1486,plain,(
    ! [A_4,C_132] : k3_zfmisc_1(A_4,'#skF_2',C_132) = k2_zfmisc_1('#skF_2',C_132) ),
    inference(superposition,[status(thm),theory(equality)],[c_1415,c_1464])).

tff(c_1496,plain,(
    ! [A_4,C_132] : k3_zfmisc_1(A_4,'#skF_2',C_132) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1414,c_1486])).

tff(c_1413,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1410,c_1218])).

tff(c_1524,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1496,c_1413])).

%------------------------------------------------------------------------------
