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
% DateTime   : Thu Dec  3 10:09:29 EST 2020

% Result     : Theorem 5.04s
% Output     : CNFRefutation 5.33s
% Verified   : 
% Statistics : Number of formulae       :  237 (6062 expanded)
%              Number of leaves         :   18 (1679 expanded)
%              Depth                    :   20
%              Number of atoms          :  309 (14342 expanded)
%              Number of equality atoms :  284 (14317 expanded)
%              Maximal formula depth    :   12 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_56,negated_conjecture,(
    ~ ! [A,B,C,D,E,F] :
        ( k3_zfmisc_1(A,B,C) = k3_zfmisc_1(D,E,F)
       => ( k3_zfmisc_1(A,B,C) = k1_xboole_0
          | ( A = D
            & B = E
            & C = F ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_mcart_1)).

tff(f_45,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & ~ ( k1_relat_1(k2_zfmisc_1(A,B)) = A
            & k2_relat_1(k2_zfmisc_1(A,B)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t195_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(c_14,plain,
    ( '#skF_6' != '#skF_3'
    | '#skF_5' != '#skF_2'
    | '#skF_1' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_42,plain,(
    '#skF_1' != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_14])).

tff(c_18,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = k3_zfmisc_1('#skF_4','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_98,plain,(
    ! [A_16,B_17,C_18] : k2_zfmisc_1(k2_zfmisc_1(A_16,B_17),C_18) = k3_zfmisc_1(A_16,B_17,C_18) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( k2_relat_1(k2_zfmisc_1(A_3,B_4)) = B_4
      | k1_xboole_0 = B_4
      | k1_xboole_0 = A_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_252,plain,(
    ! [A_32,B_33,C_34] :
      ( k2_relat_1(k3_zfmisc_1(A_32,B_33,C_34)) = C_34
      | k1_xboole_0 = C_34
      | k2_zfmisc_1(A_32,B_33) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_8])).

tff(c_273,plain,
    ( k2_relat_1(k3_zfmisc_1('#skF_4','#skF_5','#skF_6')) = '#skF_3'
    | k1_xboole_0 = '#skF_3'
    | k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_252])).

tff(c_280,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_273])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( k1_xboole_0 = B_2
      | k1_xboole_0 = A_1
      | k2_zfmisc_1(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_301,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_280,c_2])).

tff(c_303,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_301])).

tff(c_16,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_19,plain,(
    k3_zfmisc_1('#skF_4','#skF_5','#skF_6') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_16])).

tff(c_313,plain,(
    k3_zfmisc_1('#skF_4','#skF_5','#skF_6') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_303,c_19])).

tff(c_6,plain,(
    ! [B_2] : k2_zfmisc_1(k1_xboole_0,B_2) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12,plain,(
    ! [A_5,B_6,C_7] : k2_zfmisc_1(k2_zfmisc_1(A_5,B_6),C_7) = k3_zfmisc_1(A_5,B_6,C_7) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_287,plain,(
    ! [C_7] : k3_zfmisc_1('#skF_1','#skF_2',C_7) = k2_zfmisc_1(k1_xboole_0,C_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_280,c_12])).

tff(c_300,plain,(
    ! [C_7] : k3_zfmisc_1('#skF_1','#skF_2',C_7) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_287])).

tff(c_402,plain,(
    ! [C_7] : k3_zfmisc_1('#skF_1','#skF_2',C_7) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_303,c_300])).

tff(c_403,plain,(
    k3_zfmisc_1('#skF_4','#skF_5','#skF_6') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_402,c_18])).

tff(c_405,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_313,c_403])).

tff(c_406,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_301])).

tff(c_443,plain,(
    k3_zfmisc_1('#skF_4','#skF_5','#skF_6') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_406,c_19])).

tff(c_4,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_126,plain,(
    ! [A_1,C_18] : k3_zfmisc_1(A_1,k1_xboole_0,C_18) = k2_zfmisc_1(k1_xboole_0,C_18) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_98])).

tff(c_136,plain,(
    ! [A_1,C_18] : k3_zfmisc_1(A_1,k1_xboole_0,C_18) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_126])).

tff(c_437,plain,(
    ! [A_1,C_18] : k3_zfmisc_1(A_1,'#skF_2',C_18) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_406,c_406,c_136])).

tff(c_526,plain,(
    k3_zfmisc_1('#skF_4','#skF_5','#skF_6') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_437,c_18])).

tff(c_528,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_443,c_526])).

tff(c_529,plain,
    ( k1_xboole_0 = '#skF_3'
    | k2_relat_1(k3_zfmisc_1('#skF_4','#skF_5','#skF_6')) = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_273])).

tff(c_561,plain,(
    k2_relat_1(k3_zfmisc_1('#skF_4','#skF_5','#skF_6')) = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_529])).

tff(c_107,plain,(
    ! [A_16,B_17,C_18] :
      ( k2_relat_1(k3_zfmisc_1(A_16,B_17,C_18)) = C_18
      | k1_xboole_0 = C_18
      | k2_zfmisc_1(A_16,B_17) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_8])).

tff(c_565,plain,
    ( '#skF_6' = '#skF_3'
    | k1_xboole_0 = '#skF_6'
    | k2_zfmisc_1('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_561,c_107])).

tff(c_572,plain,(
    k2_zfmisc_1('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_565])).

tff(c_701,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_572,c_2])).

tff(c_703,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_701])).

tff(c_687,plain,(
    ! [C_7] : k3_zfmisc_1('#skF_4','#skF_5',C_7) = k2_zfmisc_1(k1_xboole_0,C_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_572,c_12])).

tff(c_700,plain,(
    ! [C_7] : k3_zfmisc_1('#skF_4','#skF_5',C_7) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_687])).

tff(c_771,plain,(
    ! [C_7] : k3_zfmisc_1('#skF_4','#skF_5',C_7) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_703,c_700])).

tff(c_716,plain,(
    k3_zfmisc_1('#skF_4','#skF_5','#skF_6') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_703,c_19])).

tff(c_777,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_771,c_716])).

tff(c_778,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_701])).

tff(c_786,plain,(
    ! [A_1,C_18] : k3_zfmisc_1(A_1,'#skF_5',C_18) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_778,c_778,c_136])).

tff(c_792,plain,(
    k3_zfmisc_1('#skF_4','#skF_5','#skF_6') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_778,c_19])).

tff(c_864,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_786,c_792])).

tff(c_866,plain,(
    k2_zfmisc_1('#skF_4','#skF_5') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_565])).

tff(c_865,plain,
    ( k1_xboole_0 = '#skF_6'
    | '#skF_6' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_565])).

tff(c_867,plain,(
    '#skF_6' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_865])).

tff(c_530,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_273])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( k1_relat_1(k2_zfmisc_1(A_3,B_4)) = A_3
      | k1_xboole_0 = B_4
      | k1_xboole_0 = A_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_532,plain,(
    ! [A_49,B_50,C_51] :
      ( k1_relat_1(k3_zfmisc_1(A_49,B_50,C_51)) = k2_zfmisc_1(A_49,B_50)
      | k1_xboole_0 = C_51
      | k2_zfmisc_1(A_49,B_50) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_10])).

tff(c_553,plain,
    ( k1_relat_1(k3_zfmisc_1('#skF_4','#skF_5','#skF_6')) = k2_zfmisc_1('#skF_1','#skF_2')
    | k1_xboole_0 = '#skF_3'
    | k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_532])).

tff(c_560,plain,
    ( k1_relat_1(k3_zfmisc_1('#skF_4','#skF_5','#skF_6')) = k2_zfmisc_1('#skF_1','#skF_2')
    | k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_530,c_553])).

tff(c_875,plain,
    ( k1_relat_1(k3_zfmisc_1('#skF_4','#skF_5','#skF_3')) = k2_zfmisc_1('#skF_1','#skF_2')
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_867,c_560])).

tff(c_876,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_875])).

tff(c_117,plain,(
    ! [A_16,B_17] : k3_zfmisc_1(A_16,B_17,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_4])).

tff(c_885,plain,(
    ! [A_16,B_17] : k3_zfmisc_1(A_16,B_17,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_876,c_876,c_117])).

tff(c_870,plain,(
    k3_zfmisc_1('#skF_4','#skF_5','#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_867,c_19])).

tff(c_877,plain,(
    k3_zfmisc_1('#skF_4','#skF_5','#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_876,c_870])).

tff(c_1007,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_885,c_877])).

tff(c_1009,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_875])).

tff(c_1008,plain,(
    k1_relat_1(k3_zfmisc_1('#skF_4','#skF_5','#skF_3')) = k2_zfmisc_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_875])).

tff(c_110,plain,(
    ! [A_16,B_17,C_18] :
      ( k1_relat_1(k3_zfmisc_1(A_16,B_17,C_18)) = k2_zfmisc_1(A_16,B_17)
      | k1_xboole_0 = C_18
      | k2_zfmisc_1(A_16,B_17) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_10])).

tff(c_1027,plain,
    ( k2_zfmisc_1('#skF_1','#skF_2') = k2_zfmisc_1('#skF_4','#skF_5')
    | k1_xboole_0 = '#skF_3'
    | k2_zfmisc_1('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1008,c_110])).

tff(c_1033,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = k2_zfmisc_1('#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_866,c_1009,c_1027])).

tff(c_1068,plain,
    ( k1_relat_1(k2_zfmisc_1('#skF_4','#skF_5')) = '#skF_1'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_1033,c_10])).

tff(c_1129,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_1068])).

tff(c_1132,plain,(
    k2_zfmisc_1('#skF_4','#skF_5') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1129,c_866])).

tff(c_1143,plain,(
    ! [B_2] : k2_zfmisc_1('#skF_1',B_2) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1129,c_1129,c_6])).

tff(c_1169,plain,(
    k2_zfmisc_1('#skF_4','#skF_5') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1143,c_1033])).

tff(c_1171,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1132,c_1169])).

tff(c_1172,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1(k2_zfmisc_1('#skF_4','#skF_5')) = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1068])).

tff(c_1174,plain,(
    k1_relat_1(k2_zfmisc_1('#skF_4','#skF_5')) = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_1172])).

tff(c_1178,plain,
    ( '#skF_1' = '#skF_4'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_1174,c_10])).

tff(c_1184,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_1178])).

tff(c_1310,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_1184])).

tff(c_1326,plain,(
    ! [B_2] : k2_zfmisc_1('#skF_4',B_2) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1310,c_1310,c_6])).

tff(c_1315,plain,(
    k2_zfmisc_1('#skF_4','#skF_5') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1310,c_866])).

tff(c_1363,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1326,c_1315])).

tff(c_1364,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_1184])).

tff(c_1381,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1364,c_1364,c_4])).

tff(c_1371,plain,(
    k2_zfmisc_1('#skF_4','#skF_5') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1364,c_866])).

tff(c_1413,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1381,c_1371])).

tff(c_1414,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_1172])).

tff(c_1419,plain,(
    k2_zfmisc_1('#skF_4','#skF_5') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1414,c_866])).

tff(c_1429,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1414,c_1414,c_4])).

tff(c_1435,plain,(
    k2_zfmisc_1('#skF_4','#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1429,c_1033])).

tff(c_1479,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1419,c_1435])).

tff(c_1480,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_865])).

tff(c_1489,plain,(
    ! [A_16,B_17] : k3_zfmisc_1(A_16,B_17,'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1480,c_1480,c_117])).

tff(c_1493,plain,(
    k3_zfmisc_1('#skF_4','#skF_5','#skF_6') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1480,c_19])).

tff(c_1557,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1489,c_1493])).

tff(c_1558,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_529])).

tff(c_1570,plain,(
    k3_zfmisc_1('#skF_4','#skF_5','#skF_6') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1558,c_19])).

tff(c_1566,plain,(
    ! [A_16,B_17] : k3_zfmisc_1(A_16,B_17,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1558,c_1558,c_117])).

tff(c_1650,plain,(
    k3_zfmisc_1('#skF_4','#skF_5','#skF_6') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1566,c_18])).

tff(c_1652,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1570,c_1650])).

tff(c_1653,plain,
    ( '#skF_5' != '#skF_2'
    | '#skF_6' != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_14])).

tff(c_1664,plain,(
    '#skF_6' != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_1653])).

tff(c_1654,plain,(
    '#skF_1' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_14])).

tff(c_1659,plain,(
    k3_zfmisc_1('#skF_4','#skF_5','#skF_6') = k3_zfmisc_1('#skF_4','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1654,c_18])).

tff(c_1721,plain,(
    ! [A_93,B_94,C_95] : k2_zfmisc_1(k2_zfmisc_1(A_93,B_94),C_95) = k3_zfmisc_1(A_93,B_94,C_95) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1874,plain,(
    ! [A_109,B_110,C_111] :
      ( k2_relat_1(k3_zfmisc_1(A_109,B_110,C_111)) = C_111
      | k1_xboole_0 = C_111
      | k2_zfmisc_1(A_109,B_110) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1721,c_8])).

tff(c_1895,plain,
    ( k2_relat_1(k3_zfmisc_1('#skF_4','#skF_2','#skF_3')) = '#skF_6'
    | k1_xboole_0 = '#skF_6'
    | k2_zfmisc_1('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1659,c_1874])).

tff(c_1903,plain,(
    k2_zfmisc_1('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_1895])).

tff(c_1924,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_1903,c_2])).

tff(c_1926,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_1924])).

tff(c_1756,plain,(
    ! [B_2,C_95] : k3_zfmisc_1(k1_xboole_0,B_2,C_95) = k2_zfmisc_1(k1_xboole_0,C_95) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_1721])).

tff(c_1760,plain,(
    ! [B_2,C_95] : k3_zfmisc_1(k1_xboole_0,B_2,C_95) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1756])).

tff(c_1930,plain,(
    ! [B_2,C_95] : k3_zfmisc_1('#skF_4',B_2,C_95) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1926,c_1926,c_1760])).

tff(c_1665,plain,(
    k3_zfmisc_1('#skF_4','#skF_2','#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1659,c_19])).

tff(c_1936,plain,(
    k3_zfmisc_1('#skF_4','#skF_2','#skF_3') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1926,c_1665])).

tff(c_2042,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1930,c_1936])).

tff(c_2043,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_1924])).

tff(c_1749,plain,(
    ! [A_1,C_95] : k3_zfmisc_1(A_1,k1_xboole_0,C_95) = k2_zfmisc_1(k1_xboole_0,C_95) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_1721])).

tff(c_1759,plain,(
    ! [A_1,C_95] : k3_zfmisc_1(A_1,k1_xboole_0,C_95) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1749])).

tff(c_2052,plain,(
    ! [A_1,C_95] : k3_zfmisc_1(A_1,'#skF_5',C_95) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2043,c_2043,c_1759])).

tff(c_2128,plain,(
    k3_zfmisc_1('#skF_4','#skF_2','#skF_3') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2052,c_1659])).

tff(c_2057,plain,(
    k3_zfmisc_1('#skF_4','#skF_2','#skF_3') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2043,c_1665])).

tff(c_2212,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2128,c_2057])).

tff(c_2213,plain,
    ( k1_xboole_0 = '#skF_6'
    | k2_relat_1(k3_zfmisc_1('#skF_4','#skF_2','#skF_3')) = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_1895])).

tff(c_2215,plain,(
    k2_relat_1(k3_zfmisc_1('#skF_4','#skF_2','#skF_3')) = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_2213])).

tff(c_1733,plain,(
    ! [A_93,B_94,C_95] :
      ( k2_relat_1(k3_zfmisc_1(A_93,B_94,C_95)) = C_95
      | k1_xboole_0 = C_95
      | k2_zfmisc_1(A_93,B_94) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1721,c_8])).

tff(c_2219,plain,
    ( '#skF_6' = '#skF_3'
    | k1_xboole_0 = '#skF_3'
    | k2_zfmisc_1('#skF_4','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2215,c_1733])).

tff(c_2225,plain,
    ( k1_xboole_0 = '#skF_3'
    | k2_zfmisc_1('#skF_4','#skF_2') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_1664,c_2219])).

tff(c_2258,plain,(
    k2_zfmisc_1('#skF_4','#skF_2') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_2225])).

tff(c_2279,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_2258,c_2])).

tff(c_2281,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_2279])).

tff(c_2296,plain,(
    ! [B_2] : k2_zfmisc_1('#skF_4',B_2) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2281,c_2281,c_6])).

tff(c_2214,plain,(
    k2_zfmisc_1('#skF_4','#skF_5') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1895])).

tff(c_2285,plain,(
    k2_zfmisc_1('#skF_4','#skF_5') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2281,c_2214])).

tff(c_2324,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2296,c_2285])).

tff(c_2325,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_2279])).

tff(c_2265,plain,(
    ! [C_7] : k3_zfmisc_1('#skF_4','#skF_2',C_7) = k2_zfmisc_1(k1_xboole_0,C_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_2258,c_12])).

tff(c_2278,plain,(
    ! [C_7] : k3_zfmisc_1('#skF_4','#skF_2',C_7) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_2265])).

tff(c_2551,plain,(
    ! [C_7] : k3_zfmisc_1('#skF_4','#skF_2',C_7) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2325,c_2278])).

tff(c_2496,plain,(
    k3_zfmisc_1('#skF_4','#skF_2','#skF_3') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2325,c_1665])).

tff(c_2557,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2551,c_2496])).

tff(c_2558,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_2225])).

tff(c_1740,plain,(
    ! [A_93,B_94] : k3_zfmisc_1(A_93,B_94,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1721,c_4])).

tff(c_2566,plain,(
    ! [A_93,B_94] : k3_zfmisc_1(A_93,B_94,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2558,c_2558,c_1740])).

tff(c_2570,plain,(
    k3_zfmisc_1('#skF_4','#skF_2','#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2558,c_1665])).

tff(c_2632,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2566,c_2570])).

tff(c_2633,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_2213])).

tff(c_2644,plain,(
    k3_zfmisc_1('#skF_4','#skF_2','#skF_3') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2633,c_1665])).

tff(c_2640,plain,(
    ! [A_93,B_94] : k3_zfmisc_1(A_93,B_94,'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2633,c_2633,c_1740])).

tff(c_2752,plain,(
    k3_zfmisc_1('#skF_4','#skF_2','#skF_3') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2640,c_1659])).

tff(c_2754,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2644,c_2752])).

tff(c_2756,plain,(
    '#skF_6' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1653])).

tff(c_2773,plain,(
    k3_zfmisc_1('#skF_4','#skF_5','#skF_3') = k3_zfmisc_1('#skF_4','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2756,c_1659])).

tff(c_2885,plain,(
    ! [A_170,B_171] :
      ( k2_relat_1(k2_zfmisc_1(A_170,B_171)) = B_171
      | k1_xboole_0 = B_171
      | k1_xboole_0 = A_170 ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2927,plain,(
    ! [A_175,B_176,C_177] :
      ( k2_relat_1(k3_zfmisc_1(A_175,B_176,C_177)) = C_177
      | k1_xboole_0 = C_177
      | k2_zfmisc_1(A_175,B_176) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_2885])).

tff(c_2945,plain,
    ( k2_relat_1(k3_zfmisc_1('#skF_4','#skF_2','#skF_3')) = '#skF_3'
    | k1_xboole_0 = '#skF_3'
    | k2_zfmisc_1('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2773,c_2927])).

tff(c_3001,plain,(
    k2_zfmisc_1('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_2945])).

tff(c_3022,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_3001,c_2])).

tff(c_3024,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_3022])).

tff(c_2779,plain,(
    ! [A_159,B_160,C_161] : k2_zfmisc_1(k2_zfmisc_1(A_159,B_160),C_161) = k3_zfmisc_1(A_159,B_160,C_161) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2808,plain,(
    ! [B_2,C_161] : k3_zfmisc_1(k1_xboole_0,B_2,C_161) = k2_zfmisc_1(k1_xboole_0,C_161) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_2779])).

tff(c_2812,plain,(
    ! [B_2,C_161] : k3_zfmisc_1(k1_xboole_0,B_2,C_161) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_2808])).

tff(c_3029,plain,(
    ! [B_2,C_161] : k3_zfmisc_1('#skF_4',B_2,C_161) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3024,c_3024,c_2812])).

tff(c_2757,plain,(
    k3_zfmisc_1('#skF_4','#skF_5','#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2756,c_19])).

tff(c_2774,plain,(
    k3_zfmisc_1('#skF_4','#skF_2','#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2773,c_2757])).

tff(c_3033,plain,(
    k3_zfmisc_1('#skF_4','#skF_2','#skF_3') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3024,c_2774])).

tff(c_3117,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3029,c_3033])).

tff(c_3118,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_3022])).

tff(c_2801,plain,(
    ! [A_1,C_161] : k3_zfmisc_1(A_1,k1_xboole_0,C_161) = k2_zfmisc_1(k1_xboole_0,C_161) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_2779])).

tff(c_2811,plain,(
    ! [A_1,C_161] : k3_zfmisc_1(A_1,k1_xboole_0,C_161) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_2801])).

tff(c_3128,plain,(
    ! [A_1,C_161] : k3_zfmisc_1(A_1,'#skF_5',C_161) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3118,c_3118,c_2811])).

tff(c_3224,plain,(
    k3_zfmisc_1('#skF_4','#skF_2','#skF_3') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3128,c_2773])).

tff(c_3131,plain,(
    k3_zfmisc_1('#skF_4','#skF_2','#skF_3') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3118,c_2774])).

tff(c_3262,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3224,c_3131])).

tff(c_3264,plain,(
    k2_zfmisc_1('#skF_4','#skF_5') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_2945])).

tff(c_2823,plain,(
    ! [A_164,B_165] :
      ( k1_relat_1(k2_zfmisc_1(A_164,B_165)) = A_164
      | k1_xboole_0 = B_165
      | k1_xboole_0 = A_164 ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_3279,plain,(
    ! [A_198,B_199,C_200] :
      ( k1_relat_1(k3_zfmisc_1(A_198,B_199,C_200)) = k2_zfmisc_1(A_198,B_199)
      | k1_xboole_0 = C_200
      | k2_zfmisc_1(A_198,B_199) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_2823])).

tff(c_3300,plain,
    ( k1_relat_1(k3_zfmisc_1('#skF_4','#skF_2','#skF_3')) = k2_zfmisc_1('#skF_4','#skF_5')
    | k1_xboole_0 = '#skF_3'
    | k2_zfmisc_1('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2773,c_3279])).

tff(c_3307,plain,
    ( k1_relat_1(k3_zfmisc_1('#skF_4','#skF_2','#skF_3')) = k2_zfmisc_1('#skF_4','#skF_5')
    | k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_3264,c_3300])).

tff(c_3308,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_3307])).

tff(c_2792,plain,(
    ! [A_159,B_160] : k3_zfmisc_1(A_159,B_160,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2779,c_4])).

tff(c_3317,plain,(
    ! [A_159,B_160] : k3_zfmisc_1(A_159,B_160,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3308,c_3308,c_2792])).

tff(c_3318,plain,(
    k3_zfmisc_1('#skF_4','#skF_2','#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3308,c_2774])).

tff(c_3403,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3317,c_3318])).

tff(c_3405,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_3307])).

tff(c_3404,plain,(
    k1_relat_1(k3_zfmisc_1('#skF_4','#skF_2','#skF_3')) = k2_zfmisc_1('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_3307])).

tff(c_2832,plain,(
    ! [A_5,B_6,C_7] :
      ( k1_relat_1(k3_zfmisc_1(A_5,B_6,C_7)) = k2_zfmisc_1(A_5,B_6)
      | k1_xboole_0 = C_7
      | k2_zfmisc_1(A_5,B_6) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_2823])).

tff(c_3409,plain,
    ( k2_zfmisc_1('#skF_4','#skF_5') = k2_zfmisc_1('#skF_4','#skF_2')
    | k1_xboole_0 = '#skF_3'
    | k2_zfmisc_1('#skF_4','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_3404,c_2832])).

tff(c_3415,plain,
    ( k2_zfmisc_1('#skF_4','#skF_5') = k2_zfmisc_1('#skF_4','#skF_2')
    | k2_zfmisc_1('#skF_4','#skF_2') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_3405,c_3409])).

tff(c_3418,plain,(
    k2_zfmisc_1('#skF_4','#skF_2') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_3415])).

tff(c_3439,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_3418,c_2])).

tff(c_3441,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_3439])).

tff(c_3458,plain,(
    ! [B_2] : k2_zfmisc_1('#skF_4',B_2) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3441,c_3441,c_6])).

tff(c_3447,plain,(
    k2_zfmisc_1('#skF_4','#skF_5') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3441,c_3264])).

tff(c_3487,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3458,c_3447])).

tff(c_3488,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_3439])).

tff(c_3501,plain,(
    ! [A_1,C_161] : k3_zfmisc_1(A_1,'#skF_2',C_161) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3488,c_3488,c_2811])).

tff(c_3504,plain,(
    k3_zfmisc_1('#skF_4','#skF_2','#skF_3') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3488,c_2774])).

tff(c_3594,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3501,c_3504])).

tff(c_3596,plain,(
    k2_zfmisc_1('#skF_4','#skF_2') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_3415])).

tff(c_3413,plain,
    ( k2_zfmisc_1('#skF_4','#skF_5') = k2_zfmisc_1('#skF_4','#skF_2')
    | k1_xboole_0 = '#skF_3'
    | k2_zfmisc_1('#skF_4','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2832,c_3404])).

tff(c_3417,plain,
    ( k2_zfmisc_1('#skF_4','#skF_5') = k2_zfmisc_1('#skF_4','#skF_2')
    | k2_zfmisc_1('#skF_4','#skF_2') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_3405,c_3413])).

tff(c_3597,plain,(
    k2_zfmisc_1('#skF_4','#skF_5') = k2_zfmisc_1('#skF_4','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_3596,c_3417])).

tff(c_3606,plain,
    ( k2_relat_1(k2_zfmisc_1('#skF_4','#skF_2')) = '#skF_5'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_3597,c_8])).

tff(c_3714,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_3606])).

tff(c_3730,plain,(
    ! [B_2] : k2_zfmisc_1('#skF_4',B_2) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3714,c_3714,c_6])).

tff(c_3717,plain,(
    k2_zfmisc_1('#skF_4','#skF_2') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3714,c_3596])).

tff(c_3760,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3730,c_3717])).

tff(c_3762,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_3606])).

tff(c_2755,plain,(
    '#skF_5' != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_1653])).

tff(c_3761,plain,
    ( k1_xboole_0 = '#skF_5'
    | k2_relat_1(k2_zfmisc_1('#skF_4','#skF_2')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_3606])).

tff(c_3763,plain,(
    k2_relat_1(k2_zfmisc_1('#skF_4','#skF_2')) = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_3761])).

tff(c_3771,plain,
    ( '#skF_5' = '#skF_2'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_3763])).

tff(c_3775,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_3762,c_2755,c_3771])).

tff(c_3820,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3775,c_3775,c_4])).

tff(c_3808,plain,(
    k2_zfmisc_1('#skF_4','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3775,c_3596])).

tff(c_3851,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3820,c_3808])).

tff(c_3852,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_3761])).

tff(c_3859,plain,(
    k2_zfmisc_1('#skF_4','#skF_2') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3852,c_3596])).

tff(c_3871,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3852,c_3852,c_4])).

tff(c_3878,plain,(
    k2_zfmisc_1('#skF_4','#skF_2') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3871,c_3597])).

tff(c_3880,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3859,c_3878])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:02:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.04/2.41  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.33/2.46  
% 5.33/2.46  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.33/2.46  %$ k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 5.33/2.46  
% 5.33/2.46  %Foreground sorts:
% 5.33/2.46  
% 5.33/2.46  
% 5.33/2.46  %Background operators:
% 5.33/2.46  
% 5.33/2.46  
% 5.33/2.46  %Foreground operators:
% 5.33/2.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.33/2.46  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.33/2.46  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.33/2.46  tff('#skF_5', type, '#skF_5': $i).
% 5.33/2.46  tff('#skF_6', type, '#skF_6': $i).
% 5.33/2.46  tff('#skF_2', type, '#skF_2': $i).
% 5.33/2.46  tff('#skF_3', type, '#skF_3': $i).
% 5.33/2.46  tff('#skF_1', type, '#skF_1': $i).
% 5.33/2.46  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 5.33/2.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.33/2.46  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.33/2.46  tff('#skF_4', type, '#skF_4': $i).
% 5.33/2.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.33/2.46  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.33/2.46  
% 5.33/2.51  tff(f_56, negated_conjecture, ~(![A, B, C, D, E, F]: ((k3_zfmisc_1(A, B, C) = k3_zfmisc_1(D, E, F)) => ((k3_zfmisc_1(A, B, C) = k1_xboole_0) | (((A = D) & (B = E)) & (C = F))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_mcart_1)).
% 5.33/2.51  tff(f_45, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 5.33/2.51  tff(f_43, axiom, (![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~((k1_relat_1(k2_zfmisc_1(A, B)) = A) & (k2_relat_1(k2_zfmisc_1(A, B)) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t195_relat_1)).
% 5.33/2.51  tff(f_31, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 5.33/2.51  tff(c_14, plain, ('#skF_6'!='#skF_3' | '#skF_5'!='#skF_2' | '#skF_1'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.33/2.51  tff(c_42, plain, ('#skF_1'!='#skF_4'), inference(splitLeft, [status(thm)], [c_14])).
% 5.33/2.51  tff(c_18, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')=k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.33/2.51  tff(c_98, plain, (![A_16, B_17, C_18]: (k2_zfmisc_1(k2_zfmisc_1(A_16, B_17), C_18)=k3_zfmisc_1(A_16, B_17, C_18))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.33/2.51  tff(c_8, plain, (![A_3, B_4]: (k2_relat_1(k2_zfmisc_1(A_3, B_4))=B_4 | k1_xboole_0=B_4 | k1_xboole_0=A_3)), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.33/2.51  tff(c_252, plain, (![A_32, B_33, C_34]: (k2_relat_1(k3_zfmisc_1(A_32, B_33, C_34))=C_34 | k1_xboole_0=C_34 | k2_zfmisc_1(A_32, B_33)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_98, c_8])).
% 5.33/2.51  tff(c_273, plain, (k2_relat_1(k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6'))='#skF_3' | k1_xboole_0='#skF_3' | k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_18, c_252])).
% 5.33/2.51  tff(c_280, plain, (k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_273])).
% 5.33/2.51  tff(c_2, plain, (![B_2, A_1]: (k1_xboole_0=B_2 | k1_xboole_0=A_1 | k2_zfmisc_1(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.33/2.51  tff(c_301, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_280, c_2])).
% 5.33/2.51  tff(c_303, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_301])).
% 5.33/2.51  tff(c_16, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.33/2.51  tff(c_19, plain, (k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_18, c_16])).
% 5.33/2.51  tff(c_313, plain, (k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_303, c_19])).
% 5.33/2.51  tff(c_6, plain, (![B_2]: (k2_zfmisc_1(k1_xboole_0, B_2)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.33/2.51  tff(c_12, plain, (![A_5, B_6, C_7]: (k2_zfmisc_1(k2_zfmisc_1(A_5, B_6), C_7)=k3_zfmisc_1(A_5, B_6, C_7))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.33/2.51  tff(c_287, plain, (![C_7]: (k3_zfmisc_1('#skF_1', '#skF_2', C_7)=k2_zfmisc_1(k1_xboole_0, C_7))), inference(superposition, [status(thm), theory('equality')], [c_280, c_12])).
% 5.33/2.51  tff(c_300, plain, (![C_7]: (k3_zfmisc_1('#skF_1', '#skF_2', C_7)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_287])).
% 5.33/2.51  tff(c_402, plain, (![C_7]: (k3_zfmisc_1('#skF_1', '#skF_2', C_7)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_303, c_300])).
% 5.33/2.51  tff(c_403, plain, (k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_402, c_18])).
% 5.33/2.51  tff(c_405, plain, $false, inference(negUnitSimplification, [status(thm)], [c_313, c_403])).
% 5.33/2.51  tff(c_406, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_301])).
% 5.33/2.51  tff(c_443, plain, (k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_406, c_19])).
% 5.33/2.51  tff(c_4, plain, (![A_1]: (k2_zfmisc_1(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.33/2.51  tff(c_126, plain, (![A_1, C_18]: (k3_zfmisc_1(A_1, k1_xboole_0, C_18)=k2_zfmisc_1(k1_xboole_0, C_18))), inference(superposition, [status(thm), theory('equality')], [c_4, c_98])).
% 5.33/2.51  tff(c_136, plain, (![A_1, C_18]: (k3_zfmisc_1(A_1, k1_xboole_0, C_18)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_126])).
% 5.33/2.51  tff(c_437, plain, (![A_1, C_18]: (k3_zfmisc_1(A_1, '#skF_2', C_18)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_406, c_406, c_136])).
% 5.33/2.51  tff(c_526, plain, (k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_437, c_18])).
% 5.33/2.51  tff(c_528, plain, $false, inference(negUnitSimplification, [status(thm)], [c_443, c_526])).
% 5.33/2.51  tff(c_529, plain, (k1_xboole_0='#skF_3' | k2_relat_1(k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6'))='#skF_3'), inference(splitRight, [status(thm)], [c_273])).
% 5.33/2.51  tff(c_561, plain, (k2_relat_1(k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6'))='#skF_3'), inference(splitLeft, [status(thm)], [c_529])).
% 5.33/2.51  tff(c_107, plain, (![A_16, B_17, C_18]: (k2_relat_1(k3_zfmisc_1(A_16, B_17, C_18))=C_18 | k1_xboole_0=C_18 | k2_zfmisc_1(A_16, B_17)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_98, c_8])).
% 5.33/2.51  tff(c_565, plain, ('#skF_6'='#skF_3' | k1_xboole_0='#skF_6' | k2_zfmisc_1('#skF_4', '#skF_5')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_561, c_107])).
% 5.33/2.51  tff(c_572, plain, (k2_zfmisc_1('#skF_4', '#skF_5')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_565])).
% 5.33/2.51  tff(c_701, plain, (k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_572, c_2])).
% 5.33/2.51  tff(c_703, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_701])).
% 5.33/2.51  tff(c_687, plain, (![C_7]: (k3_zfmisc_1('#skF_4', '#skF_5', C_7)=k2_zfmisc_1(k1_xboole_0, C_7))), inference(superposition, [status(thm), theory('equality')], [c_572, c_12])).
% 5.33/2.51  tff(c_700, plain, (![C_7]: (k3_zfmisc_1('#skF_4', '#skF_5', C_7)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_687])).
% 5.33/2.51  tff(c_771, plain, (![C_7]: (k3_zfmisc_1('#skF_4', '#skF_5', C_7)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_703, c_700])).
% 5.33/2.51  tff(c_716, plain, (k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_703, c_19])).
% 5.33/2.51  tff(c_777, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_771, c_716])).
% 5.33/2.51  tff(c_778, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_701])).
% 5.33/2.51  tff(c_786, plain, (![A_1, C_18]: (k3_zfmisc_1(A_1, '#skF_5', C_18)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_778, c_778, c_136])).
% 5.33/2.51  tff(c_792, plain, (k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_778, c_19])).
% 5.33/2.51  tff(c_864, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_786, c_792])).
% 5.33/2.51  tff(c_866, plain, (k2_zfmisc_1('#skF_4', '#skF_5')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_565])).
% 5.33/2.51  tff(c_865, plain, (k1_xboole_0='#skF_6' | '#skF_6'='#skF_3'), inference(splitRight, [status(thm)], [c_565])).
% 5.33/2.51  tff(c_867, plain, ('#skF_6'='#skF_3'), inference(splitLeft, [status(thm)], [c_865])).
% 5.33/2.51  tff(c_530, plain, (k2_zfmisc_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_273])).
% 5.33/2.51  tff(c_10, plain, (![A_3, B_4]: (k1_relat_1(k2_zfmisc_1(A_3, B_4))=A_3 | k1_xboole_0=B_4 | k1_xboole_0=A_3)), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.33/2.51  tff(c_532, plain, (![A_49, B_50, C_51]: (k1_relat_1(k3_zfmisc_1(A_49, B_50, C_51))=k2_zfmisc_1(A_49, B_50) | k1_xboole_0=C_51 | k2_zfmisc_1(A_49, B_50)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_98, c_10])).
% 5.33/2.51  tff(c_553, plain, (k1_relat_1(k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6'))=k2_zfmisc_1('#skF_1', '#skF_2') | k1_xboole_0='#skF_3' | k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_18, c_532])).
% 5.33/2.51  tff(c_560, plain, (k1_relat_1(k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6'))=k2_zfmisc_1('#skF_1', '#skF_2') | k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_530, c_553])).
% 5.33/2.51  tff(c_875, plain, (k1_relat_1(k3_zfmisc_1('#skF_4', '#skF_5', '#skF_3'))=k2_zfmisc_1('#skF_1', '#skF_2') | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_867, c_560])).
% 5.33/2.51  tff(c_876, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_875])).
% 5.33/2.51  tff(c_117, plain, (![A_16, B_17]: (k3_zfmisc_1(A_16, B_17, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_98, c_4])).
% 5.33/2.51  tff(c_885, plain, (![A_16, B_17]: (k3_zfmisc_1(A_16, B_17, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_876, c_876, c_117])).
% 5.33/2.51  tff(c_870, plain, (k3_zfmisc_1('#skF_4', '#skF_5', '#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_867, c_19])).
% 5.33/2.51  tff(c_877, plain, (k3_zfmisc_1('#skF_4', '#skF_5', '#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_876, c_870])).
% 5.33/2.51  tff(c_1007, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_885, c_877])).
% 5.33/2.51  tff(c_1009, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_875])).
% 5.33/2.51  tff(c_1008, plain, (k1_relat_1(k3_zfmisc_1('#skF_4', '#skF_5', '#skF_3'))=k2_zfmisc_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_875])).
% 5.33/2.51  tff(c_110, plain, (![A_16, B_17, C_18]: (k1_relat_1(k3_zfmisc_1(A_16, B_17, C_18))=k2_zfmisc_1(A_16, B_17) | k1_xboole_0=C_18 | k2_zfmisc_1(A_16, B_17)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_98, c_10])).
% 5.33/2.51  tff(c_1027, plain, (k2_zfmisc_1('#skF_1', '#skF_2')=k2_zfmisc_1('#skF_4', '#skF_5') | k1_xboole_0='#skF_3' | k2_zfmisc_1('#skF_4', '#skF_5')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1008, c_110])).
% 5.33/2.51  tff(c_1033, plain, (k2_zfmisc_1('#skF_1', '#skF_2')=k2_zfmisc_1('#skF_4', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_866, c_1009, c_1027])).
% 5.33/2.51  tff(c_1068, plain, (k1_relat_1(k2_zfmisc_1('#skF_4', '#skF_5'))='#skF_1' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_1033, c_10])).
% 5.33/2.51  tff(c_1129, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_1068])).
% 5.33/2.51  tff(c_1132, plain, (k2_zfmisc_1('#skF_4', '#skF_5')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1129, c_866])).
% 5.33/2.51  tff(c_1143, plain, (![B_2]: (k2_zfmisc_1('#skF_1', B_2)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1129, c_1129, c_6])).
% 5.33/2.51  tff(c_1169, plain, (k2_zfmisc_1('#skF_4', '#skF_5')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1143, c_1033])).
% 5.33/2.51  tff(c_1171, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1132, c_1169])).
% 5.33/2.51  tff(c_1172, plain, (k1_xboole_0='#skF_2' | k1_relat_1(k2_zfmisc_1('#skF_4', '#skF_5'))='#skF_1'), inference(splitRight, [status(thm)], [c_1068])).
% 5.33/2.51  tff(c_1174, plain, (k1_relat_1(k2_zfmisc_1('#skF_4', '#skF_5'))='#skF_1'), inference(splitLeft, [status(thm)], [c_1172])).
% 5.33/2.51  tff(c_1178, plain, ('#skF_1'='#skF_4' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_1174, c_10])).
% 5.33/2.51  tff(c_1184, plain, (k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_42, c_1178])).
% 5.33/2.51  tff(c_1310, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_1184])).
% 5.33/2.51  tff(c_1326, plain, (![B_2]: (k2_zfmisc_1('#skF_4', B_2)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1310, c_1310, c_6])).
% 5.33/2.51  tff(c_1315, plain, (k2_zfmisc_1('#skF_4', '#skF_5')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1310, c_866])).
% 5.33/2.51  tff(c_1363, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1326, c_1315])).
% 5.33/2.51  tff(c_1364, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_1184])).
% 5.33/2.51  tff(c_1381, plain, (![A_1]: (k2_zfmisc_1(A_1, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1364, c_1364, c_4])).
% 5.33/2.51  tff(c_1371, plain, (k2_zfmisc_1('#skF_4', '#skF_5')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_1364, c_866])).
% 5.33/2.51  tff(c_1413, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1381, c_1371])).
% 5.33/2.51  tff(c_1414, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_1172])).
% 5.33/2.51  tff(c_1419, plain, (k2_zfmisc_1('#skF_4', '#skF_5')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1414, c_866])).
% 5.33/2.51  tff(c_1429, plain, (![A_1]: (k2_zfmisc_1(A_1, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1414, c_1414, c_4])).
% 5.33/2.51  tff(c_1435, plain, (k2_zfmisc_1('#skF_4', '#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1429, c_1033])).
% 5.33/2.51  tff(c_1479, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1419, c_1435])).
% 5.33/2.51  tff(c_1480, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_865])).
% 5.33/2.51  tff(c_1489, plain, (![A_16, B_17]: (k3_zfmisc_1(A_16, B_17, '#skF_6')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1480, c_1480, c_117])).
% 5.33/2.51  tff(c_1493, plain, (k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_1480, c_19])).
% 5.33/2.51  tff(c_1557, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1489, c_1493])).
% 5.33/2.51  tff(c_1558, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_529])).
% 5.33/2.51  tff(c_1570, plain, (k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1558, c_19])).
% 5.33/2.51  tff(c_1566, plain, (![A_16, B_17]: (k3_zfmisc_1(A_16, B_17, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1558, c_1558, c_117])).
% 5.33/2.51  tff(c_1650, plain, (k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1566, c_18])).
% 5.33/2.51  tff(c_1652, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1570, c_1650])).
% 5.33/2.51  tff(c_1653, plain, ('#skF_5'!='#skF_2' | '#skF_6'!='#skF_3'), inference(splitRight, [status(thm)], [c_14])).
% 5.33/2.51  tff(c_1664, plain, ('#skF_6'!='#skF_3'), inference(splitLeft, [status(thm)], [c_1653])).
% 5.33/2.51  tff(c_1654, plain, ('#skF_1'='#skF_4'), inference(splitRight, [status(thm)], [c_14])).
% 5.33/2.51  tff(c_1659, plain, (k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')=k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1654, c_18])).
% 5.33/2.51  tff(c_1721, plain, (![A_93, B_94, C_95]: (k2_zfmisc_1(k2_zfmisc_1(A_93, B_94), C_95)=k3_zfmisc_1(A_93, B_94, C_95))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.33/2.51  tff(c_1874, plain, (![A_109, B_110, C_111]: (k2_relat_1(k3_zfmisc_1(A_109, B_110, C_111))=C_111 | k1_xboole_0=C_111 | k2_zfmisc_1(A_109, B_110)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1721, c_8])).
% 5.33/2.51  tff(c_1895, plain, (k2_relat_1(k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3'))='#skF_6' | k1_xboole_0='#skF_6' | k2_zfmisc_1('#skF_4', '#skF_5')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1659, c_1874])).
% 5.33/2.51  tff(c_1903, plain, (k2_zfmisc_1('#skF_4', '#skF_5')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_1895])).
% 5.33/2.51  tff(c_1924, plain, (k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_1903, c_2])).
% 5.33/2.51  tff(c_1926, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_1924])).
% 5.33/2.51  tff(c_1756, plain, (![B_2, C_95]: (k3_zfmisc_1(k1_xboole_0, B_2, C_95)=k2_zfmisc_1(k1_xboole_0, C_95))), inference(superposition, [status(thm), theory('equality')], [c_6, c_1721])).
% 5.33/2.51  tff(c_1760, plain, (![B_2, C_95]: (k3_zfmisc_1(k1_xboole_0, B_2, C_95)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_1756])).
% 5.33/2.51  tff(c_1930, plain, (![B_2, C_95]: (k3_zfmisc_1('#skF_4', B_2, C_95)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1926, c_1926, c_1760])).
% 5.33/2.51  tff(c_1665, plain, (k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1659, c_19])).
% 5.33/2.51  tff(c_1936, plain, (k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1926, c_1665])).
% 5.33/2.51  tff(c_2042, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1930, c_1936])).
% 5.33/2.51  tff(c_2043, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_1924])).
% 5.33/2.51  tff(c_1749, plain, (![A_1, C_95]: (k3_zfmisc_1(A_1, k1_xboole_0, C_95)=k2_zfmisc_1(k1_xboole_0, C_95))), inference(superposition, [status(thm), theory('equality')], [c_4, c_1721])).
% 5.33/2.51  tff(c_1759, plain, (![A_1, C_95]: (k3_zfmisc_1(A_1, k1_xboole_0, C_95)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_1749])).
% 5.33/2.51  tff(c_2052, plain, (![A_1, C_95]: (k3_zfmisc_1(A_1, '#skF_5', C_95)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2043, c_2043, c_1759])).
% 5.33/2.51  tff(c_2128, plain, (k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_2052, c_1659])).
% 5.33/2.51  tff(c_2057, plain, (k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_2043, c_1665])).
% 5.33/2.51  tff(c_2212, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2128, c_2057])).
% 5.33/2.51  tff(c_2213, plain, (k1_xboole_0='#skF_6' | k2_relat_1(k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3'))='#skF_6'), inference(splitRight, [status(thm)], [c_1895])).
% 5.33/2.51  tff(c_2215, plain, (k2_relat_1(k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3'))='#skF_6'), inference(splitLeft, [status(thm)], [c_2213])).
% 5.33/2.51  tff(c_1733, plain, (![A_93, B_94, C_95]: (k2_relat_1(k3_zfmisc_1(A_93, B_94, C_95))=C_95 | k1_xboole_0=C_95 | k2_zfmisc_1(A_93, B_94)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1721, c_8])).
% 5.33/2.51  tff(c_2219, plain, ('#skF_6'='#skF_3' | k1_xboole_0='#skF_3' | k2_zfmisc_1('#skF_4', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_2215, c_1733])).
% 5.33/2.51  tff(c_2225, plain, (k1_xboole_0='#skF_3' | k2_zfmisc_1('#skF_4', '#skF_2')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_1664, c_2219])).
% 5.33/2.51  tff(c_2258, plain, (k2_zfmisc_1('#skF_4', '#skF_2')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_2225])).
% 5.33/2.51  tff(c_2279, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_2258, c_2])).
% 5.33/2.51  tff(c_2281, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_2279])).
% 5.33/2.51  tff(c_2296, plain, (![B_2]: (k2_zfmisc_1('#skF_4', B_2)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2281, c_2281, c_6])).
% 5.33/2.51  tff(c_2214, plain, (k2_zfmisc_1('#skF_4', '#skF_5')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_1895])).
% 5.33/2.51  tff(c_2285, plain, (k2_zfmisc_1('#skF_4', '#skF_5')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2281, c_2214])).
% 5.33/2.51  tff(c_2324, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2296, c_2285])).
% 5.33/2.51  tff(c_2325, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_2279])).
% 5.33/2.51  tff(c_2265, plain, (![C_7]: (k3_zfmisc_1('#skF_4', '#skF_2', C_7)=k2_zfmisc_1(k1_xboole_0, C_7))), inference(superposition, [status(thm), theory('equality')], [c_2258, c_12])).
% 5.33/2.51  tff(c_2278, plain, (![C_7]: (k3_zfmisc_1('#skF_4', '#skF_2', C_7)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_2265])).
% 5.33/2.51  tff(c_2551, plain, (![C_7]: (k3_zfmisc_1('#skF_4', '#skF_2', C_7)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2325, c_2278])).
% 5.33/2.51  tff(c_2496, plain, (k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2325, c_1665])).
% 5.33/2.51  tff(c_2557, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2551, c_2496])).
% 5.33/2.51  tff(c_2558, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_2225])).
% 5.33/2.51  tff(c_1740, plain, (![A_93, B_94]: (k3_zfmisc_1(A_93, B_94, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1721, c_4])).
% 5.33/2.51  tff(c_2566, plain, (![A_93, B_94]: (k3_zfmisc_1(A_93, B_94, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2558, c_2558, c_1740])).
% 5.33/2.51  tff(c_2570, plain, (k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2558, c_1665])).
% 5.33/2.51  tff(c_2632, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2566, c_2570])).
% 5.33/2.51  tff(c_2633, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_2213])).
% 5.33/2.51  tff(c_2644, plain, (k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_2633, c_1665])).
% 5.33/2.51  tff(c_2640, plain, (![A_93, B_94]: (k3_zfmisc_1(A_93, B_94, '#skF_6')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2633, c_2633, c_1740])).
% 5.33/2.51  tff(c_2752, plain, (k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_2640, c_1659])).
% 5.33/2.51  tff(c_2754, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2644, c_2752])).
% 5.33/2.51  tff(c_2756, plain, ('#skF_6'='#skF_3'), inference(splitRight, [status(thm)], [c_1653])).
% 5.33/2.51  tff(c_2773, plain, (k3_zfmisc_1('#skF_4', '#skF_5', '#skF_3')=k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2756, c_1659])).
% 5.33/2.51  tff(c_2885, plain, (![A_170, B_171]: (k2_relat_1(k2_zfmisc_1(A_170, B_171))=B_171 | k1_xboole_0=B_171 | k1_xboole_0=A_170)), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.33/2.51  tff(c_2927, plain, (![A_175, B_176, C_177]: (k2_relat_1(k3_zfmisc_1(A_175, B_176, C_177))=C_177 | k1_xboole_0=C_177 | k2_zfmisc_1(A_175, B_176)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_12, c_2885])).
% 5.33/2.51  tff(c_2945, plain, (k2_relat_1(k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3'))='#skF_3' | k1_xboole_0='#skF_3' | k2_zfmisc_1('#skF_4', '#skF_5')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_2773, c_2927])).
% 5.33/2.51  tff(c_3001, plain, (k2_zfmisc_1('#skF_4', '#skF_5')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_2945])).
% 5.33/2.51  tff(c_3022, plain, (k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_3001, c_2])).
% 5.33/2.51  tff(c_3024, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_3022])).
% 5.33/2.51  tff(c_2779, plain, (![A_159, B_160, C_161]: (k2_zfmisc_1(k2_zfmisc_1(A_159, B_160), C_161)=k3_zfmisc_1(A_159, B_160, C_161))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.33/2.51  tff(c_2808, plain, (![B_2, C_161]: (k3_zfmisc_1(k1_xboole_0, B_2, C_161)=k2_zfmisc_1(k1_xboole_0, C_161))), inference(superposition, [status(thm), theory('equality')], [c_6, c_2779])).
% 5.33/2.51  tff(c_2812, plain, (![B_2, C_161]: (k3_zfmisc_1(k1_xboole_0, B_2, C_161)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_2808])).
% 5.33/2.51  tff(c_3029, plain, (![B_2, C_161]: (k3_zfmisc_1('#skF_4', B_2, C_161)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3024, c_3024, c_2812])).
% 5.33/2.51  tff(c_2757, plain, (k3_zfmisc_1('#skF_4', '#skF_5', '#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2756, c_19])).
% 5.33/2.51  tff(c_2774, plain, (k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2773, c_2757])).
% 5.33/2.51  tff(c_3033, plain, (k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3024, c_2774])).
% 5.33/2.51  tff(c_3117, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3029, c_3033])).
% 5.33/2.51  tff(c_3118, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_3022])).
% 5.33/2.51  tff(c_2801, plain, (![A_1, C_161]: (k3_zfmisc_1(A_1, k1_xboole_0, C_161)=k2_zfmisc_1(k1_xboole_0, C_161))), inference(superposition, [status(thm), theory('equality')], [c_4, c_2779])).
% 5.33/2.51  tff(c_2811, plain, (![A_1, C_161]: (k3_zfmisc_1(A_1, k1_xboole_0, C_161)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_2801])).
% 5.33/2.51  tff(c_3128, plain, (![A_1, C_161]: (k3_zfmisc_1(A_1, '#skF_5', C_161)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_3118, c_3118, c_2811])).
% 5.33/2.51  tff(c_3224, plain, (k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_3128, c_2773])).
% 5.33/2.51  tff(c_3131, plain, (k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_3118, c_2774])).
% 5.33/2.51  tff(c_3262, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3224, c_3131])).
% 5.33/2.51  tff(c_3264, plain, (k2_zfmisc_1('#skF_4', '#skF_5')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_2945])).
% 5.33/2.51  tff(c_2823, plain, (![A_164, B_165]: (k1_relat_1(k2_zfmisc_1(A_164, B_165))=A_164 | k1_xboole_0=B_165 | k1_xboole_0=A_164)), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.33/2.51  tff(c_3279, plain, (![A_198, B_199, C_200]: (k1_relat_1(k3_zfmisc_1(A_198, B_199, C_200))=k2_zfmisc_1(A_198, B_199) | k1_xboole_0=C_200 | k2_zfmisc_1(A_198, B_199)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_12, c_2823])).
% 5.33/2.51  tff(c_3300, plain, (k1_relat_1(k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3'))=k2_zfmisc_1('#skF_4', '#skF_5') | k1_xboole_0='#skF_3' | k2_zfmisc_1('#skF_4', '#skF_5')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_2773, c_3279])).
% 5.33/2.51  tff(c_3307, plain, (k1_relat_1(k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3'))=k2_zfmisc_1('#skF_4', '#skF_5') | k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_3264, c_3300])).
% 5.33/2.51  tff(c_3308, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_3307])).
% 5.33/2.51  tff(c_2792, plain, (![A_159, B_160]: (k3_zfmisc_1(A_159, B_160, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2779, c_4])).
% 5.33/2.51  tff(c_3317, plain, (![A_159, B_160]: (k3_zfmisc_1(A_159, B_160, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3308, c_3308, c_2792])).
% 5.33/2.51  tff(c_3318, plain, (k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_3308, c_2774])).
% 5.33/2.51  tff(c_3403, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3317, c_3318])).
% 5.33/2.51  tff(c_3405, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_3307])).
% 5.33/2.51  tff(c_3404, plain, (k1_relat_1(k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3'))=k2_zfmisc_1('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_3307])).
% 5.33/2.51  tff(c_2832, plain, (![A_5, B_6, C_7]: (k1_relat_1(k3_zfmisc_1(A_5, B_6, C_7))=k2_zfmisc_1(A_5, B_6) | k1_xboole_0=C_7 | k2_zfmisc_1(A_5, B_6)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_12, c_2823])).
% 5.33/2.51  tff(c_3409, plain, (k2_zfmisc_1('#skF_4', '#skF_5')=k2_zfmisc_1('#skF_4', '#skF_2') | k1_xboole_0='#skF_3' | k2_zfmisc_1('#skF_4', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_3404, c_2832])).
% 5.33/2.51  tff(c_3415, plain, (k2_zfmisc_1('#skF_4', '#skF_5')=k2_zfmisc_1('#skF_4', '#skF_2') | k2_zfmisc_1('#skF_4', '#skF_2')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_3405, c_3409])).
% 5.33/2.51  tff(c_3418, plain, (k2_zfmisc_1('#skF_4', '#skF_2')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_3415])).
% 5.33/2.51  tff(c_3439, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_3418, c_2])).
% 5.33/2.51  tff(c_3441, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_3439])).
% 5.33/2.51  tff(c_3458, plain, (![B_2]: (k2_zfmisc_1('#skF_4', B_2)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3441, c_3441, c_6])).
% 5.33/2.51  tff(c_3447, plain, (k2_zfmisc_1('#skF_4', '#skF_5')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3441, c_3264])).
% 5.33/2.51  tff(c_3487, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3458, c_3447])).
% 5.33/2.51  tff(c_3488, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_3439])).
% 5.33/2.51  tff(c_3501, plain, (![A_1, C_161]: (k3_zfmisc_1(A_1, '#skF_2', C_161)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3488, c_3488, c_2811])).
% 5.33/2.51  tff(c_3504, plain, (k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_3488, c_2774])).
% 5.33/2.51  tff(c_3594, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3501, c_3504])).
% 5.33/2.51  tff(c_3596, plain, (k2_zfmisc_1('#skF_4', '#skF_2')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_3415])).
% 5.33/2.51  tff(c_3413, plain, (k2_zfmisc_1('#skF_4', '#skF_5')=k2_zfmisc_1('#skF_4', '#skF_2') | k1_xboole_0='#skF_3' | k2_zfmisc_1('#skF_4', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_2832, c_3404])).
% 5.33/2.51  tff(c_3417, plain, (k2_zfmisc_1('#skF_4', '#skF_5')=k2_zfmisc_1('#skF_4', '#skF_2') | k2_zfmisc_1('#skF_4', '#skF_2')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_3405, c_3413])).
% 5.33/2.51  tff(c_3597, plain, (k2_zfmisc_1('#skF_4', '#skF_5')=k2_zfmisc_1('#skF_4', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_3596, c_3417])).
% 5.33/2.51  tff(c_3606, plain, (k2_relat_1(k2_zfmisc_1('#skF_4', '#skF_2'))='#skF_5' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_3597, c_8])).
% 5.33/2.51  tff(c_3714, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_3606])).
% 5.33/2.51  tff(c_3730, plain, (![B_2]: (k2_zfmisc_1('#skF_4', B_2)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3714, c_3714, c_6])).
% 5.33/2.51  tff(c_3717, plain, (k2_zfmisc_1('#skF_4', '#skF_2')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3714, c_3596])).
% 5.33/2.51  tff(c_3760, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3730, c_3717])).
% 5.33/2.51  tff(c_3762, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_3606])).
% 5.33/2.51  tff(c_2755, plain, ('#skF_5'!='#skF_2'), inference(splitRight, [status(thm)], [c_1653])).
% 5.33/2.51  tff(c_3761, plain, (k1_xboole_0='#skF_5' | k2_relat_1(k2_zfmisc_1('#skF_4', '#skF_2'))='#skF_5'), inference(splitRight, [status(thm)], [c_3606])).
% 5.33/2.51  tff(c_3763, plain, (k2_relat_1(k2_zfmisc_1('#skF_4', '#skF_2'))='#skF_5'), inference(splitLeft, [status(thm)], [c_3761])).
% 5.33/2.51  tff(c_3771, plain, ('#skF_5'='#skF_2' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_8, c_3763])).
% 5.33/2.51  tff(c_3775, plain, (k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_3762, c_2755, c_3771])).
% 5.33/2.51  tff(c_3820, plain, (![A_1]: (k2_zfmisc_1(A_1, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3775, c_3775, c_4])).
% 5.33/2.51  tff(c_3808, plain, (k2_zfmisc_1('#skF_4', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_3775, c_3596])).
% 5.33/2.51  tff(c_3851, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3820, c_3808])).
% 5.33/2.51  tff(c_3852, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_3761])).
% 5.33/2.51  tff(c_3859, plain, (k2_zfmisc_1('#skF_4', '#skF_2')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_3852, c_3596])).
% 5.33/2.51  tff(c_3871, plain, (![A_1]: (k2_zfmisc_1(A_1, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_3852, c_3852, c_4])).
% 5.33/2.51  tff(c_3878, plain, (k2_zfmisc_1('#skF_4', '#skF_2')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_3871, c_3597])).
% 5.33/2.51  tff(c_3880, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3859, c_3878])).
% 5.33/2.51  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.33/2.51  
% 5.33/2.51  Inference rules
% 5.33/2.51  ----------------------
% 5.33/2.51  #Ref     : 0
% 5.33/2.51  #Sup     : 867
% 5.33/2.51  #Fact    : 0
% 5.33/2.51  #Define  : 0
% 5.33/2.51  #Split   : 34
% 5.33/2.51  #Chain   : 0
% 5.33/2.51  #Close   : 0
% 5.33/2.51  
% 5.33/2.51  Ordering : KBO
% 5.33/2.51  
% 5.33/2.51  Simplification rules
% 5.33/2.51  ----------------------
% 5.33/2.51  #Subsume      : 21
% 5.33/2.51  #Demod        : 1217
% 5.33/2.51  #Tautology    : 626
% 5.33/2.51  #SimpNegUnit  : 56
% 5.33/2.51  #BackRed      : 516
% 5.33/2.51  
% 5.33/2.51  #Partial instantiations: 0
% 5.33/2.51  #Strategies tried      : 1
% 5.33/2.51  
% 5.33/2.51  Timing (in seconds)
% 5.33/2.51  ----------------------
% 5.33/2.51  Preprocessing        : 0.44
% 5.33/2.51  Parsing              : 0.22
% 5.33/2.51  CNF conversion       : 0.03
% 5.33/2.51  Main loop            : 1.14
% 5.33/2.52  Inferencing          : 0.38
% 5.33/2.52  Reduction            : 0.41
% 5.33/2.52  Demodulation         : 0.29
% 5.33/2.52  BG Simplification    : 0.05
% 5.33/2.52  Subsumption          : 0.17
% 5.33/2.52  Abstraction          : 0.07
% 5.33/2.52  MUC search           : 0.00
% 5.33/2.52  Cooper               : 0.00
% 5.33/2.52  Total                : 1.70
% 5.33/2.52  Index Insertion      : 0.00
% 5.33/2.52  Index Deletion       : 0.00
% 5.33/2.52  Index Matching       : 0.00
% 5.33/2.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
