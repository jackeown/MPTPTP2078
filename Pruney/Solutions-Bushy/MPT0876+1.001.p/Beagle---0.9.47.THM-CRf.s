%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0876+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:00 EST 2020

% Result     : Theorem 3.77s
% Output     : CNFRefutation 3.97s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 596 expanded)
%              Number of leaves         :   16 ( 184 expanded)
%              Depth                    :   15
%              Number of atoms          :  209 (1714 expanded)
%              Number of equality atoms :  200 (1705 expanded)
%              Maximal formula depth    :   14 (   4 average)
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

tff(f_57,negated_conjecture,(
    ~ ! [A,B,C,D,E,F] :
        ( k3_zfmisc_1(A,B,C) = k3_zfmisc_1(D,E,F)
       => ( A = k1_xboole_0
          | B = k1_xboole_0
          | C = k1_xboole_0
          | ( A = D
            & B = E
            & C = F ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_mcart_1)).

tff(f_26,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_42,axiom,(
    ! [A,B,C,D] :
      ( k2_zfmisc_1(A,B) = k2_zfmisc_1(C,D)
     => ( A = k1_xboole_0
        | B = k1_xboole_0
        | ( A = C
          & B = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(c_14,plain,
    ( '#skF_6' != '#skF_3'
    | '#skF_5' != '#skF_2'
    | '#skF_1' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_45,plain,(
    '#skF_1' != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_14])).

tff(c_20,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_18,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] : k2_zfmisc_1(k2_zfmisc_1(A_1,B_2),C_3) = k3_zfmisc_1(A_1,B_2,C_3) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_16,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_22,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = k3_zfmisc_1('#skF_4','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_165,plain,(
    ! [D_26,B_27,A_28,C_29] :
      ( D_26 = B_27
      | k1_xboole_0 = B_27
      | k1_xboole_0 = A_28
      | k2_zfmisc_1(C_29,D_26) != k2_zfmisc_1(A_28,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_326,plain,(
    ! [B_52,D_51,C_50,C_53,A_54] :
      ( D_51 = C_53
      | k1_xboole_0 = C_53
      | k2_zfmisc_1(A_54,B_52) = k1_xboole_0
      | k3_zfmisc_1(A_54,B_52,C_53) != k2_zfmisc_1(C_50,D_51) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_165])).

tff(c_344,plain,(
    ! [D_51,C_50] :
      ( D_51 = '#skF_3'
      | k1_xboole_0 = '#skF_3'
      | k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0
      | k3_zfmisc_1('#skF_4','#skF_5','#skF_6') != k2_zfmisc_1(C_50,D_51) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_326])).

tff(c_355,plain,(
    ! [D_51,C_50] :
      ( D_51 = '#skF_3'
      | k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0
      | k3_zfmisc_1('#skF_4','#skF_5','#skF_6') != k2_zfmisc_1(C_50,D_51) ) ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_344])).

tff(c_386,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_355])).

tff(c_4,plain,(
    ! [B_5,A_4] :
      ( k1_xboole_0 = B_5
      | k1_xboole_0 = A_4
      | k2_zfmisc_1(A_4,B_5) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_408,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_386,c_4])).

tff(c_418,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_18,c_408])).

tff(c_433,plain,(
    ! [D_62,C_63] :
      ( D_62 = '#skF_3'
      | k3_zfmisc_1('#skF_4','#skF_5','#skF_6') != k2_zfmisc_1(C_63,D_62) ) ),
    inference(splitRight,[status(thm)],[c_355])).

tff(c_436,plain,(
    ! [C_3,A_1,B_2] :
      ( C_3 = '#skF_3'
      | k3_zfmisc_1(A_1,B_2,C_3) != k3_zfmisc_1('#skF_4','#skF_5','#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_433])).

tff(c_446,plain,(
    '#skF_6' = '#skF_3' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_436])).

tff(c_420,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_355])).

tff(c_191,plain,(
    ! [C_30,A_31,B_32,D_33] :
      ( C_30 = A_31
      | k1_xboole_0 = B_32
      | k1_xboole_0 = A_31
      | k2_zfmisc_1(C_30,D_33) != k2_zfmisc_1(A_31,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_356,plain,(
    ! [A_58,B_56,D_59,C_57,C_55] :
      ( k2_zfmisc_1(A_58,B_56) = C_55
      | k1_xboole_0 = C_57
      | k2_zfmisc_1(A_58,B_56) = k1_xboole_0
      | k3_zfmisc_1(A_58,B_56,C_57) != k2_zfmisc_1(C_55,D_59) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_191])).

tff(c_374,plain,(
    ! [C_55,D_59] :
      ( k2_zfmisc_1('#skF_1','#skF_2') = C_55
      | k1_xboole_0 = '#skF_3'
      | k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0
      | k3_zfmisc_1('#skF_4','#skF_5','#skF_6') != k2_zfmisc_1(C_55,D_59) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_356])).

tff(c_385,plain,(
    ! [C_55,D_59] :
      ( k2_zfmisc_1('#skF_1','#skF_2') = C_55
      | k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0
      | k3_zfmisc_1('#skF_4','#skF_5','#skF_6') != k2_zfmisc_1(C_55,D_59) ) ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_374])).

tff(c_422,plain,(
    ! [C_60,D_61] :
      ( k2_zfmisc_1('#skF_1','#skF_2') = C_60
      | k3_zfmisc_1('#skF_4','#skF_5','#skF_6') != k2_zfmisc_1(C_60,D_61) ) ),
    inference(negUnitSimplification,[status(thm)],[c_420,c_385])).

tff(c_425,plain,(
    ! [A_1,B_2,C_3] :
      ( k2_zfmisc_1(A_1,B_2) = k2_zfmisc_1('#skF_1','#skF_2')
      | k3_zfmisc_1(A_1,B_2,C_3) != k3_zfmisc_1('#skF_4','#skF_5','#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_422])).

tff(c_553,plain,(
    ! [A_1,B_2,C_3] :
      ( k2_zfmisc_1(A_1,B_2) = k2_zfmisc_1('#skF_1','#skF_2')
      | k3_zfmisc_1(A_1,B_2,C_3) != k3_zfmisc_1('#skF_4','#skF_5','#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_446,c_425])).

tff(c_556,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = k2_zfmisc_1('#skF_4','#skF_5') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_553])).

tff(c_10,plain,(
    ! [D_9,B_7,A_6,C_8] :
      ( D_9 = B_7
      | k1_xboole_0 = B_7
      | k1_xboole_0 = A_6
      | k2_zfmisc_1(C_8,D_9) != k2_zfmisc_1(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_598,plain,(
    ! [D_9,C_8] :
      ( D_9 = '#skF_2'
      | k1_xboole_0 = '#skF_2'
      | k1_xboole_0 = '#skF_1'
      | k2_zfmisc_1(C_8,D_9) != k2_zfmisc_1('#skF_4','#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_556,c_10])).

tff(c_609,plain,(
    ! [D_9,C_8] :
      ( D_9 = '#skF_2'
      | k2_zfmisc_1(C_8,D_9) != k2_zfmisc_1('#skF_4','#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_18,c_598])).

tff(c_656,plain,(
    '#skF_5' = '#skF_2' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_609])).

tff(c_12,plain,(
    ! [C_8,A_6,B_7,D_9] :
      ( C_8 = A_6
      | k1_xboole_0 = B_7
      | k1_xboole_0 = A_6
      | k2_zfmisc_1(C_8,D_9) != k2_zfmisc_1(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_592,plain,(
    ! [C_8,D_9] :
      ( C_8 = '#skF_1'
      | k1_xboole_0 = '#skF_2'
      | k1_xboole_0 = '#skF_1'
      | k2_zfmisc_1(C_8,D_9) != k2_zfmisc_1('#skF_4','#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_556,c_12])).

tff(c_608,plain,(
    ! [C_8,D_9] :
      ( C_8 = '#skF_1'
      | k2_zfmisc_1(C_8,D_9) != k2_zfmisc_1('#skF_4','#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_18,c_592])).

tff(c_684,plain,(
    ! [C_8,D_9] :
      ( C_8 = '#skF_1'
      | k2_zfmisc_1(C_8,D_9) != k2_zfmisc_1('#skF_4','#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_656,c_608])).

tff(c_687,plain,(
    '#skF_1' = '#skF_4' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_684])).

tff(c_689,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_45,c_687])).

tff(c_691,plain,(
    '#skF_1' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_14])).

tff(c_692,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_691,c_20])).

tff(c_690,plain,
    ( '#skF_5' != '#skF_2'
    | '#skF_6' != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_14])).

tff(c_697,plain,(
    '#skF_6' != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_690])).

tff(c_709,plain,(
    k3_zfmisc_1('#skF_4','#skF_5','#skF_6') = k3_zfmisc_1('#skF_4','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_691,c_22])).

tff(c_843,plain,(
    ! [D_105,B_106,A_107,C_108] :
      ( D_105 = B_106
      | k1_xboole_0 = B_106
      | k1_xboole_0 = A_107
      | k2_zfmisc_1(C_108,D_105) != k2_zfmisc_1(A_107,B_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_977,plain,(
    ! [C_126,C_128,D_125,B_127,A_129] :
      ( D_125 = C_128
      | k1_xboole_0 = C_128
      | k2_zfmisc_1(A_129,B_127) = k1_xboole_0
      | k3_zfmisc_1(A_129,B_127,C_128) != k2_zfmisc_1(C_126,D_125) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_843])).

tff(c_995,plain,(
    ! [D_125,C_126] :
      ( D_125 = '#skF_6'
      | k1_xboole_0 = '#skF_6'
      | k2_zfmisc_1('#skF_4','#skF_5') = k1_xboole_0
      | k3_zfmisc_1('#skF_4','#skF_2','#skF_3') != k2_zfmisc_1(C_126,D_125) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_709,c_977])).

tff(c_1016,plain,(
    k2_zfmisc_1('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_995])).

tff(c_1039,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_1016,c_4])).

tff(c_1048,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_692,c_1039])).

tff(c_8,plain,(
    ! [B_5] : k2_zfmisc_1(k1_xboole_0,B_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1036,plain,(
    ! [C_3] : k3_zfmisc_1('#skF_4','#skF_5',C_3) = k2_zfmisc_1(k1_xboole_0,C_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_1016,c_2])).

tff(c_1045,plain,(
    ! [C_3] : k3_zfmisc_1('#skF_4','#skF_5',C_3) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_1036])).

tff(c_1158,plain,(
    ! [C_3] : k3_zfmisc_1('#skF_4','#skF_5',C_3) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1048,c_1045])).

tff(c_1159,plain,(
    k3_zfmisc_1('#skF_4','#skF_2','#skF_3') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1158,c_709])).

tff(c_714,plain,(
    ! [A_89,B_90,C_91] : k2_zfmisc_1(k2_zfmisc_1(A_89,B_90),C_91) = k3_zfmisc_1(A_89,B_90,C_91) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_819,plain,(
    ! [C_102,A_103,B_104] :
      ( k1_xboole_0 = C_102
      | k2_zfmisc_1(A_103,B_104) = k1_xboole_0
      | k3_zfmisc_1(A_103,B_104,C_102) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_714,c_4])).

tff(c_831,plain,
    ( k1_xboole_0 = '#skF_6'
    | k2_zfmisc_1('#skF_4','#skF_5') = k1_xboole_0
    | k3_zfmisc_1('#skF_4','#skF_2','#skF_3') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_709,c_819])).

tff(c_838,plain,(
    k3_zfmisc_1('#skF_4','#skF_2','#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_831])).

tff(c_1087,plain,(
    k3_zfmisc_1('#skF_4','#skF_2','#skF_3') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1048,c_838])).

tff(c_1261,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1159,c_1087])).

tff(c_1262,plain,(
    ! [D_125,C_126] :
      ( k1_xboole_0 = '#skF_6'
      | D_125 = '#skF_6'
      | k3_zfmisc_1('#skF_4','#skF_2','#skF_3') != k2_zfmisc_1(C_126,D_125) ) ),
    inference(splitRight,[status(thm)],[c_995])).

tff(c_1264,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_1262])).

tff(c_6,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_727,plain,(
    ! [A_89,B_90] : k3_zfmisc_1(A_89,B_90,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_714,c_6])).

tff(c_1277,plain,(
    ! [A_89,B_90] : k3_zfmisc_1(A_89,B_90,'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1264,c_1264,c_727])).

tff(c_1401,plain,(
    k3_zfmisc_1('#skF_4','#skF_2','#skF_3') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1277,c_709])).

tff(c_1272,plain,(
    k3_zfmisc_1('#skF_4','#skF_2','#skF_3') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1264,c_838])).

tff(c_1449,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1401,c_1272])).

tff(c_1452,plain,(
    ! [D_163,C_164] :
      ( D_163 = '#skF_6'
      | k3_zfmisc_1('#skF_4','#skF_2','#skF_3') != k2_zfmisc_1(C_164,D_163) ) ),
    inference(splitRight,[status(thm)],[c_1262])).

tff(c_1455,plain,(
    ! [C_3,A_1,B_2] :
      ( C_3 = '#skF_6'
      | k3_zfmisc_1(A_1,B_2,C_3) != k3_zfmisc_1('#skF_4','#skF_2','#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1452])).

tff(c_1465,plain,(
    '#skF_6' = '#skF_3' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_1455])).

tff(c_1467,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_697,c_1465])).

tff(c_1469,plain,(
    k3_zfmisc_1('#skF_4','#skF_2','#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_831])).

tff(c_723,plain,(
    ! [C_91,A_89,B_90] :
      ( k1_xboole_0 = C_91
      | k2_zfmisc_1(A_89,B_90) = k1_xboole_0
      | k3_zfmisc_1(A_89,B_90,C_91) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_714,c_4])).

tff(c_1474,plain,
    ( k1_xboole_0 = '#skF_3'
    | k2_zfmisc_1('#skF_4','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1469,c_723])).

tff(c_1479,plain,(
    k2_zfmisc_1('#skF_4','#skF_2') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_1474])).

tff(c_1493,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_1479,c_4])).

tff(c_1501,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_692,c_18,c_1493])).

tff(c_1502,plain,(
    '#skF_5' != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_690])).

tff(c_1503,plain,(
    '#skF_6' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_690])).

tff(c_1519,plain,(
    k3_zfmisc_1('#skF_4','#skF_5','#skF_3') = k3_zfmisc_1('#skF_4','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1503,c_691,c_22])).

tff(c_1585,plain,(
    ! [C_174,A_175,B_176,D_177] :
      ( C_174 = A_175
      | k1_xboole_0 = B_176
      | k1_xboole_0 = A_175
      | k2_zfmisc_1(C_174,D_177) != k2_zfmisc_1(A_175,B_176) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_2016,plain,(
    ! [B_216,A_215,B_217,C_218,A_219] :
      ( k2_zfmisc_1(A_219,B_217) = A_215
      | k1_xboole_0 = B_216
      | k1_xboole_0 = A_215
      | k3_zfmisc_1(A_219,B_217,C_218) != k2_zfmisc_1(A_215,B_216) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1585])).

tff(c_2079,plain,(
    ! [A_225,B_226] :
      ( k2_zfmisc_1('#skF_4','#skF_5') = A_225
      | k1_xboole_0 = B_226
      | k1_xboole_0 = A_225
      | k3_zfmisc_1('#skF_4','#skF_2','#skF_3') != k2_zfmisc_1(A_225,B_226) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1519,c_2016])).

tff(c_2082,plain,(
    ! [A_1,B_2,C_3] :
      ( k2_zfmisc_1(A_1,B_2) = k2_zfmisc_1('#skF_4','#skF_5')
      | k1_xboole_0 = C_3
      | k2_zfmisc_1(A_1,B_2) = k1_xboole_0
      | k3_zfmisc_1(A_1,B_2,C_3) != k3_zfmisc_1('#skF_4','#skF_2','#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_2079])).

tff(c_2092,plain,
    ( k2_zfmisc_1('#skF_4','#skF_5') = k2_zfmisc_1('#skF_4','#skF_2')
    | k1_xboole_0 = '#skF_3'
    | k2_zfmisc_1('#skF_4','#skF_2') = k1_xboole_0 ),
    inference(reflexivity,[status(thm),theory(equality)],[c_2082])).

tff(c_2093,plain,
    ( k2_zfmisc_1('#skF_4','#skF_5') = k2_zfmisc_1('#skF_4','#skF_2')
    | k2_zfmisc_1('#skF_4','#skF_2') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_2092])).

tff(c_2119,plain,(
    k2_zfmisc_1('#skF_4','#skF_2') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_2093])).

tff(c_2141,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_2119,c_4])).

tff(c_2151,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_692,c_18,c_2141])).

tff(c_2152,plain,(
    k2_zfmisc_1('#skF_4','#skF_5') = k2_zfmisc_1('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_2093])).

tff(c_2166,plain,(
    ! [D_9,C_8] :
      ( D_9 = '#skF_5'
      | k1_xboole_0 = '#skF_5'
      | k1_xboole_0 = '#skF_4'
      | k2_zfmisc_1(C_8,D_9) != k2_zfmisc_1('#skF_4','#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2152,c_10])).

tff(c_2182,plain,(
    ! [D_9,C_8] :
      ( D_9 = '#skF_5'
      | k1_xboole_0 = '#skF_5'
      | k2_zfmisc_1(C_8,D_9) != k2_zfmisc_1('#skF_4','#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_692,c_2166])).

tff(c_2265,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_2182])).

tff(c_2153,plain,(
    k2_zfmisc_1('#skF_4','#skF_2') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_2093])).

tff(c_2268,plain,(
    k2_zfmisc_1('#skF_4','#skF_2') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2265,c_2153])).

tff(c_2281,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2265,c_2265,c_6])).

tff(c_2306,plain,(
    k2_zfmisc_1('#skF_4','#skF_2') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2281,c_2152])).

tff(c_2308,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2268,c_2306])).

tff(c_2309,plain,(
    ! [D_9,C_8] :
      ( D_9 = '#skF_5'
      | k2_zfmisc_1(C_8,D_9) != k2_zfmisc_1('#skF_4','#skF_2') ) ),
    inference(splitRight,[status(thm)],[c_2182])).

tff(c_2354,plain,(
    '#skF_5' = '#skF_2' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_2309])).

tff(c_2356,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1502,c_2354])).

%------------------------------------------------------------------------------
