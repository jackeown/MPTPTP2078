%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:28 EST 2020

% Result     : Theorem 4.10s
% Output     : CNFRefutation 4.41s
% Verified   : 
% Statistics : Number of formulae       :  182 (1434 expanded)
%              Number of leaves         :   16 ( 434 expanded)
%              Depth                    :   18
%              Number of atoms          :  316 (4095 expanded)
%              Number of equality atoms :  302 (4081 expanded)
%              Maximal formula depth    :   14 (   3 average)
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

tff(f_58,negated_conjecture,(
    ~ ! [A,B,C,D,E,F] :
        ( k3_zfmisc_1(A,B,C) = k3_zfmisc_1(D,E,F)
       => ( A = k1_xboole_0
          | B = k1_xboole_0
          | C = k1_xboole_0
          | ( A = D
            & B = E
            & C = F ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_mcart_1)).

tff(f_43,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B,C,D] :
      ( k2_zfmisc_1(A,B) = k2_zfmisc_1(C,D)
     => ( A = k1_xboole_0
        | B = k1_xboole_0
        | ( A = C
          & B = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(c_20,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_18,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_14,plain,
    ( '#skF_6' != '#skF_3'
    | '#skF_5' != '#skF_2'
    | '#skF_1' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_45,plain,(
    '#skF_1' != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_14])).

tff(c_12,plain,(
    ! [A_7,B_8,C_9] : k2_zfmisc_1(k2_zfmisc_1(A_7,B_8),C_9) = k3_zfmisc_1(A_7,B_8,C_9) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_16,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_22,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = k3_zfmisc_1('#skF_4','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_191,plain,(
    ! [D_30,B_31,A_32,C_33] :
      ( D_30 = B_31
      | k1_xboole_0 = B_31
      | k1_xboole_0 = A_32
      | k2_zfmisc_1(C_33,D_30) != k2_zfmisc_1(A_32,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_296,plain,(
    ! [C_46,A_47,C_48,D_49,B_45] :
      ( D_49 = C_46
      | k1_xboole_0 = C_46
      | k2_zfmisc_1(A_47,B_45) = k1_xboole_0
      | k3_zfmisc_1(A_47,B_45,C_46) != k2_zfmisc_1(C_48,D_49) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_191])).

tff(c_314,plain,(
    ! [D_49,C_48] :
      ( D_49 = '#skF_3'
      | k1_xboole_0 = '#skF_3'
      | k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0
      | k3_zfmisc_1('#skF_4','#skF_5','#skF_6') != k2_zfmisc_1(C_48,D_49) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_296])).

tff(c_325,plain,(
    ! [D_49,C_48] :
      ( D_49 = '#skF_3'
      | k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0
      | k3_zfmisc_1('#skF_4','#skF_5','#skF_6') != k2_zfmisc_1(C_48,D_49) ) ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_314])).

tff(c_326,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_325])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( k1_xboole_0 = B_2
      | k1_xboole_0 = A_1
      | k2_zfmisc_1(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_378,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_326,c_2])).

tff(c_388,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_18,c_378])).

tff(c_390,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_325])).

tff(c_258,plain,(
    ! [B_38,A_42,B_39,A_41,C_40] :
      ( C_40 = B_39
      | k1_xboole_0 = B_39
      | k1_xboole_0 = A_41
      | k3_zfmisc_1(A_42,B_38,C_40) != k2_zfmisc_1(A_41,B_39) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_191])).

tff(c_285,plain,(
    ! [B_43,A_44] :
      ( B_43 = '#skF_3'
      | k1_xboole_0 = B_43
      | k1_xboole_0 = A_44
      | k3_zfmisc_1('#skF_4','#skF_5','#skF_6') != k2_zfmisc_1(A_44,B_43) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_258])).

tff(c_288,plain,(
    ! [C_9,A_7,B_8] :
      ( C_9 = '#skF_3'
      | k1_xboole_0 = C_9
      | k2_zfmisc_1(A_7,B_8) = k1_xboole_0
      | k3_zfmisc_1(A_7,B_8,C_9) != k3_zfmisc_1('#skF_4','#skF_5','#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_285])).

tff(c_404,plain,
    ( '#skF_6' = '#skF_3'
    | k1_xboole_0 = '#skF_6'
    | k2_zfmisc_1('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(reflexivity,[status(thm),theory(equality)],[c_288])).

tff(c_429,plain,(
    k2_zfmisc_1('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_404])).

tff(c_456,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_429,c_2])).

tff(c_458,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_456])).

tff(c_6,plain,(
    ! [B_2] : k2_zfmisc_1(k1_xboole_0,B_2) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_61,plain,(
    ! [A_14,B_15,C_16] : k2_zfmisc_1(k2_zfmisc_1(A_14,B_15),C_16) = k3_zfmisc_1(A_14,B_15,C_16) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_90,plain,(
    ! [B_2,C_16] : k3_zfmisc_1(k1_xboole_0,B_2,C_16) = k2_zfmisc_1(k1_xboole_0,C_16) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_61])).

tff(c_94,plain,(
    ! [B_2,C_16] : k3_zfmisc_1(k1_xboole_0,B_2,C_16) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_90])).

tff(c_469,plain,(
    ! [B_2,C_16] : k3_zfmisc_1('#skF_4',B_2,C_16) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_458,c_458,c_94])).

tff(c_141,plain,(
    ! [C_23,A_24,B_25] :
      ( k1_xboole_0 = C_23
      | k2_zfmisc_1(A_24,B_25) = k1_xboole_0
      | k3_zfmisc_1(A_24,B_25,C_23) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_2])).

tff(c_153,plain,
    ( k1_xboole_0 = '#skF_3'
    | k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0
    | k3_zfmisc_1('#skF_4','#skF_5','#skF_6') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_141])).

tff(c_160,plain,
    ( k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0
    | k3_zfmisc_1('#skF_4','#skF_5','#skF_6') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_153])).

tff(c_186,plain,(
    k3_zfmisc_1('#skF_4','#skF_5','#skF_6') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_160])).

tff(c_465,plain,(
    k3_zfmisc_1('#skF_4','#skF_5','#skF_6') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_458,c_186])).

tff(c_683,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_469,c_465])).

tff(c_684,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_456])).

tff(c_448,plain,(
    ! [C_9] : k3_zfmisc_1('#skF_4','#skF_5',C_9) = k2_zfmisc_1(k1_xboole_0,C_9) ),
    inference(superposition,[status(thm),theory(equality)],[c_429,c_12])).

tff(c_455,plain,(
    ! [C_9] : k3_zfmisc_1('#skF_4','#skF_5',C_9) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_448])).

tff(c_817,plain,(
    ! [C_9] : k3_zfmisc_1('#skF_4','#skF_5',C_9) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_684,c_455])).

tff(c_391,plain,(
    ! [D_55,C_56] :
      ( D_55 = '#skF_3'
      | k3_zfmisc_1('#skF_4','#skF_5','#skF_6') != k2_zfmisc_1(C_56,D_55) ) ),
    inference(splitRight,[status(thm)],[c_325])).

tff(c_394,plain,(
    ! [C_9,A_7,B_8] :
      ( C_9 = '#skF_3'
      | k3_zfmisc_1(A_7,B_8,C_9) != k3_zfmisc_1('#skF_4','#skF_5','#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_391])).

tff(c_688,plain,(
    '#skF_6' = '#skF_3' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_394])).

tff(c_710,plain,(
    k3_zfmisc_1('#skF_4','#skF_5','#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_688,c_186])).

tff(c_816,plain,(
    k3_zfmisc_1('#skF_4','#skF_5','#skF_3') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_684,c_710])).

tff(c_821,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_817,c_816])).

tff(c_822,plain,
    ( k1_xboole_0 = '#skF_6'
    | '#skF_6' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_404])).

tff(c_854,plain,(
    '#skF_6' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_822])).

tff(c_858,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = k3_zfmisc_1('#skF_4','#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_854,c_22])).

tff(c_165,plain,(
    ! [C_26,A_27,B_28,D_29] :
      ( C_26 = A_27
      | k1_xboole_0 = B_28
      | k1_xboole_0 = A_27
      | k2_zfmisc_1(C_26,D_29) != k2_zfmisc_1(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_915,plain,(
    ! [C_103,B_102,A_104,D_101,C_100] :
      ( k2_zfmisc_1(A_104,B_102) = C_100
      | k1_xboole_0 = C_103
      | k2_zfmisc_1(A_104,B_102) = k1_xboole_0
      | k3_zfmisc_1(A_104,B_102,C_103) != k2_zfmisc_1(C_100,D_101) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_165])).

tff(c_918,plain,(
    ! [C_100,D_101] :
      ( k2_zfmisc_1('#skF_1','#skF_2') = C_100
      | k1_xboole_0 = '#skF_3'
      | k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0
      | k3_zfmisc_1('#skF_4','#skF_5','#skF_3') != k2_zfmisc_1(C_100,D_101) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_858,c_915])).

tff(c_945,plain,(
    ! [C_105,D_106] :
      ( k2_zfmisc_1('#skF_1','#skF_2') = C_105
      | k3_zfmisc_1('#skF_4','#skF_5','#skF_3') != k2_zfmisc_1(C_105,D_106) ) ),
    inference(negUnitSimplification,[status(thm)],[c_390,c_16,c_918])).

tff(c_948,plain,(
    ! [A_7,B_8,C_9] :
      ( k2_zfmisc_1(A_7,B_8) = k2_zfmisc_1('#skF_1','#skF_2')
      | k3_zfmisc_1(A_7,B_8,C_9) != k3_zfmisc_1('#skF_4','#skF_5','#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_945])).

tff(c_958,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = k2_zfmisc_1('#skF_4','#skF_5') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_948])).

tff(c_8,plain,(
    ! [D_6,B_4,A_3,C_5] :
      ( D_6 = B_4
      | k1_xboole_0 = B_4
      | k1_xboole_0 = A_3
      | k2_zfmisc_1(C_5,D_6) != k2_zfmisc_1(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_995,plain,(
    ! [D_6,C_5] :
      ( D_6 = '#skF_2'
      | k1_xboole_0 = '#skF_2'
      | k1_xboole_0 = '#skF_1'
      | k2_zfmisc_1(C_5,D_6) != k2_zfmisc_1('#skF_4','#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_958,c_8])).

tff(c_1011,plain,(
    ! [D_6,C_5] :
      ( D_6 = '#skF_2'
      | k2_zfmisc_1(C_5,D_6) != k2_zfmisc_1('#skF_4','#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_18,c_995])).

tff(c_1018,plain,(
    '#skF_5' = '#skF_2' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_1011])).

tff(c_10,plain,(
    ! [C_5,A_3,B_4,D_6] :
      ( C_5 = A_3
      | k1_xboole_0 = B_4
      | k1_xboole_0 = A_3
      | k2_zfmisc_1(C_5,D_6) != k2_zfmisc_1(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1001,plain,(
    ! [C_5,D_6] :
      ( C_5 = '#skF_1'
      | k1_xboole_0 = '#skF_2'
      | k1_xboole_0 = '#skF_1'
      | k2_zfmisc_1(C_5,D_6) != k2_zfmisc_1('#skF_4','#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_958,c_10])).

tff(c_1012,plain,(
    ! [C_5,D_6] :
      ( C_5 = '#skF_1'
      | k2_zfmisc_1(C_5,D_6) != k2_zfmisc_1('#skF_4','#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_18,c_1001])).

tff(c_1109,plain,(
    ! [C_5,D_6] :
      ( C_5 = '#skF_1'
      | k2_zfmisc_1(C_5,D_6) != k2_zfmisc_1('#skF_4','#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1018,c_1012])).

tff(c_1112,plain,(
    '#skF_1' = '#skF_4' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_1109])).

tff(c_1114,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_45,c_1112])).

tff(c_1115,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_822])).

tff(c_4,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_74,plain,(
    ! [A_14,B_15] : k3_zfmisc_1(A_14,B_15,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_4])).

tff(c_1140,plain,(
    ! [A_14,B_15] : k3_zfmisc_1(A_14,B_15,'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1115,c_1115,c_74])).

tff(c_1135,plain,(
    k3_zfmisc_1('#skF_4','#skF_5','#skF_6') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1115,c_186])).

tff(c_1253,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1140,c_1135])).

tff(c_1254,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_160])).

tff(c_1268,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_1254,c_2])).

tff(c_1276,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_18,c_1268])).

tff(c_1278,plain,(
    '#skF_1' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_14])).

tff(c_1279,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1278,c_20])).

tff(c_1277,plain,
    ( '#skF_5' != '#skF_2'
    | '#skF_6' != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_14])).

tff(c_1284,plain,(
    '#skF_6' != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_1277])).

tff(c_1296,plain,(
    k3_zfmisc_1('#skF_4','#skF_5','#skF_6') = k3_zfmisc_1('#skF_4','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1278,c_22])).

tff(c_1339,plain,(
    ! [D_134,B_135,A_136,C_137] :
      ( D_134 = B_135
      | k1_xboole_0 = B_135
      | k1_xboole_0 = A_136
      | k2_zfmisc_1(C_137,D_134) != k2_zfmisc_1(A_136,B_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1564,plain,(
    ! [C_170,A_171,D_167,C_168,B_169] :
      ( D_167 = C_170
      | k1_xboole_0 = C_170
      | k2_zfmisc_1(A_171,B_169) = k1_xboole_0
      | k3_zfmisc_1(A_171,B_169,C_170) != k2_zfmisc_1(C_168,D_167) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_1339])).

tff(c_1582,plain,(
    ! [D_167,C_168] :
      ( D_167 = '#skF_6'
      | k1_xboole_0 = '#skF_6'
      | k2_zfmisc_1('#skF_4','#skF_5') = k1_xboole_0
      | k3_zfmisc_1('#skF_4','#skF_2','#skF_3') != k2_zfmisc_1(C_168,D_167) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1296,c_1564])).

tff(c_1632,plain,(
    k2_zfmisc_1('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_1582])).

tff(c_1655,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_1632,c_2])).

tff(c_1664,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_1279,c_1655])).

tff(c_1652,plain,(
    ! [C_9] : k3_zfmisc_1('#skF_4','#skF_5',C_9) = k2_zfmisc_1(k1_xboole_0,C_9) ),
    inference(superposition,[status(thm),theory(equality)],[c_1632,c_12])).

tff(c_1661,plain,(
    ! [C_9] : k3_zfmisc_1('#skF_4','#skF_5',C_9) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1652])).

tff(c_1756,plain,(
    ! [C_9] : k3_zfmisc_1('#skF_4','#skF_5',C_9) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1664,c_1661])).

tff(c_1757,plain,(
    k3_zfmisc_1('#skF_4','#skF_2','#skF_3') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1756,c_1296])).

tff(c_1301,plain,(
    ! [A_131,B_132,C_133] : k2_zfmisc_1(k2_zfmisc_1(A_131,B_132),C_133) = k3_zfmisc_1(A_131,B_132,C_133) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1406,plain,(
    ! [C_144,A_145,B_146] :
      ( k1_xboole_0 = C_144
      | k2_zfmisc_1(A_145,B_146) = k1_xboole_0
      | k3_zfmisc_1(A_145,B_146,C_144) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1301,c_2])).

tff(c_1418,plain,
    ( k1_xboole_0 = '#skF_6'
    | k2_zfmisc_1('#skF_4','#skF_5') = k1_xboole_0
    | k3_zfmisc_1('#skF_4','#skF_2','#skF_3') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1296,c_1406])).

tff(c_1450,plain,(
    k3_zfmisc_1('#skF_4','#skF_2','#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_1418])).

tff(c_1672,plain,(
    k3_zfmisc_1('#skF_4','#skF_2','#skF_3') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1664,c_1450])).

tff(c_1846,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1757,c_1672])).

tff(c_1847,plain,(
    ! [D_167,C_168] :
      ( k1_xboole_0 = '#skF_6'
      | D_167 = '#skF_6'
      | k3_zfmisc_1('#skF_4','#skF_2','#skF_3') != k2_zfmisc_1(C_168,D_167) ) ),
    inference(splitRight,[status(thm)],[c_1582])).

tff(c_1849,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_1847])).

tff(c_1314,plain,(
    ! [A_131,B_132] : k3_zfmisc_1(A_131,B_132,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1301,c_4])).

tff(c_1862,plain,(
    ! [A_131,B_132] : k3_zfmisc_1(A_131,B_132,'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1849,c_1849,c_1314])).

tff(c_1918,plain,(
    k3_zfmisc_1('#skF_4','#skF_2','#skF_3') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1862,c_1296])).

tff(c_1857,plain,(
    k3_zfmisc_1('#skF_4','#skF_2','#skF_3') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1849,c_1450])).

tff(c_1989,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1918,c_1857])).

tff(c_1992,plain,(
    ! [D_198,C_199] :
      ( D_198 = '#skF_6'
      | k3_zfmisc_1('#skF_4','#skF_2','#skF_3') != k2_zfmisc_1(C_199,D_198) ) ),
    inference(splitRight,[status(thm)],[c_1847])).

tff(c_1995,plain,(
    ! [C_9,A_7,B_8] :
      ( C_9 = '#skF_6'
      | k3_zfmisc_1(A_7,B_8,C_9) != k3_zfmisc_1('#skF_4','#skF_2','#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_1992])).

tff(c_2017,plain,(
    '#skF_6' = '#skF_3' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_1995])).

tff(c_2019,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1284,c_2017])).

tff(c_2021,plain,(
    k3_zfmisc_1('#skF_4','#skF_2','#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1418])).

tff(c_1310,plain,(
    ! [C_133,A_131,B_132] :
      ( k1_xboole_0 = C_133
      | k2_zfmisc_1(A_131,B_132) = k1_xboole_0
      | k3_zfmisc_1(A_131,B_132,C_133) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1301,c_2])).

tff(c_2026,plain,
    ( k1_xboole_0 = '#skF_3'
    | k2_zfmisc_1('#skF_4','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2021,c_1310])).

tff(c_2031,plain,(
    k2_zfmisc_1('#skF_4','#skF_2') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_2026])).

tff(c_2051,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_2031,c_2])).

tff(c_2060,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1279,c_18,c_2051])).

tff(c_2061,plain,(
    '#skF_5' != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_1277])).

tff(c_2062,plain,(
    '#skF_6' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1277])).

tff(c_2067,plain,(
    k3_zfmisc_1('#skF_4','#skF_5','#skF_3') = k3_zfmisc_1('#skF_4','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2062,c_1278,c_22])).

tff(c_2128,plain,(
    ! [D_209,B_210,A_211,C_212] :
      ( D_209 = B_210
      | k1_xboole_0 = B_210
      | k1_xboole_0 = A_211
      | k2_zfmisc_1(C_212,D_209) != k2_zfmisc_1(A_211,B_210) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2337,plain,(
    ! [D_242,A_241,C_238,B_239,C_240] :
      ( D_242 = C_240
      | k1_xboole_0 = C_240
      | k2_zfmisc_1(A_241,B_239) = k1_xboole_0
      | k3_zfmisc_1(A_241,B_239,C_240) != k2_zfmisc_1(C_238,D_242) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_2128])).

tff(c_2355,plain,(
    ! [D_242,C_238] :
      ( D_242 = '#skF_3'
      | k1_xboole_0 = '#skF_3'
      | k2_zfmisc_1('#skF_4','#skF_5') = k1_xboole_0
      | k3_zfmisc_1('#skF_4','#skF_2','#skF_3') != k2_zfmisc_1(C_238,D_242) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2067,c_2337])).

tff(c_2366,plain,(
    ! [D_242,C_238] :
      ( D_242 = '#skF_3'
      | k2_zfmisc_1('#skF_4','#skF_5') = k1_xboole_0
      | k3_zfmisc_1('#skF_4','#skF_2','#skF_3') != k2_zfmisc_1(C_238,D_242) ) ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_2355])).

tff(c_2367,plain,(
    k2_zfmisc_1('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_2366])).

tff(c_2389,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_2367,c_2])).

tff(c_2398,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_1279,c_2389])).

tff(c_2083,plain,(
    ! [A_204,B_205,C_206] : k2_zfmisc_1(k2_zfmisc_1(A_204,B_205),C_206) = k3_zfmisc_1(A_204,B_205,C_206) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2105,plain,(
    ! [A_1,C_206] : k3_zfmisc_1(A_1,k1_xboole_0,C_206) = k2_zfmisc_1(k1_xboole_0,C_206) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_2083])).

tff(c_2115,plain,(
    ! [A_1,C_206] : k3_zfmisc_1(A_1,k1_xboole_0,C_206) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_2105])).

tff(c_2408,plain,(
    ! [A_1,C_206] : k3_zfmisc_1(A_1,'#skF_5',C_206) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2398,c_2398,c_2115])).

tff(c_2536,plain,(
    k3_zfmisc_1('#skF_4','#skF_2','#skF_3') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2408,c_2067])).

tff(c_2188,plain,(
    ! [C_217,A_218,B_219] :
      ( k1_xboole_0 = C_217
      | k2_zfmisc_1(A_218,B_219) = k1_xboole_0
      | k3_zfmisc_1(A_218,B_219,C_217) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2083,c_2])).

tff(c_2200,plain,
    ( k1_xboole_0 = '#skF_3'
    | k2_zfmisc_1('#skF_4','#skF_5') = k1_xboole_0
    | k3_zfmisc_1('#skF_4','#skF_2','#skF_3') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2067,c_2188])).

tff(c_2207,plain,
    ( k2_zfmisc_1('#skF_4','#skF_5') = k1_xboole_0
    | k3_zfmisc_1('#skF_4','#skF_2','#skF_3') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_2200])).

tff(c_2208,plain,(
    k3_zfmisc_1('#skF_4','#skF_2','#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_2207])).

tff(c_2404,plain,(
    k3_zfmisc_1('#skF_4','#skF_2','#skF_3') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2398,c_2208])).

tff(c_2598,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2536,c_2404])).

tff(c_2600,plain,(
    k2_zfmisc_1('#skF_4','#skF_5') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_2366])).

tff(c_2213,plain,(
    ! [C_220,A_221,B_222,D_223] :
      ( C_220 = A_221
      | k1_xboole_0 = B_222
      | k1_xboole_0 = A_221
      | k2_zfmisc_1(C_220,D_223) != k2_zfmisc_1(A_221,B_222) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2685,plain,(
    ! [A_274,C_273,C_275,D_271,B_272] :
      ( k2_zfmisc_1(A_274,B_272) = C_275
      | k1_xboole_0 = C_273
      | k2_zfmisc_1(A_274,B_272) = k1_xboole_0
      | k3_zfmisc_1(A_274,B_272,C_273) != k2_zfmisc_1(C_275,D_271) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_2213])).

tff(c_2703,plain,(
    ! [C_275,D_271] :
      ( k2_zfmisc_1('#skF_4','#skF_5') = C_275
      | k1_xboole_0 = '#skF_3'
      | k2_zfmisc_1('#skF_4','#skF_5') = k1_xboole_0
      | k3_zfmisc_1('#skF_4','#skF_2','#skF_3') != k2_zfmisc_1(C_275,D_271) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2067,c_2685])).

tff(c_2715,plain,(
    ! [C_276,D_277] :
      ( k2_zfmisc_1('#skF_4','#skF_5') = C_276
      | k3_zfmisc_1('#skF_4','#skF_2','#skF_3') != k2_zfmisc_1(C_276,D_277) ) ),
    inference(negUnitSimplification,[status(thm)],[c_2600,c_16,c_2703])).

tff(c_2718,plain,(
    ! [A_7,B_8,C_9] :
      ( k2_zfmisc_1(A_7,B_8) = k2_zfmisc_1('#skF_4','#skF_5')
      | k3_zfmisc_1(A_7,B_8,C_9) != k3_zfmisc_1('#skF_4','#skF_2','#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_2715])).

tff(c_2728,plain,(
    k2_zfmisc_1('#skF_4','#skF_5') = k2_zfmisc_1('#skF_4','#skF_2') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_2718])).

tff(c_2764,plain,(
    ! [C_5,D_6] :
      ( C_5 = '#skF_4'
      | k1_xboole_0 = '#skF_5'
      | k1_xboole_0 = '#skF_4'
      | k2_zfmisc_1(C_5,D_6) != k2_zfmisc_1('#skF_4','#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2728,c_10])).

tff(c_2780,plain,(
    ! [C_5,D_6] :
      ( C_5 = '#skF_4'
      | k1_xboole_0 = '#skF_5'
      | k2_zfmisc_1(C_5,D_6) != k2_zfmisc_1('#skF_4','#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_1279,c_2764])).

tff(c_2846,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_2780])).

tff(c_2754,plain,(
    k2_zfmisc_1('#skF_4','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2728,c_2600])).

tff(c_2894,plain,(
    k2_zfmisc_1('#skF_4','#skF_2') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2846,c_2754])).

tff(c_2909,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2846,c_2846,c_4])).

tff(c_2918,plain,(
    k2_zfmisc_1('#skF_4','#skF_2') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2909,c_2728])).

tff(c_2969,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2894,c_2918])).

tff(c_2971,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_2780])).

tff(c_2770,plain,(
    ! [D_6,C_5] :
      ( D_6 = '#skF_5'
      | k1_xboole_0 = '#skF_5'
      | k1_xboole_0 = '#skF_4'
      | k2_zfmisc_1(C_5,D_6) != k2_zfmisc_1('#skF_4','#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2728,c_8])).

tff(c_2781,plain,(
    ! [D_6,C_5] :
      ( D_6 = '#skF_5'
      | k1_xboole_0 = '#skF_5'
      | k2_zfmisc_1(C_5,D_6) != k2_zfmisc_1('#skF_4','#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_1279,c_2770])).

tff(c_3036,plain,(
    ! [D_6,C_5] :
      ( D_6 = '#skF_5'
      | k2_zfmisc_1(C_5,D_6) != k2_zfmisc_1('#skF_4','#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_2971,c_2781])).

tff(c_3039,plain,(
    '#skF_5' = '#skF_2' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_3036])).

tff(c_3041,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2061,c_3039])).

tff(c_3042,plain,(
    k2_zfmisc_1('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_2207])).

tff(c_3056,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_3042,c_2])).

tff(c_3063,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_1279,c_3056])).

tff(c_3072,plain,(
    '#skF_5' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3063,c_1279])).

tff(c_3076,plain,(
    '#skF_5' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3063,c_16])).

tff(c_3043,plain,(
    k3_zfmisc_1('#skF_4','#skF_2','#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_2207])).

tff(c_3154,plain,(
    k3_zfmisc_1('#skF_4','#skF_2','#skF_3') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3063,c_3043])).

tff(c_2092,plain,(
    ! [C_206,A_204,B_205] :
      ( k1_xboole_0 = C_206
      | k2_zfmisc_1(A_204,B_205) = k1_xboole_0
      | k3_zfmisc_1(A_204,B_205,C_206) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2083,c_2])).

tff(c_3268,plain,(
    ! [C_317,A_318,B_319] :
      ( C_317 = '#skF_5'
      | k2_zfmisc_1(A_318,B_319) = '#skF_5'
      | k3_zfmisc_1(A_318,B_319,C_317) != '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3063,c_3063,c_3063,c_2092])).

tff(c_3283,plain,
    ( '#skF_5' = '#skF_3'
    | k2_zfmisc_1('#skF_4','#skF_2') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_3154,c_3268])).

tff(c_3293,plain,(
    k2_zfmisc_1('#skF_4','#skF_2') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_3076,c_3283])).

tff(c_3071,plain,(
    ! [B_2,A_1] :
      ( B_2 = '#skF_5'
      | A_1 = '#skF_5'
      | k2_zfmisc_1(A_1,B_2) != '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3063,c_3063,c_3063,c_2])).

tff(c_3297,plain,
    ( '#skF_5' = '#skF_2'
    | '#skF_5' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_3293,c_3071])).

tff(c_3315,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3072,c_2061,c_3297])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:21:26 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.10/1.73  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.41/1.77  
% 4.41/1.77  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.41/1.77  %$ k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.41/1.77  
% 4.41/1.77  %Foreground sorts:
% 4.41/1.77  
% 4.41/1.77  
% 4.41/1.77  %Background operators:
% 4.41/1.77  
% 4.41/1.77  
% 4.41/1.77  %Foreground operators:
% 4.41/1.77  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.41/1.77  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.41/1.77  tff('#skF_5', type, '#skF_5': $i).
% 4.41/1.77  tff('#skF_6', type, '#skF_6': $i).
% 4.41/1.77  tff('#skF_2', type, '#skF_2': $i).
% 4.41/1.77  tff('#skF_3', type, '#skF_3': $i).
% 4.41/1.77  tff('#skF_1', type, '#skF_1': $i).
% 4.41/1.77  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 4.41/1.77  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.41/1.77  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.41/1.77  tff('#skF_4', type, '#skF_4': $i).
% 4.41/1.77  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.41/1.77  
% 4.41/1.79  tff(f_58, negated_conjecture, ~(![A, B, C, D, E, F]: ((k3_zfmisc_1(A, B, C) = k3_zfmisc_1(D, E, F)) => ((((A = k1_xboole_0) | (B = k1_xboole_0)) | (C = k1_xboole_0)) | (((A = D) & (B = E)) & (C = F))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_mcart_1)).
% 4.41/1.79  tff(f_43, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 4.41/1.79  tff(f_41, axiom, (![A, B, C, D]: ((k2_zfmisc_1(A, B) = k2_zfmisc_1(C, D)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | ((A = C) & (B = D))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t134_zfmisc_1)).
% 4.41/1.79  tff(f_31, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 4.41/1.79  tff(c_20, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.41/1.79  tff(c_18, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.41/1.79  tff(c_14, plain, ('#skF_6'!='#skF_3' | '#skF_5'!='#skF_2' | '#skF_1'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.41/1.79  tff(c_45, plain, ('#skF_1'!='#skF_4'), inference(splitLeft, [status(thm)], [c_14])).
% 4.41/1.79  tff(c_12, plain, (![A_7, B_8, C_9]: (k2_zfmisc_1(k2_zfmisc_1(A_7, B_8), C_9)=k3_zfmisc_1(A_7, B_8, C_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.41/1.79  tff(c_16, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.41/1.79  tff(c_22, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')=k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.41/1.79  tff(c_191, plain, (![D_30, B_31, A_32, C_33]: (D_30=B_31 | k1_xboole_0=B_31 | k1_xboole_0=A_32 | k2_zfmisc_1(C_33, D_30)!=k2_zfmisc_1(A_32, B_31))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.41/1.79  tff(c_296, plain, (![C_46, A_47, C_48, D_49, B_45]: (D_49=C_46 | k1_xboole_0=C_46 | k2_zfmisc_1(A_47, B_45)=k1_xboole_0 | k3_zfmisc_1(A_47, B_45, C_46)!=k2_zfmisc_1(C_48, D_49))), inference(superposition, [status(thm), theory('equality')], [c_12, c_191])).
% 4.41/1.79  tff(c_314, plain, (![D_49, C_48]: (D_49='#skF_3' | k1_xboole_0='#skF_3' | k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0 | k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')!=k2_zfmisc_1(C_48, D_49))), inference(superposition, [status(thm), theory('equality')], [c_22, c_296])).
% 4.41/1.79  tff(c_325, plain, (![D_49, C_48]: (D_49='#skF_3' | k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0 | k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')!=k2_zfmisc_1(C_48, D_49))), inference(negUnitSimplification, [status(thm)], [c_16, c_314])).
% 4.41/1.79  tff(c_326, plain, (k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_325])).
% 4.41/1.79  tff(c_2, plain, (![B_2, A_1]: (k1_xboole_0=B_2 | k1_xboole_0=A_1 | k2_zfmisc_1(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.41/1.79  tff(c_378, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_326, c_2])).
% 4.41/1.79  tff(c_388, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_18, c_378])).
% 4.41/1.79  tff(c_390, plain, (k2_zfmisc_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_325])).
% 4.41/1.79  tff(c_258, plain, (![B_38, A_42, B_39, A_41, C_40]: (C_40=B_39 | k1_xboole_0=B_39 | k1_xboole_0=A_41 | k3_zfmisc_1(A_42, B_38, C_40)!=k2_zfmisc_1(A_41, B_39))), inference(superposition, [status(thm), theory('equality')], [c_12, c_191])).
% 4.41/1.79  tff(c_285, plain, (![B_43, A_44]: (B_43='#skF_3' | k1_xboole_0=B_43 | k1_xboole_0=A_44 | k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')!=k2_zfmisc_1(A_44, B_43))), inference(superposition, [status(thm), theory('equality')], [c_22, c_258])).
% 4.41/1.79  tff(c_288, plain, (![C_9, A_7, B_8]: (C_9='#skF_3' | k1_xboole_0=C_9 | k2_zfmisc_1(A_7, B_8)=k1_xboole_0 | k3_zfmisc_1(A_7, B_8, C_9)!=k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_12, c_285])).
% 4.41/1.79  tff(c_404, plain, ('#skF_6'='#skF_3' | k1_xboole_0='#skF_6' | k2_zfmisc_1('#skF_4', '#skF_5')=k1_xboole_0), inference(reflexivity, [status(thm), theory('equality')], [c_288])).
% 4.41/1.79  tff(c_429, plain, (k2_zfmisc_1('#skF_4', '#skF_5')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_404])).
% 4.41/1.79  tff(c_456, plain, (k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_429, c_2])).
% 4.41/1.79  tff(c_458, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_456])).
% 4.41/1.79  tff(c_6, plain, (![B_2]: (k2_zfmisc_1(k1_xboole_0, B_2)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.41/1.79  tff(c_61, plain, (![A_14, B_15, C_16]: (k2_zfmisc_1(k2_zfmisc_1(A_14, B_15), C_16)=k3_zfmisc_1(A_14, B_15, C_16))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.41/1.79  tff(c_90, plain, (![B_2, C_16]: (k3_zfmisc_1(k1_xboole_0, B_2, C_16)=k2_zfmisc_1(k1_xboole_0, C_16))), inference(superposition, [status(thm), theory('equality')], [c_6, c_61])).
% 4.41/1.79  tff(c_94, plain, (![B_2, C_16]: (k3_zfmisc_1(k1_xboole_0, B_2, C_16)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_90])).
% 4.41/1.79  tff(c_469, plain, (![B_2, C_16]: (k3_zfmisc_1('#skF_4', B_2, C_16)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_458, c_458, c_94])).
% 4.41/1.79  tff(c_141, plain, (![C_23, A_24, B_25]: (k1_xboole_0=C_23 | k2_zfmisc_1(A_24, B_25)=k1_xboole_0 | k3_zfmisc_1(A_24, B_25, C_23)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_61, c_2])).
% 4.41/1.79  tff(c_153, plain, (k1_xboole_0='#skF_3' | k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0 | k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_22, c_141])).
% 4.41/1.79  tff(c_160, plain, (k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0 | k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_16, c_153])).
% 4.41/1.79  tff(c_186, plain, (k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_160])).
% 4.41/1.79  tff(c_465, plain, (k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_458, c_186])).
% 4.41/1.79  tff(c_683, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_469, c_465])).
% 4.41/1.79  tff(c_684, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_456])).
% 4.41/1.79  tff(c_448, plain, (![C_9]: (k3_zfmisc_1('#skF_4', '#skF_5', C_9)=k2_zfmisc_1(k1_xboole_0, C_9))), inference(superposition, [status(thm), theory('equality')], [c_429, c_12])).
% 4.41/1.79  tff(c_455, plain, (![C_9]: (k3_zfmisc_1('#skF_4', '#skF_5', C_9)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_448])).
% 4.41/1.79  tff(c_817, plain, (![C_9]: (k3_zfmisc_1('#skF_4', '#skF_5', C_9)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_684, c_455])).
% 4.41/1.79  tff(c_391, plain, (![D_55, C_56]: (D_55='#skF_3' | k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')!=k2_zfmisc_1(C_56, D_55))), inference(splitRight, [status(thm)], [c_325])).
% 4.41/1.79  tff(c_394, plain, (![C_9, A_7, B_8]: (C_9='#skF_3' | k3_zfmisc_1(A_7, B_8, C_9)!=k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_12, c_391])).
% 4.41/1.79  tff(c_688, plain, ('#skF_6'='#skF_3'), inference(reflexivity, [status(thm), theory('equality')], [c_394])).
% 4.41/1.79  tff(c_710, plain, (k3_zfmisc_1('#skF_4', '#skF_5', '#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_688, c_186])).
% 4.41/1.79  tff(c_816, plain, (k3_zfmisc_1('#skF_4', '#skF_5', '#skF_3')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_684, c_710])).
% 4.41/1.79  tff(c_821, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_817, c_816])).
% 4.41/1.79  tff(c_822, plain, (k1_xboole_0='#skF_6' | '#skF_6'='#skF_3'), inference(splitRight, [status(thm)], [c_404])).
% 4.41/1.79  tff(c_854, plain, ('#skF_6'='#skF_3'), inference(splitLeft, [status(thm)], [c_822])).
% 4.41/1.79  tff(c_858, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')=k3_zfmisc_1('#skF_4', '#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_854, c_22])).
% 4.41/1.79  tff(c_165, plain, (![C_26, A_27, B_28, D_29]: (C_26=A_27 | k1_xboole_0=B_28 | k1_xboole_0=A_27 | k2_zfmisc_1(C_26, D_29)!=k2_zfmisc_1(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.41/1.79  tff(c_915, plain, (![C_103, B_102, A_104, D_101, C_100]: (k2_zfmisc_1(A_104, B_102)=C_100 | k1_xboole_0=C_103 | k2_zfmisc_1(A_104, B_102)=k1_xboole_0 | k3_zfmisc_1(A_104, B_102, C_103)!=k2_zfmisc_1(C_100, D_101))), inference(superposition, [status(thm), theory('equality')], [c_12, c_165])).
% 4.41/1.79  tff(c_918, plain, (![C_100, D_101]: (k2_zfmisc_1('#skF_1', '#skF_2')=C_100 | k1_xboole_0='#skF_3' | k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0 | k3_zfmisc_1('#skF_4', '#skF_5', '#skF_3')!=k2_zfmisc_1(C_100, D_101))), inference(superposition, [status(thm), theory('equality')], [c_858, c_915])).
% 4.41/1.79  tff(c_945, plain, (![C_105, D_106]: (k2_zfmisc_1('#skF_1', '#skF_2')=C_105 | k3_zfmisc_1('#skF_4', '#skF_5', '#skF_3')!=k2_zfmisc_1(C_105, D_106))), inference(negUnitSimplification, [status(thm)], [c_390, c_16, c_918])).
% 4.41/1.79  tff(c_948, plain, (![A_7, B_8, C_9]: (k2_zfmisc_1(A_7, B_8)=k2_zfmisc_1('#skF_1', '#skF_2') | k3_zfmisc_1(A_7, B_8, C_9)!=k3_zfmisc_1('#skF_4', '#skF_5', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_12, c_945])).
% 4.41/1.79  tff(c_958, plain, (k2_zfmisc_1('#skF_1', '#skF_2')=k2_zfmisc_1('#skF_4', '#skF_5')), inference(reflexivity, [status(thm), theory('equality')], [c_948])).
% 4.41/1.79  tff(c_8, plain, (![D_6, B_4, A_3, C_5]: (D_6=B_4 | k1_xboole_0=B_4 | k1_xboole_0=A_3 | k2_zfmisc_1(C_5, D_6)!=k2_zfmisc_1(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.41/1.79  tff(c_995, plain, (![D_6, C_5]: (D_6='#skF_2' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1' | k2_zfmisc_1(C_5, D_6)!=k2_zfmisc_1('#skF_4', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_958, c_8])).
% 4.41/1.79  tff(c_1011, plain, (![D_6, C_5]: (D_6='#skF_2' | k2_zfmisc_1(C_5, D_6)!=k2_zfmisc_1('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_20, c_18, c_995])).
% 4.41/1.79  tff(c_1018, plain, ('#skF_5'='#skF_2'), inference(reflexivity, [status(thm), theory('equality')], [c_1011])).
% 4.41/1.79  tff(c_10, plain, (![C_5, A_3, B_4, D_6]: (C_5=A_3 | k1_xboole_0=B_4 | k1_xboole_0=A_3 | k2_zfmisc_1(C_5, D_6)!=k2_zfmisc_1(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.41/1.79  tff(c_1001, plain, (![C_5, D_6]: (C_5='#skF_1' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1' | k2_zfmisc_1(C_5, D_6)!=k2_zfmisc_1('#skF_4', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_958, c_10])).
% 4.41/1.79  tff(c_1012, plain, (![C_5, D_6]: (C_5='#skF_1' | k2_zfmisc_1(C_5, D_6)!=k2_zfmisc_1('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_20, c_18, c_1001])).
% 4.41/1.79  tff(c_1109, plain, (![C_5, D_6]: (C_5='#skF_1' | k2_zfmisc_1(C_5, D_6)!=k2_zfmisc_1('#skF_4', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1018, c_1012])).
% 4.41/1.79  tff(c_1112, plain, ('#skF_1'='#skF_4'), inference(reflexivity, [status(thm), theory('equality')], [c_1109])).
% 4.41/1.79  tff(c_1114, plain, $false, inference(negUnitSimplification, [status(thm)], [c_45, c_1112])).
% 4.41/1.79  tff(c_1115, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_822])).
% 4.41/1.79  tff(c_4, plain, (![A_1]: (k2_zfmisc_1(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.41/1.79  tff(c_74, plain, (![A_14, B_15]: (k3_zfmisc_1(A_14, B_15, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_61, c_4])).
% 4.41/1.79  tff(c_1140, plain, (![A_14, B_15]: (k3_zfmisc_1(A_14, B_15, '#skF_6')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1115, c_1115, c_74])).
% 4.41/1.79  tff(c_1135, plain, (k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_1115, c_186])).
% 4.41/1.79  tff(c_1253, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1140, c_1135])).
% 4.41/1.79  tff(c_1254, plain, (k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_160])).
% 4.41/1.79  tff(c_1268, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_1254, c_2])).
% 4.41/1.79  tff(c_1276, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_18, c_1268])).
% 4.41/1.79  tff(c_1278, plain, ('#skF_1'='#skF_4'), inference(splitRight, [status(thm)], [c_14])).
% 4.41/1.79  tff(c_1279, plain, (k1_xboole_0!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1278, c_20])).
% 4.41/1.79  tff(c_1277, plain, ('#skF_5'!='#skF_2' | '#skF_6'!='#skF_3'), inference(splitRight, [status(thm)], [c_14])).
% 4.41/1.79  tff(c_1284, plain, ('#skF_6'!='#skF_3'), inference(splitLeft, [status(thm)], [c_1277])).
% 4.41/1.79  tff(c_1296, plain, (k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')=k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1278, c_22])).
% 4.41/1.79  tff(c_1339, plain, (![D_134, B_135, A_136, C_137]: (D_134=B_135 | k1_xboole_0=B_135 | k1_xboole_0=A_136 | k2_zfmisc_1(C_137, D_134)!=k2_zfmisc_1(A_136, B_135))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.41/1.79  tff(c_1564, plain, (![C_170, A_171, D_167, C_168, B_169]: (D_167=C_170 | k1_xboole_0=C_170 | k2_zfmisc_1(A_171, B_169)=k1_xboole_0 | k3_zfmisc_1(A_171, B_169, C_170)!=k2_zfmisc_1(C_168, D_167))), inference(superposition, [status(thm), theory('equality')], [c_12, c_1339])).
% 4.41/1.79  tff(c_1582, plain, (![D_167, C_168]: (D_167='#skF_6' | k1_xboole_0='#skF_6' | k2_zfmisc_1('#skF_4', '#skF_5')=k1_xboole_0 | k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3')!=k2_zfmisc_1(C_168, D_167))), inference(superposition, [status(thm), theory('equality')], [c_1296, c_1564])).
% 4.41/1.79  tff(c_1632, plain, (k2_zfmisc_1('#skF_4', '#skF_5')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_1582])).
% 4.41/1.79  tff(c_1655, plain, (k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_1632, c_2])).
% 4.41/1.79  tff(c_1664, plain, (k1_xboole_0='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_1279, c_1655])).
% 4.41/1.79  tff(c_1652, plain, (![C_9]: (k3_zfmisc_1('#skF_4', '#skF_5', C_9)=k2_zfmisc_1(k1_xboole_0, C_9))), inference(superposition, [status(thm), theory('equality')], [c_1632, c_12])).
% 4.41/1.79  tff(c_1661, plain, (![C_9]: (k3_zfmisc_1('#skF_4', '#skF_5', C_9)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_1652])).
% 4.41/1.79  tff(c_1756, plain, (![C_9]: (k3_zfmisc_1('#skF_4', '#skF_5', C_9)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1664, c_1661])).
% 4.41/1.79  tff(c_1757, plain, (k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_1756, c_1296])).
% 4.41/1.79  tff(c_1301, plain, (![A_131, B_132, C_133]: (k2_zfmisc_1(k2_zfmisc_1(A_131, B_132), C_133)=k3_zfmisc_1(A_131, B_132, C_133))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.41/1.79  tff(c_1406, plain, (![C_144, A_145, B_146]: (k1_xboole_0=C_144 | k2_zfmisc_1(A_145, B_146)=k1_xboole_0 | k3_zfmisc_1(A_145, B_146, C_144)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1301, c_2])).
% 4.41/1.79  tff(c_1418, plain, (k1_xboole_0='#skF_6' | k2_zfmisc_1('#skF_4', '#skF_5')=k1_xboole_0 | k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1296, c_1406])).
% 4.41/1.79  tff(c_1450, plain, (k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_1418])).
% 4.41/1.79  tff(c_1672, plain, (k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_1664, c_1450])).
% 4.41/1.79  tff(c_1846, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1757, c_1672])).
% 4.41/1.79  tff(c_1847, plain, (![D_167, C_168]: (k1_xboole_0='#skF_6' | D_167='#skF_6' | k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3')!=k2_zfmisc_1(C_168, D_167))), inference(splitRight, [status(thm)], [c_1582])).
% 4.41/1.79  tff(c_1849, plain, (k1_xboole_0='#skF_6'), inference(splitLeft, [status(thm)], [c_1847])).
% 4.41/1.79  tff(c_1314, plain, (![A_131, B_132]: (k3_zfmisc_1(A_131, B_132, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1301, c_4])).
% 4.41/1.79  tff(c_1862, plain, (![A_131, B_132]: (k3_zfmisc_1(A_131, B_132, '#skF_6')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1849, c_1849, c_1314])).
% 4.41/1.79  tff(c_1918, plain, (k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_1862, c_1296])).
% 4.41/1.79  tff(c_1857, plain, (k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_1849, c_1450])).
% 4.41/1.79  tff(c_1989, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1918, c_1857])).
% 4.41/1.79  tff(c_1992, plain, (![D_198, C_199]: (D_198='#skF_6' | k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3')!=k2_zfmisc_1(C_199, D_198))), inference(splitRight, [status(thm)], [c_1847])).
% 4.41/1.79  tff(c_1995, plain, (![C_9, A_7, B_8]: (C_9='#skF_6' | k3_zfmisc_1(A_7, B_8, C_9)!=k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_12, c_1992])).
% 4.41/1.79  tff(c_2017, plain, ('#skF_6'='#skF_3'), inference(reflexivity, [status(thm), theory('equality')], [c_1995])).
% 4.41/1.79  tff(c_2019, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1284, c_2017])).
% 4.41/1.79  tff(c_2021, plain, (k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_1418])).
% 4.41/1.79  tff(c_1310, plain, (![C_133, A_131, B_132]: (k1_xboole_0=C_133 | k2_zfmisc_1(A_131, B_132)=k1_xboole_0 | k3_zfmisc_1(A_131, B_132, C_133)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1301, c_2])).
% 4.41/1.79  tff(c_2026, plain, (k1_xboole_0='#skF_3' | k2_zfmisc_1('#skF_4', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_2021, c_1310])).
% 4.41/1.79  tff(c_2031, plain, (k2_zfmisc_1('#skF_4', '#skF_2')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_16, c_2026])).
% 4.41/1.79  tff(c_2051, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_2031, c_2])).
% 4.41/1.79  tff(c_2060, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1279, c_18, c_2051])).
% 4.41/1.79  tff(c_2061, plain, ('#skF_5'!='#skF_2'), inference(splitRight, [status(thm)], [c_1277])).
% 4.41/1.79  tff(c_2062, plain, ('#skF_6'='#skF_3'), inference(splitRight, [status(thm)], [c_1277])).
% 4.41/1.79  tff(c_2067, plain, (k3_zfmisc_1('#skF_4', '#skF_5', '#skF_3')=k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2062, c_1278, c_22])).
% 4.41/1.79  tff(c_2128, plain, (![D_209, B_210, A_211, C_212]: (D_209=B_210 | k1_xboole_0=B_210 | k1_xboole_0=A_211 | k2_zfmisc_1(C_212, D_209)!=k2_zfmisc_1(A_211, B_210))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.41/1.79  tff(c_2337, plain, (![D_242, A_241, C_238, B_239, C_240]: (D_242=C_240 | k1_xboole_0=C_240 | k2_zfmisc_1(A_241, B_239)=k1_xboole_0 | k3_zfmisc_1(A_241, B_239, C_240)!=k2_zfmisc_1(C_238, D_242))), inference(superposition, [status(thm), theory('equality')], [c_12, c_2128])).
% 4.41/1.79  tff(c_2355, plain, (![D_242, C_238]: (D_242='#skF_3' | k1_xboole_0='#skF_3' | k2_zfmisc_1('#skF_4', '#skF_5')=k1_xboole_0 | k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3')!=k2_zfmisc_1(C_238, D_242))), inference(superposition, [status(thm), theory('equality')], [c_2067, c_2337])).
% 4.41/1.79  tff(c_2366, plain, (![D_242, C_238]: (D_242='#skF_3' | k2_zfmisc_1('#skF_4', '#skF_5')=k1_xboole_0 | k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3')!=k2_zfmisc_1(C_238, D_242))), inference(negUnitSimplification, [status(thm)], [c_16, c_2355])).
% 4.41/1.79  tff(c_2367, plain, (k2_zfmisc_1('#skF_4', '#skF_5')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_2366])).
% 4.41/1.79  tff(c_2389, plain, (k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_2367, c_2])).
% 4.41/1.79  tff(c_2398, plain, (k1_xboole_0='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_1279, c_2389])).
% 4.41/1.79  tff(c_2083, plain, (![A_204, B_205, C_206]: (k2_zfmisc_1(k2_zfmisc_1(A_204, B_205), C_206)=k3_zfmisc_1(A_204, B_205, C_206))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.41/1.79  tff(c_2105, plain, (![A_1, C_206]: (k3_zfmisc_1(A_1, k1_xboole_0, C_206)=k2_zfmisc_1(k1_xboole_0, C_206))), inference(superposition, [status(thm), theory('equality')], [c_4, c_2083])).
% 4.41/1.79  tff(c_2115, plain, (![A_1, C_206]: (k3_zfmisc_1(A_1, k1_xboole_0, C_206)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_2105])).
% 4.41/1.79  tff(c_2408, plain, (![A_1, C_206]: (k3_zfmisc_1(A_1, '#skF_5', C_206)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2398, c_2398, c_2115])).
% 4.41/1.79  tff(c_2536, plain, (k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_2408, c_2067])).
% 4.41/1.79  tff(c_2188, plain, (![C_217, A_218, B_219]: (k1_xboole_0=C_217 | k2_zfmisc_1(A_218, B_219)=k1_xboole_0 | k3_zfmisc_1(A_218, B_219, C_217)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2083, c_2])).
% 4.41/1.79  tff(c_2200, plain, (k1_xboole_0='#skF_3' | k2_zfmisc_1('#skF_4', '#skF_5')=k1_xboole_0 | k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_2067, c_2188])).
% 4.41/1.79  tff(c_2207, plain, (k2_zfmisc_1('#skF_4', '#skF_5')=k1_xboole_0 | k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_16, c_2200])).
% 4.41/1.79  tff(c_2208, plain, (k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_2207])).
% 4.41/1.79  tff(c_2404, plain, (k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_2398, c_2208])).
% 4.41/1.79  tff(c_2598, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2536, c_2404])).
% 4.41/1.79  tff(c_2600, plain, (k2_zfmisc_1('#skF_4', '#skF_5')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_2366])).
% 4.41/1.79  tff(c_2213, plain, (![C_220, A_221, B_222, D_223]: (C_220=A_221 | k1_xboole_0=B_222 | k1_xboole_0=A_221 | k2_zfmisc_1(C_220, D_223)!=k2_zfmisc_1(A_221, B_222))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.41/1.79  tff(c_2685, plain, (![A_274, C_273, C_275, D_271, B_272]: (k2_zfmisc_1(A_274, B_272)=C_275 | k1_xboole_0=C_273 | k2_zfmisc_1(A_274, B_272)=k1_xboole_0 | k3_zfmisc_1(A_274, B_272, C_273)!=k2_zfmisc_1(C_275, D_271))), inference(superposition, [status(thm), theory('equality')], [c_12, c_2213])).
% 4.41/1.79  tff(c_2703, plain, (![C_275, D_271]: (k2_zfmisc_1('#skF_4', '#skF_5')=C_275 | k1_xboole_0='#skF_3' | k2_zfmisc_1('#skF_4', '#skF_5')=k1_xboole_0 | k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3')!=k2_zfmisc_1(C_275, D_271))), inference(superposition, [status(thm), theory('equality')], [c_2067, c_2685])).
% 4.41/1.79  tff(c_2715, plain, (![C_276, D_277]: (k2_zfmisc_1('#skF_4', '#skF_5')=C_276 | k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3')!=k2_zfmisc_1(C_276, D_277))), inference(negUnitSimplification, [status(thm)], [c_2600, c_16, c_2703])).
% 4.41/1.79  tff(c_2718, plain, (![A_7, B_8, C_9]: (k2_zfmisc_1(A_7, B_8)=k2_zfmisc_1('#skF_4', '#skF_5') | k3_zfmisc_1(A_7, B_8, C_9)!=k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_12, c_2715])).
% 4.41/1.79  tff(c_2728, plain, (k2_zfmisc_1('#skF_4', '#skF_5')=k2_zfmisc_1('#skF_4', '#skF_2')), inference(reflexivity, [status(thm), theory('equality')], [c_2718])).
% 4.41/1.79  tff(c_2764, plain, (![C_5, D_6]: (C_5='#skF_4' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k2_zfmisc_1(C_5, D_6)!=k2_zfmisc_1('#skF_4', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_2728, c_10])).
% 4.41/1.79  tff(c_2780, plain, (![C_5, D_6]: (C_5='#skF_4' | k1_xboole_0='#skF_5' | k2_zfmisc_1(C_5, D_6)!=k2_zfmisc_1('#skF_4', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_1279, c_2764])).
% 4.41/1.79  tff(c_2846, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_2780])).
% 4.41/1.79  tff(c_2754, plain, (k2_zfmisc_1('#skF_4', '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2728, c_2600])).
% 4.41/1.79  tff(c_2894, plain, (k2_zfmisc_1('#skF_4', '#skF_2')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_2846, c_2754])).
% 4.41/1.79  tff(c_2909, plain, (![A_1]: (k2_zfmisc_1(A_1, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2846, c_2846, c_4])).
% 4.41/1.79  tff(c_2918, plain, (k2_zfmisc_1('#skF_4', '#skF_2')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_2909, c_2728])).
% 4.41/1.79  tff(c_2969, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2894, c_2918])).
% 4.41/1.79  tff(c_2971, plain, (k1_xboole_0!='#skF_5'), inference(splitRight, [status(thm)], [c_2780])).
% 4.41/1.79  tff(c_2770, plain, (![D_6, C_5]: (D_6='#skF_5' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k2_zfmisc_1(C_5, D_6)!=k2_zfmisc_1('#skF_4', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_2728, c_8])).
% 4.41/1.79  tff(c_2781, plain, (![D_6, C_5]: (D_6='#skF_5' | k1_xboole_0='#skF_5' | k2_zfmisc_1(C_5, D_6)!=k2_zfmisc_1('#skF_4', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_1279, c_2770])).
% 4.41/1.79  tff(c_3036, plain, (![D_6, C_5]: (D_6='#skF_5' | k2_zfmisc_1(C_5, D_6)!=k2_zfmisc_1('#skF_4', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_2971, c_2781])).
% 4.41/1.79  tff(c_3039, plain, ('#skF_5'='#skF_2'), inference(reflexivity, [status(thm), theory('equality')], [c_3036])).
% 4.41/1.79  tff(c_3041, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2061, c_3039])).
% 4.41/1.79  tff(c_3042, plain, (k2_zfmisc_1('#skF_4', '#skF_5')=k1_xboole_0), inference(splitRight, [status(thm)], [c_2207])).
% 4.41/1.79  tff(c_3056, plain, (k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_3042, c_2])).
% 4.41/1.79  tff(c_3063, plain, (k1_xboole_0='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_1279, c_3056])).
% 4.41/1.79  tff(c_3072, plain, ('#skF_5'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3063, c_1279])).
% 4.41/1.79  tff(c_3076, plain, ('#skF_5'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_3063, c_16])).
% 4.41/1.79  tff(c_3043, plain, (k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_2207])).
% 4.41/1.79  tff(c_3154, plain, (k3_zfmisc_1('#skF_4', '#skF_2', '#skF_3')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_3063, c_3043])).
% 4.41/1.79  tff(c_2092, plain, (![C_206, A_204, B_205]: (k1_xboole_0=C_206 | k2_zfmisc_1(A_204, B_205)=k1_xboole_0 | k3_zfmisc_1(A_204, B_205, C_206)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2083, c_2])).
% 4.41/1.79  tff(c_3268, plain, (![C_317, A_318, B_319]: (C_317='#skF_5' | k2_zfmisc_1(A_318, B_319)='#skF_5' | k3_zfmisc_1(A_318, B_319, C_317)!='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_3063, c_3063, c_3063, c_2092])).
% 4.41/1.79  tff(c_3283, plain, ('#skF_5'='#skF_3' | k2_zfmisc_1('#skF_4', '#skF_2')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_3154, c_3268])).
% 4.41/1.79  tff(c_3293, plain, (k2_zfmisc_1('#skF_4', '#skF_2')='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_3076, c_3283])).
% 4.41/1.79  tff(c_3071, plain, (![B_2, A_1]: (B_2='#skF_5' | A_1='#skF_5' | k2_zfmisc_1(A_1, B_2)!='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_3063, c_3063, c_3063, c_2])).
% 4.41/1.79  tff(c_3297, plain, ('#skF_5'='#skF_2' | '#skF_5'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_3293, c_3071])).
% 4.41/1.79  tff(c_3315, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3072, c_2061, c_3297])).
% 4.41/1.79  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.41/1.79  
% 4.41/1.79  Inference rules
% 4.41/1.79  ----------------------
% 4.41/1.79  #Ref     : 22
% 4.41/1.79  #Sup     : 796
% 4.41/1.79  #Fact    : 0
% 4.41/1.79  #Define  : 0
% 4.41/1.79  #Split   : 14
% 4.41/1.79  #Chain   : 0
% 4.41/1.79  #Close   : 0
% 4.41/1.79  
% 4.41/1.79  Ordering : KBO
% 4.41/1.79  
% 4.41/1.79  Simplification rules
% 4.41/1.79  ----------------------
% 4.41/1.79  #Subsume      : 183
% 4.41/1.79  #Demod        : 598
% 4.41/1.79  #Tautology    : 436
% 4.41/1.79  #SimpNegUnit  : 78
% 4.41/1.80  #BackRed      : 181
% 4.41/1.80  
% 4.41/1.80  #Partial instantiations: 0
% 4.41/1.80  #Strategies tried      : 1
% 4.41/1.80  
% 4.41/1.80  Timing (in seconds)
% 4.41/1.80  ----------------------
% 4.41/1.80  Preprocessing        : 0.29
% 4.41/1.80  Parsing              : 0.15
% 4.41/1.80  CNF conversion       : 0.02
% 4.41/1.80  Main loop            : 0.70
% 4.41/1.80  Inferencing          : 0.23
% 4.41/1.80  Reduction            : 0.22
% 4.41/1.80  Demodulation         : 0.15
% 4.41/1.80  BG Simplification    : 0.03
% 4.41/1.80  Subsumption          : 0.16
% 4.41/1.80  Abstraction          : 0.04
% 4.41/1.80  MUC search           : 0.00
% 4.41/1.80  Cooper               : 0.00
% 4.41/1.80  Total                : 1.06
% 4.41/1.80  Index Insertion      : 0.00
% 4.41/1.80  Index Deletion       : 0.00
% 4.41/1.80  Index Matching       : 0.00
% 4.41/1.80  BG Taut test         : 0.00
%------------------------------------------------------------------------------
