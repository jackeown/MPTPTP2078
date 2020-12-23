%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:37 EST 2020

% Result     : Theorem 3.54s
% Output     : CNFRefutation 3.54s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 300 expanded)
%              Number of leaves         :   34 ( 110 expanded)
%              Depth                    :   13
%              Number of atoms          :  137 ( 650 expanded)
%              Number of equality atoms :   96 ( 454 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k5_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_8 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_96,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ~ ( r1_tarski(k2_tarski(A,B),k2_tarski(C,D))
          & A != C
          & A != D ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_zfmisc_1)).

tff(f_63,axiom,(
    ! [A,B,C] : k5_enumset1(A,A,A,A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t89_enumset1)).

tff(f_65,axiom,(
    ! [A] : k5_enumset1(A,A,A,A,A,A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_enumset1)).

tff(f_61,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_tarski(B,C))
    <=> ~ ( A != k1_xboole_0
          & A != k1_tarski(B)
          & A != k1_tarski(C)
          & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).

tff(f_82,axiom,(
    ! [A,B] : r1_tarski(k1_tarski(A),k2_tarski(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_43,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( k3_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_zfmisc_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_50,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(c_68,plain,(
    '#skF_5' != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_70,plain,(
    '#skF_7' != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_476,plain,(
    ! [A_100,B_101,C_102] : k5_enumset1(A_100,A_100,A_100,A_100,A_100,B_101,C_102) = k1_enumset1(A_100,B_101,C_102) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_52,plain,(
    ! [A_26] : k5_enumset1(A_26,A_26,A_26,A_26,A_26,A_26,A_26) = k1_tarski(A_26) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_492,plain,(
    ! [C_103] : k1_enumset1(C_103,C_103,C_103) = k1_tarski(C_103) ),
    inference(superposition,[status(thm),theory(equality)],[c_476,c_52])).

tff(c_48,plain,(
    ! [A_21,B_22] : k1_enumset1(A_21,A_21,B_22) = k2_tarski(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_508,plain,(
    ! [C_104] : k2_tarski(C_104,C_104) = k1_tarski(C_104) ),
    inference(superposition,[status(thm),theory(equality)],[c_492,c_48])).

tff(c_62,plain,(
    ! [B_28,C_29] : r1_tarski(k1_xboole_0,k2_tarski(B_28,C_29)) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_546,plain,(
    ! [C_104] : r1_tarski(k1_xboole_0,k1_tarski(C_104)) ),
    inference(superposition,[status(thm),theory(equality)],[c_508,c_62])).

tff(c_72,plain,(
    r1_tarski(k2_tarski('#skF_5','#skF_6'),k2_tarski('#skF_7','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_653,plain,(
    ! [B_126,C_127,A_128] :
      ( k2_tarski(B_126,C_127) = A_128
      | k1_tarski(C_127) = A_128
      | k1_tarski(B_126) = A_128
      | k1_xboole_0 = A_128
      | ~ r1_tarski(A_128,k2_tarski(B_126,C_127)) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_681,plain,
    ( k2_tarski('#skF_7','#skF_8') = k2_tarski('#skF_5','#skF_6')
    | k2_tarski('#skF_5','#skF_6') = k1_tarski('#skF_8')
    | k2_tarski('#skF_5','#skF_6') = k1_tarski('#skF_7')
    | k2_tarski('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_72,c_653])).

tff(c_752,plain,(
    k2_tarski('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_681])).

tff(c_64,plain,(
    ! [A_30,B_31] : r1_tarski(k1_tarski(A_30),k2_tarski(A_30,B_31)) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_214,plain,(
    ! [B_65,A_66] :
      ( B_65 = A_66
      | ~ r1_tarski(B_65,A_66)
      | ~ r1_tarski(A_66,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_230,plain,(
    ! [A_30,B_31] :
      ( k2_tarski(A_30,B_31) = k1_tarski(A_30)
      | ~ r1_tarski(k2_tarski(A_30,B_31),k1_tarski(A_30)) ) ),
    inference(resolution,[status(thm)],[c_64,c_214])).

tff(c_776,plain,
    ( k2_tarski('#skF_5','#skF_6') = k1_tarski('#skF_5')
    | ~ r1_tarski(k1_xboole_0,k1_tarski('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_752,c_230])).

tff(c_821,plain,(
    k1_tarski('#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_546,c_752,c_776])).

tff(c_16,plain,(
    ! [A_9] : k4_xboole_0(k1_xboole_0,A_9) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | k4_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_106,plain,(
    ! [A_53,B_54] :
      ( k3_xboole_0(A_53,B_54) = A_53
      | ~ r1_tarski(A_53,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_276,plain,(
    ! [A_73,B_74] :
      ( k3_xboole_0(A_73,B_74) = A_73
      | k4_xboole_0(A_73,B_74) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_106])).

tff(c_297,plain,(
    ! [A_9] : k3_xboole_0(k1_xboole_0,A_9) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_276])).

tff(c_66,plain,(
    ! [B_33,A_32] :
      ( B_33 = A_32
      | k3_xboole_0(k1_tarski(A_32),k1_tarski(B_33)) != k1_tarski(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_869,plain,(
    ! [B_33] :
      ( B_33 = '#skF_5'
      | k3_xboole_0(k1_xboole_0,k1_tarski(B_33)) != k1_tarski('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_821,c_66])).

tff(c_923,plain,(
    ! [B_145] : B_145 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_821,c_297,c_869])).

tff(c_1133,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_923,c_70])).

tff(c_1135,plain,(
    k2_tarski('#skF_5','#skF_6') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_681])).

tff(c_131,plain,(
    ! [A_55,B_56] :
      ( k4_xboole_0(A_55,B_56) = k1_xboole_0
      | ~ r1_tarski(A_55,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_152,plain,(
    k4_xboole_0(k2_tarski('#skF_5','#skF_6'),k2_tarski('#skF_7','#skF_8')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_72,c_131])).

tff(c_719,plain,(
    ! [B_136,C_137,A_138] :
      ( k2_tarski(B_136,C_137) = A_138
      | k1_tarski(C_137) = A_138
      | k1_tarski(B_136) = A_138
      | k1_xboole_0 = A_138
      | k4_xboole_0(A_138,k2_tarski(B_136,C_137)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_653])).

tff(c_745,plain,
    ( k2_tarski('#skF_7','#skF_8') = k2_tarski('#skF_5','#skF_6')
    | k2_tarski('#skF_5','#skF_6') = k1_tarski('#skF_8')
    | k2_tarski('#skF_5','#skF_6') = k1_tarski('#skF_7')
    | k2_tarski('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_152,c_719])).

tff(c_1158,plain,
    ( k2_tarski('#skF_7','#skF_8') = k2_tarski('#skF_5','#skF_6')
    | k2_tarski('#skF_5','#skF_6') = k1_tarski('#skF_8')
    | k2_tarski('#skF_5','#skF_6') = k1_tarski('#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_1135,c_745])).

tff(c_1159,plain,(
    k2_tarski('#skF_5','#skF_6') = k1_tarski('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_1158])).

tff(c_32,plain,(
    ! [D_20,A_15] : r2_hidden(D_20,k2_tarski(A_15,D_20)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1214,plain,(
    r2_hidden('#skF_6',k1_tarski('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1159,c_32])).

tff(c_18,plain,(
    ! [C_14,A_10] :
      ( C_14 = A_10
      | ~ r2_hidden(C_14,k1_tarski(A_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1234,plain,(
    '#skF_7' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_1214,c_18])).

tff(c_1238,plain,(
    '#skF_5' != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1234,c_70])).

tff(c_34,plain,(
    ! [D_20,B_16] : r2_hidden(D_20,k2_tarski(D_20,B_16)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1219,plain,(
    r2_hidden('#skF_5',k1_tarski('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1159,c_34])).

tff(c_1245,plain,(
    r2_hidden('#skF_5',k1_tarski('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1234,c_1219])).

tff(c_1248,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_1245,c_18])).

tff(c_1252,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1238,c_1248])).

tff(c_1254,plain,(
    k2_tarski('#skF_5','#skF_6') != k1_tarski('#skF_7') ),
    inference(splitRight,[status(thm)],[c_1158])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_156,plain,(
    ! [B_2] : k4_xboole_0(B_2,B_2) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_131])).

tff(c_1134,plain,
    ( k2_tarski('#skF_5','#skF_6') = k1_tarski('#skF_7')
    | k2_tarski('#skF_5','#skF_6') = k1_tarski('#skF_8')
    | k2_tarski('#skF_7','#skF_8') = k2_tarski('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_681])).

tff(c_1147,plain,(
    k2_tarski('#skF_7','#skF_8') = k2_tarski('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_1134])).

tff(c_229,plain,
    ( k2_tarski('#skF_7','#skF_8') = k2_tarski('#skF_5','#skF_6')
    | ~ r1_tarski(k2_tarski('#skF_7','#skF_8'),k2_tarski('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_72,c_214])).

tff(c_416,plain,(
    ~ r1_tarski(k2_tarski('#skF_7','#skF_8'),k2_tarski('#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_229])).

tff(c_420,plain,(
    k4_xboole_0(k2_tarski('#skF_7','#skF_8'),k2_tarski('#skF_5','#skF_6')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_416])).

tff(c_1148,plain,(
    k4_xboole_0(k2_tarski('#skF_5','#skF_6'),k2_tarski('#skF_5','#skF_6')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1147,c_420])).

tff(c_1155,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_1148])).

tff(c_1156,plain,
    ( k2_tarski('#skF_5','#skF_6') = k1_tarski('#skF_8')
    | k2_tarski('#skF_5','#skF_6') = k1_tarski('#skF_7') ),
    inference(splitRight,[status(thm)],[c_1134])).

tff(c_1255,plain,(
    k2_tarski('#skF_5','#skF_6') = k1_tarski('#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_1254,c_1156])).

tff(c_1317,plain,(
    r2_hidden('#skF_5',k1_tarski('#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1255,c_34])).

tff(c_1342,plain,(
    '#skF_5' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_1317,c_18])).

tff(c_1346,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1342])).

tff(c_1347,plain,(
    k2_tarski('#skF_7','#skF_8') = k2_tarski('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_229])).

tff(c_1382,plain,(
    r2_hidden('#skF_8',k2_tarski('#skF_5','#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1347,c_32])).

tff(c_30,plain,(
    ! [D_20,B_16,A_15] :
      ( D_20 = B_16
      | D_20 = A_15
      | ~ r2_hidden(D_20,k2_tarski(A_15,B_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1395,plain,
    ( '#skF_6' = '#skF_8'
    | '#skF_5' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_1382,c_30])).

tff(c_1398,plain,(
    '#skF_6' = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1395])).

tff(c_1387,plain,(
    r2_hidden('#skF_7',k2_tarski('#skF_5','#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1347,c_34])).

tff(c_1406,plain,(
    r2_hidden('#skF_7',k2_tarski('#skF_5','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1398,c_1387])).

tff(c_1409,plain,
    ( '#skF_7' = '#skF_8'
    | '#skF_7' = '#skF_5' ),
    inference(resolution,[status(thm)],[c_1406,c_30])).

tff(c_1412,plain,(
    '#skF_7' = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_1409])).

tff(c_1400,plain,(
    k2_tarski('#skF_7','#skF_8') = k2_tarski('#skF_5','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1398,c_1347])).

tff(c_1422,plain,(
    k2_tarski('#skF_5','#skF_8') = k2_tarski('#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1412,c_1400])).

tff(c_1455,plain,(
    r2_hidden('#skF_5',k2_tarski('#skF_8','#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1422,c_34])).

tff(c_1468,plain,(
    '#skF_5' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_1455,c_30])).

tff(c_1472,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_68,c_1468])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:10:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.54/1.64  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.54/1.65  
% 3.54/1.65  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.54/1.65  %$ r2_hidden > r1_tarski > k5_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_8 > #skF_3 > #skF_2 > #skF_1
% 3.54/1.65  
% 3.54/1.65  %Foreground sorts:
% 3.54/1.65  
% 3.54/1.65  
% 3.54/1.65  %Background operators:
% 3.54/1.65  
% 3.54/1.65  
% 3.54/1.65  %Foreground operators:
% 3.54/1.65  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.54/1.65  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.54/1.65  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.54/1.65  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.54/1.65  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.54/1.65  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.54/1.65  tff('#skF_7', type, '#skF_7': $i).
% 3.54/1.65  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.54/1.65  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.54/1.65  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.54/1.65  tff('#skF_5', type, '#skF_5': $i).
% 3.54/1.65  tff('#skF_6', type, '#skF_6': $i).
% 3.54/1.65  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.54/1.65  tff('#skF_8', type, '#skF_8': $i).
% 3.54/1.65  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.54/1.65  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.54/1.65  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.54/1.65  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.54/1.65  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.54/1.65  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.54/1.65  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.54/1.65  
% 3.54/1.67  tff(f_96, negated_conjecture, ~(![A, B, C, D]: ~((r1_tarski(k2_tarski(A, B), k2_tarski(C, D)) & ~(A = C)) & ~(A = D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_zfmisc_1)).
% 3.54/1.67  tff(f_63, axiom, (![A, B, C]: (k5_enumset1(A, A, A, A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t89_enumset1)).
% 3.54/1.67  tff(f_65, axiom, (![A]: (k5_enumset1(A, A, A, A, A, A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_enumset1)).
% 3.54/1.67  tff(f_61, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 3.54/1.67  tff(f_80, axiom, (![A, B, C]: (r1_tarski(A, k2_tarski(B, C)) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l45_zfmisc_1)).
% 3.54/1.67  tff(f_82, axiom, (![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 3.54/1.67  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.54/1.67  tff(f_43, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 3.54/1.67  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.54/1.67  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.54/1.67  tff(f_86, axiom, (![A, B]: ((k3_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_zfmisc_1)).
% 3.54/1.67  tff(f_59, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 3.54/1.67  tff(f_50, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 3.54/1.67  tff(c_68, plain, ('#skF_5'!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.54/1.67  tff(c_70, plain, ('#skF_7'!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.54/1.67  tff(c_476, plain, (![A_100, B_101, C_102]: (k5_enumset1(A_100, A_100, A_100, A_100, A_100, B_101, C_102)=k1_enumset1(A_100, B_101, C_102))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.54/1.67  tff(c_52, plain, (![A_26]: (k5_enumset1(A_26, A_26, A_26, A_26, A_26, A_26, A_26)=k1_tarski(A_26))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.54/1.67  tff(c_492, plain, (![C_103]: (k1_enumset1(C_103, C_103, C_103)=k1_tarski(C_103))), inference(superposition, [status(thm), theory('equality')], [c_476, c_52])).
% 3.54/1.67  tff(c_48, plain, (![A_21, B_22]: (k1_enumset1(A_21, A_21, B_22)=k2_tarski(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.54/1.67  tff(c_508, plain, (![C_104]: (k2_tarski(C_104, C_104)=k1_tarski(C_104))), inference(superposition, [status(thm), theory('equality')], [c_492, c_48])).
% 3.54/1.67  tff(c_62, plain, (![B_28, C_29]: (r1_tarski(k1_xboole_0, k2_tarski(B_28, C_29)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.54/1.67  tff(c_546, plain, (![C_104]: (r1_tarski(k1_xboole_0, k1_tarski(C_104)))), inference(superposition, [status(thm), theory('equality')], [c_508, c_62])).
% 3.54/1.67  tff(c_72, plain, (r1_tarski(k2_tarski('#skF_5', '#skF_6'), k2_tarski('#skF_7', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.54/1.67  tff(c_653, plain, (![B_126, C_127, A_128]: (k2_tarski(B_126, C_127)=A_128 | k1_tarski(C_127)=A_128 | k1_tarski(B_126)=A_128 | k1_xboole_0=A_128 | ~r1_tarski(A_128, k2_tarski(B_126, C_127)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.54/1.67  tff(c_681, plain, (k2_tarski('#skF_7', '#skF_8')=k2_tarski('#skF_5', '#skF_6') | k2_tarski('#skF_5', '#skF_6')=k1_tarski('#skF_8') | k2_tarski('#skF_5', '#skF_6')=k1_tarski('#skF_7') | k2_tarski('#skF_5', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_72, c_653])).
% 3.54/1.67  tff(c_752, plain, (k2_tarski('#skF_5', '#skF_6')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_681])).
% 3.54/1.67  tff(c_64, plain, (![A_30, B_31]: (r1_tarski(k1_tarski(A_30), k2_tarski(A_30, B_31)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.54/1.67  tff(c_214, plain, (![B_65, A_66]: (B_65=A_66 | ~r1_tarski(B_65, A_66) | ~r1_tarski(A_66, B_65))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.54/1.67  tff(c_230, plain, (![A_30, B_31]: (k2_tarski(A_30, B_31)=k1_tarski(A_30) | ~r1_tarski(k2_tarski(A_30, B_31), k1_tarski(A_30)))), inference(resolution, [status(thm)], [c_64, c_214])).
% 3.54/1.67  tff(c_776, plain, (k2_tarski('#skF_5', '#skF_6')=k1_tarski('#skF_5') | ~r1_tarski(k1_xboole_0, k1_tarski('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_752, c_230])).
% 3.54/1.67  tff(c_821, plain, (k1_tarski('#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_546, c_752, c_776])).
% 3.54/1.67  tff(c_16, plain, (![A_9]: (k4_xboole_0(k1_xboole_0, A_9)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.54/1.67  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | k4_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.54/1.67  tff(c_106, plain, (![A_53, B_54]: (k3_xboole_0(A_53, B_54)=A_53 | ~r1_tarski(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.54/1.67  tff(c_276, plain, (![A_73, B_74]: (k3_xboole_0(A_73, B_74)=A_73 | k4_xboole_0(A_73, B_74)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_106])).
% 3.54/1.67  tff(c_297, plain, (![A_9]: (k3_xboole_0(k1_xboole_0, A_9)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_16, c_276])).
% 3.54/1.67  tff(c_66, plain, (![B_33, A_32]: (B_33=A_32 | k3_xboole_0(k1_tarski(A_32), k1_tarski(B_33))!=k1_tarski(A_32))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.54/1.67  tff(c_869, plain, (![B_33]: (B_33='#skF_5' | k3_xboole_0(k1_xboole_0, k1_tarski(B_33))!=k1_tarski('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_821, c_66])).
% 3.54/1.67  tff(c_923, plain, (![B_145]: (B_145='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_821, c_297, c_869])).
% 3.54/1.67  tff(c_1133, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_923, c_70])).
% 3.54/1.67  tff(c_1135, plain, (k2_tarski('#skF_5', '#skF_6')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_681])).
% 3.54/1.67  tff(c_131, plain, (![A_55, B_56]: (k4_xboole_0(A_55, B_56)=k1_xboole_0 | ~r1_tarski(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.54/1.67  tff(c_152, plain, (k4_xboole_0(k2_tarski('#skF_5', '#skF_6'), k2_tarski('#skF_7', '#skF_8'))=k1_xboole_0), inference(resolution, [status(thm)], [c_72, c_131])).
% 3.54/1.67  tff(c_719, plain, (![B_136, C_137, A_138]: (k2_tarski(B_136, C_137)=A_138 | k1_tarski(C_137)=A_138 | k1_tarski(B_136)=A_138 | k1_xboole_0=A_138 | k4_xboole_0(A_138, k2_tarski(B_136, C_137))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_653])).
% 3.54/1.67  tff(c_745, plain, (k2_tarski('#skF_7', '#skF_8')=k2_tarski('#skF_5', '#skF_6') | k2_tarski('#skF_5', '#skF_6')=k1_tarski('#skF_8') | k2_tarski('#skF_5', '#skF_6')=k1_tarski('#skF_7') | k2_tarski('#skF_5', '#skF_6')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_152, c_719])).
% 3.54/1.67  tff(c_1158, plain, (k2_tarski('#skF_7', '#skF_8')=k2_tarski('#skF_5', '#skF_6') | k2_tarski('#skF_5', '#skF_6')=k1_tarski('#skF_8') | k2_tarski('#skF_5', '#skF_6')=k1_tarski('#skF_7')), inference(negUnitSimplification, [status(thm)], [c_1135, c_745])).
% 3.54/1.67  tff(c_1159, plain, (k2_tarski('#skF_5', '#skF_6')=k1_tarski('#skF_7')), inference(splitLeft, [status(thm)], [c_1158])).
% 3.54/1.67  tff(c_32, plain, (![D_20, A_15]: (r2_hidden(D_20, k2_tarski(A_15, D_20)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.54/1.67  tff(c_1214, plain, (r2_hidden('#skF_6', k1_tarski('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_1159, c_32])).
% 3.54/1.67  tff(c_18, plain, (![C_14, A_10]: (C_14=A_10 | ~r2_hidden(C_14, k1_tarski(A_10)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.54/1.67  tff(c_1234, plain, ('#skF_7'='#skF_6'), inference(resolution, [status(thm)], [c_1214, c_18])).
% 3.54/1.67  tff(c_1238, plain, ('#skF_5'!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_1234, c_70])).
% 3.54/1.67  tff(c_34, plain, (![D_20, B_16]: (r2_hidden(D_20, k2_tarski(D_20, B_16)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.54/1.67  tff(c_1219, plain, (r2_hidden('#skF_5', k1_tarski('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_1159, c_34])).
% 3.54/1.67  tff(c_1245, plain, (r2_hidden('#skF_5', k1_tarski('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_1234, c_1219])).
% 3.54/1.67  tff(c_1248, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_1245, c_18])).
% 3.54/1.67  tff(c_1252, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1238, c_1248])).
% 3.54/1.67  tff(c_1254, plain, (k2_tarski('#skF_5', '#skF_6')!=k1_tarski('#skF_7')), inference(splitRight, [status(thm)], [c_1158])).
% 3.54/1.67  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.54/1.67  tff(c_156, plain, (![B_2]: (k4_xboole_0(B_2, B_2)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_131])).
% 3.54/1.67  tff(c_1134, plain, (k2_tarski('#skF_5', '#skF_6')=k1_tarski('#skF_7') | k2_tarski('#skF_5', '#skF_6')=k1_tarski('#skF_8') | k2_tarski('#skF_7', '#skF_8')=k2_tarski('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_681])).
% 3.54/1.67  tff(c_1147, plain, (k2_tarski('#skF_7', '#skF_8')=k2_tarski('#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_1134])).
% 3.54/1.67  tff(c_229, plain, (k2_tarski('#skF_7', '#skF_8')=k2_tarski('#skF_5', '#skF_6') | ~r1_tarski(k2_tarski('#skF_7', '#skF_8'), k2_tarski('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_72, c_214])).
% 3.54/1.67  tff(c_416, plain, (~r1_tarski(k2_tarski('#skF_7', '#skF_8'), k2_tarski('#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_229])).
% 3.54/1.67  tff(c_420, plain, (k4_xboole_0(k2_tarski('#skF_7', '#skF_8'), k2_tarski('#skF_5', '#skF_6'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_8, c_416])).
% 3.54/1.67  tff(c_1148, plain, (k4_xboole_0(k2_tarski('#skF_5', '#skF_6'), k2_tarski('#skF_5', '#skF_6'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1147, c_420])).
% 3.54/1.67  tff(c_1155, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_156, c_1148])).
% 3.54/1.67  tff(c_1156, plain, (k2_tarski('#skF_5', '#skF_6')=k1_tarski('#skF_8') | k2_tarski('#skF_5', '#skF_6')=k1_tarski('#skF_7')), inference(splitRight, [status(thm)], [c_1134])).
% 3.54/1.67  tff(c_1255, plain, (k2_tarski('#skF_5', '#skF_6')=k1_tarski('#skF_8')), inference(negUnitSimplification, [status(thm)], [c_1254, c_1156])).
% 3.54/1.67  tff(c_1317, plain, (r2_hidden('#skF_5', k1_tarski('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_1255, c_34])).
% 3.54/1.67  tff(c_1342, plain, ('#skF_5'='#skF_8'), inference(resolution, [status(thm)], [c_1317, c_18])).
% 3.54/1.67  tff(c_1346, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_1342])).
% 3.54/1.67  tff(c_1347, plain, (k2_tarski('#skF_7', '#skF_8')=k2_tarski('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_229])).
% 3.54/1.67  tff(c_1382, plain, (r2_hidden('#skF_8', k2_tarski('#skF_5', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_1347, c_32])).
% 3.54/1.67  tff(c_30, plain, (![D_20, B_16, A_15]: (D_20=B_16 | D_20=A_15 | ~r2_hidden(D_20, k2_tarski(A_15, B_16)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.54/1.67  tff(c_1395, plain, ('#skF_6'='#skF_8' | '#skF_5'='#skF_8'), inference(resolution, [status(thm)], [c_1382, c_30])).
% 3.54/1.67  tff(c_1398, plain, ('#skF_6'='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_68, c_1395])).
% 3.54/1.67  tff(c_1387, plain, (r2_hidden('#skF_7', k2_tarski('#skF_5', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_1347, c_34])).
% 3.54/1.67  tff(c_1406, plain, (r2_hidden('#skF_7', k2_tarski('#skF_5', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_1398, c_1387])).
% 3.54/1.67  tff(c_1409, plain, ('#skF_7'='#skF_8' | '#skF_7'='#skF_5'), inference(resolution, [status(thm)], [c_1406, c_30])).
% 3.54/1.67  tff(c_1412, plain, ('#skF_7'='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_70, c_1409])).
% 3.54/1.67  tff(c_1400, plain, (k2_tarski('#skF_7', '#skF_8')=k2_tarski('#skF_5', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1398, c_1347])).
% 3.54/1.67  tff(c_1422, plain, (k2_tarski('#skF_5', '#skF_8')=k2_tarski('#skF_8', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1412, c_1400])).
% 3.54/1.67  tff(c_1455, plain, (r2_hidden('#skF_5', k2_tarski('#skF_8', '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_1422, c_34])).
% 3.54/1.67  tff(c_1468, plain, ('#skF_5'='#skF_8'), inference(resolution, [status(thm)], [c_1455, c_30])).
% 3.54/1.67  tff(c_1472, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_68, c_1468])).
% 3.54/1.67  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.54/1.67  
% 3.54/1.67  Inference rules
% 3.54/1.67  ----------------------
% 3.54/1.67  #Ref     : 0
% 3.54/1.67  #Sup     : 373
% 3.54/1.67  #Fact    : 0
% 3.54/1.67  #Define  : 0
% 3.54/1.67  #Split   : 4
% 3.54/1.67  #Chain   : 0
% 3.54/1.67  #Close   : 0
% 3.54/1.67  
% 3.54/1.67  Ordering : KBO
% 3.54/1.67  
% 3.54/1.67  Simplification rules
% 3.54/1.67  ----------------------
% 3.54/1.67  #Subsume      : 44
% 3.54/1.67  #Demod        : 188
% 3.54/1.67  #Tautology    : 161
% 3.54/1.67  #SimpNegUnit  : 7
% 3.54/1.67  #BackRed      : 37
% 3.54/1.67  
% 3.54/1.67  #Partial instantiations: 128
% 3.54/1.67  #Strategies tried      : 1
% 3.54/1.67  
% 3.54/1.67  Timing (in seconds)
% 3.54/1.67  ----------------------
% 3.54/1.67  Preprocessing        : 0.33
% 3.54/1.67  Parsing              : 0.17
% 3.54/1.67  CNF conversion       : 0.03
% 3.54/1.67  Main loop            : 0.49
% 3.54/1.67  Inferencing          : 0.18
% 3.54/1.67  Reduction            : 0.16
% 3.54/1.67  Demodulation         : 0.11
% 3.54/1.67  BG Simplification    : 0.03
% 3.54/1.67  Subsumption          : 0.09
% 3.54/1.67  Abstraction          : 0.03
% 3.54/1.67  MUC search           : 0.00
% 3.54/1.67  Cooper               : 0.00
% 3.54/1.67  Total                : 0.86
% 3.54/1.67  Index Insertion      : 0.00
% 3.54/1.67  Index Deletion       : 0.00
% 3.54/1.67  Index Matching       : 0.00
% 3.54/1.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------
