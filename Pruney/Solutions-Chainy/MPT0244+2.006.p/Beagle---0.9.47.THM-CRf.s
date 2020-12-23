%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:57 EST 2020

% Result     : Theorem 5.50s
% Output     : CNFRefutation 5.74s
% Verified   : 
% Statistics : Number of formulae       :  187 (1649 expanded)
%              Number of leaves         :   32 ( 502 expanded)
%              Depth                    :   16
%              Number of atoms          :  273 (3456 expanded)
%              Number of equality atoms :  121 (1550 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_6 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_5 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_48,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_87,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_94,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(A,k1_tarski(B))
      <=> ( A = k1_xboole_0
          | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_zfmisc_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_42,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_69,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_54,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(c_26,plain,(
    ! [B_10] : r1_tarski(B_10,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_72,plain,(
    ! [A_49,B_50] :
      ( r1_tarski(k1_tarski(A_49),B_50)
      | ~ r2_hidden(A_49,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_74,plain,
    ( ~ r1_tarski('#skF_6',k1_tarski('#skF_7'))
    | k1_tarski('#skF_9') != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_102,plain,(
    k1_tarski('#skF_9') != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_84,plain,
    ( k1_tarski('#skF_7') = '#skF_6'
    | k1_xboole_0 = '#skF_6'
    | r1_tarski('#skF_8',k1_tarski('#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_234,plain,(
    r1_tarski('#skF_8',k1_tarski('#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_84])).

tff(c_22,plain,(
    ! [B_10,A_9] :
      ( B_10 = A_9
      | ~ r1_tarski(B_10,A_9)
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_236,plain,
    ( k1_tarski('#skF_9') = '#skF_8'
    | ~ r1_tarski(k1_tarski('#skF_9'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_234,c_22])).

tff(c_242,plain,(
    ~ r1_tarski(k1_tarski('#skF_9'),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_236])).

tff(c_247,plain,(
    ~ r2_hidden('#skF_9','#skF_8') ),
    inference(resolution,[status(thm)],[c_72,c_242])).

tff(c_78,plain,
    ( ~ r1_tarski('#skF_6',k1_tarski('#skF_7'))
    | k1_xboole_0 != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_100,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_78])).

tff(c_28,plain,(
    ! [A_11,B_12] :
      ( k3_xboole_0(A_11,B_12) = A_11
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_243,plain,(
    k3_xboole_0('#skF_8',k1_tarski('#skF_9')) = '#skF_8' ),
    inference(resolution,[status(thm)],[c_234,c_28])).

tff(c_20,plain,(
    ! [A_7] :
      ( r2_hidden('#skF_3'(A_7),A_7)
      | k1_xboole_0 = A_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_214,plain,(
    ! [D_82,A_83,B_84] :
      ( r2_hidden(D_82,A_83)
      | ~ r2_hidden(D_82,k3_xboole_0(A_83,B_84)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_396,plain,(
    ! [A_104,B_105] :
      ( r2_hidden('#skF_3'(k3_xboole_0(A_104,B_105)),A_104)
      | k3_xboole_0(A_104,B_105) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_20,c_214])).

tff(c_417,plain,
    ( r2_hidden('#skF_3'('#skF_8'),'#skF_8')
    | k3_xboole_0('#skF_8',k1_tarski('#skF_9')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_243,c_396])).

tff(c_430,plain,
    ( r2_hidden('#skF_3'('#skF_8'),'#skF_8')
    | k1_xboole_0 = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_243,c_417])).

tff(c_431,plain,(
    r2_hidden('#skF_3'('#skF_8'),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_430])).

tff(c_36,plain,(
    ! [E_20,A_14,C_16] : r2_hidden(E_20,k1_enumset1(A_14,E_20,C_16)) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_255,plain,(
    ! [D_86,B_87,A_88] :
      ( r2_hidden(D_86,B_87)
      | ~ r2_hidden(D_86,k3_xboole_0(A_88,B_87)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_258,plain,(
    ! [D_86] :
      ( r2_hidden(D_86,k1_tarski('#skF_9'))
      | ~ r2_hidden(D_86,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_243,c_255])).

tff(c_174,plain,(
    ! [A_77,B_78] :
      ( r1_tarski(k1_tarski(A_77),B_78)
      | ~ r2_hidden(A_77,B_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_286,plain,(
    ! [A_95,B_96] :
      ( k3_xboole_0(k1_tarski(A_95),B_96) = k1_tarski(A_95)
      | ~ r2_hidden(A_95,B_96) ) ),
    inference(resolution,[status(thm)],[c_174,c_28])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k3_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_443,plain,(
    ! [D_110,B_111,A_112] :
      ( r2_hidden(D_110,B_111)
      | ~ r2_hidden(D_110,k1_tarski(A_112))
      | ~ r2_hidden(A_112,B_111) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_286,c_4])).

tff(c_491,plain,(
    ! [D_114,B_115] :
      ( r2_hidden(D_114,B_115)
      | ~ r2_hidden('#skF_9',B_115)
      | ~ r2_hidden(D_114,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_258,c_443])).

tff(c_607,plain,(
    ! [D_130,A_131,C_132] :
      ( r2_hidden(D_130,k1_enumset1(A_131,'#skF_9',C_132))
      | ~ r2_hidden(D_130,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_36,c_491])).

tff(c_32,plain,(
    ! [E_20,C_16,B_15,A_14] :
      ( E_20 = C_16
      | E_20 = B_15
      | E_20 = A_14
      | ~ r2_hidden(E_20,k1_enumset1(A_14,B_15,C_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_648,plain,(
    ! [D_137,C_138,A_139] :
      ( D_137 = C_138
      | D_137 = '#skF_9'
      | D_137 = A_139
      | ~ r2_hidden(D_137,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_607,c_32])).

tff(c_664,plain,(
    ! [C_138,A_139] :
      ( C_138 = '#skF_3'('#skF_8')
      | '#skF_3'('#skF_8') = '#skF_9'
      | A_139 = '#skF_3'('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_431,c_648])).

tff(c_692,plain,(
    '#skF_3'('#skF_8') = '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_664])).

tff(c_705,plain,(
    r2_hidden('#skF_9','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_692,c_431])).

tff(c_708,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_247,c_705])).

tff(c_709,plain,(
    ! [A_139,C_138] :
      ( A_139 = '#skF_3'('#skF_8')
      | C_138 = '#skF_3'('#skF_8') ) ),
    inference(splitRight,[status(thm)],[c_664])).

tff(c_793,plain,(
    '#skF_3'('#skF_8') = '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_709])).

tff(c_794,plain,(
    r2_hidden('#skF_9','#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_793,c_431])).

tff(c_945,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_247,c_794])).

tff(c_1020,plain,(
    '#skF_3'('#skF_8') = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_709])).

tff(c_1021,plain,(
    r2_hidden('#skF_9','#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_1020,c_431])).

tff(c_1178,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_247,c_1021])).

tff(c_1179,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_tarski('#skF_7') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_1181,plain,(
    k1_tarski('#skF_7') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_1179])).

tff(c_82,plain,
    ( ~ r1_tarski('#skF_6',k1_tarski('#skF_7'))
    | r1_tarski('#skF_8',k1_tarski('#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_233,plain,(
    ~ r1_tarski('#skF_6',k1_tarski('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_82])).

tff(c_1182,plain,(
    ~ r1_tarski('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1181,c_233])).

tff(c_1185,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1182])).

tff(c_1186,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_1179])).

tff(c_30,plain,(
    ! [A_13] : r1_tarski(k1_xboole_0,A_13) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1193,plain,(
    ! [A_13] : r1_tarski('#skF_6',A_13) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1186,c_30])).

tff(c_1200,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1193,c_233])).

tff(c_1201,plain,(
    r1_tarski('#skF_8',k1_tarski('#skF_9')) ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_1203,plain,(
    r1_tarski('#skF_8',k1_tarski('#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_84])).

tff(c_1205,plain,
    ( k1_tarski('#skF_9') = '#skF_8'
    | ~ r1_tarski(k1_tarski('#skF_9'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_1203,c_22])).

tff(c_1211,plain,(
    ~ r1_tarski(k1_tarski('#skF_9'),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_1205])).

tff(c_1224,plain,(
    ~ r2_hidden('#skF_9','#skF_8') ),
    inference(resolution,[status(thm)],[c_72,c_1211])).

tff(c_1212,plain,(
    k3_xboole_0('#skF_8',k1_tarski('#skF_9')) = '#skF_8' ),
    inference(resolution,[status(thm)],[c_1203,c_28])).

tff(c_1202,plain,(
    r1_tarski('#skF_6',k1_tarski('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_1220,plain,(
    k3_xboole_0('#skF_6',k1_tarski('#skF_7')) = '#skF_6' ),
    inference(resolution,[status(thm)],[c_1202,c_28])).

tff(c_1225,plain,(
    ! [D_6046,B_6047,A_6048] :
      ( r2_hidden(D_6046,B_6047)
      | ~ r2_hidden(D_6046,k3_xboole_0(A_6048,B_6047)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1332,plain,(
    ! [A_6061,B_6062] :
      ( r2_hidden('#skF_3'(k3_xboole_0(A_6061,B_6062)),B_6062)
      | k3_xboole_0(A_6061,B_6062) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_20,c_1225])).

tff(c_1353,plain,
    ( r2_hidden('#skF_3'('#skF_6'),k1_tarski('#skF_7'))
    | k3_xboole_0('#skF_6',k1_tarski('#skF_7')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1220,c_1332])).

tff(c_1367,plain,
    ( r2_hidden('#skF_3'('#skF_6'),k1_tarski('#skF_7'))
    | k1_xboole_0 = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1220,c_1353])).

tff(c_1372,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_1367])).

tff(c_1378,plain,(
    '#skF_6' != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1372,c_100])).

tff(c_225,plain,(
    ! [A_83,B_84] :
      ( r2_hidden('#skF_3'(k3_xboole_0(A_83,B_84)),A_83)
      | k3_xboole_0(A_83,B_84) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_20,c_214])).

tff(c_1531,plain,(
    ! [A_6085,B_6086] :
      ( r2_hidden('#skF_3'(k3_xboole_0(A_6085,B_6086)),A_6085)
      | k3_xboole_0(A_6085,B_6086) = '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1372,c_225])).

tff(c_1559,plain,
    ( r2_hidden('#skF_3'('#skF_8'),'#skF_8')
    | k3_xboole_0('#skF_8',k1_tarski('#skF_9')) = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_1212,c_1531])).

tff(c_1571,plain,
    ( r2_hidden('#skF_3'('#skF_8'),'#skF_8')
    | '#skF_6' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1212,c_1559])).

tff(c_1572,plain,(
    r2_hidden('#skF_3'('#skF_8'),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_1378,c_1571])).

tff(c_1240,plain,(
    ! [D_6] :
      ( r2_hidden(D_6,k1_tarski('#skF_9'))
      | ~ r2_hidden(D_6,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1212,c_4])).

tff(c_1300,plain,(
    ! [A_6059,B_6060] :
      ( k3_xboole_0(k1_tarski(A_6059),B_6060) = k1_tarski(A_6059)
      | ~ r2_hidden(A_6059,B_6060) ) ),
    inference(resolution,[status(thm)],[c_174,c_28])).

tff(c_1574,plain,(
    ! [D_6087,B_6088,A_6089] :
      ( r2_hidden(D_6087,B_6088)
      | ~ r2_hidden(D_6087,k1_tarski(A_6089))
      | ~ r2_hidden(A_6089,B_6088) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1300,c_4])).

tff(c_1622,plain,(
    ! [D_6091,B_6092] :
      ( r2_hidden(D_6091,B_6092)
      | ~ r2_hidden('#skF_9',B_6092)
      | ~ r2_hidden(D_6091,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_1240,c_1574])).

tff(c_1695,plain,(
    ! [D_6106,A_6107,C_6108] :
      ( r2_hidden(D_6106,k1_enumset1(A_6107,'#skF_9',C_6108))
      | ~ r2_hidden(D_6106,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_36,c_1622])).

tff(c_1749,plain,(
    ! [D_6116,C_6117,A_6118] :
      ( D_6116 = C_6117
      | D_6116 = '#skF_9'
      | D_6116 = A_6118
      | ~ r2_hidden(D_6116,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_1695,c_32])).

tff(c_1762,plain,(
    ! [C_6117,A_6118] :
      ( C_6117 = '#skF_3'('#skF_8')
      | '#skF_3'('#skF_8') = '#skF_9'
      | A_6118 = '#skF_3'('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_1572,c_1749])).

tff(c_1841,plain,(
    '#skF_3'('#skF_8') = '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_1762])).

tff(c_1845,plain,(
    r2_hidden('#skF_9','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1841,c_1572])).

tff(c_1848,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1224,c_1845])).

tff(c_1850,plain,(
    '#skF_3'('#skF_8') != '#skF_9' ),
    inference(splitRight,[status(thm)],[c_1762])).

tff(c_1379,plain,(
    ! [A_7] :
      ( r2_hidden('#skF_3'(A_7),A_7)
      | A_7 = '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1372,c_20])).

tff(c_1760,plain,(
    ! [C_6117,A_6118] :
      ( C_6117 = '#skF_3'('#skF_8')
      | '#skF_3'('#skF_8') = '#skF_9'
      | A_6118 = '#skF_3'('#skF_8')
      | '#skF_6' = '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_1379,c_1749])).

tff(c_1766,plain,(
    ! [C_6117,A_6118] :
      ( C_6117 = '#skF_3'('#skF_8')
      | '#skF_3'('#skF_8') = '#skF_9'
      | A_6118 = '#skF_3'('#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_1378,c_1760])).

tff(c_1851,plain,(
    ! [C_6117,A_6118] :
      ( C_6117 = '#skF_3'('#skF_8')
      | A_6118 = '#skF_3'('#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_1850,c_1766])).

tff(c_1937,plain,(
    '#skF_3'('#skF_8') = '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_1851])).

tff(c_1938,plain,(
    r2_hidden('#skF_9','#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_1937,c_1572])).

tff(c_2084,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1224,c_1938])).

tff(c_2164,plain,(
    '#skF_3'('#skF_8') = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_1851])).

tff(c_2165,plain,(
    r2_hidden('#skF_9','#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_2164,c_1572])).

tff(c_2317,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1224,c_2165])).

tff(c_2318,plain,(
    r2_hidden('#skF_3'('#skF_6'),k1_tarski('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_1367])).

tff(c_2434,plain,(
    ! [D_12393,B_12394,A_12395] :
      ( r2_hidden(D_12393,B_12394)
      | ~ r2_hidden(D_12393,k1_tarski(A_12395))
      | ~ r2_hidden(A_12395,B_12394) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1300,c_4])).

tff(c_2491,plain,(
    ! [B_12397] :
      ( r2_hidden('#skF_3'('#skF_6'),B_12397)
      | ~ r2_hidden('#skF_7',B_12397) ) ),
    inference(resolution,[status(thm)],[c_2318,c_2434])).

tff(c_2854,plain,(
    ! [B_12446,A_12447] :
      ( r2_hidden('#skF_3'('#skF_6'),B_12446)
      | ~ r2_hidden('#skF_7',k3_xboole_0(A_12447,B_12446)) ) ),
    inference(resolution,[status(thm)],[c_2491,c_4])).

tff(c_2863,plain,
    ( r2_hidden('#skF_3'('#skF_6'),k1_tarski('#skF_9'))
    | ~ r2_hidden('#skF_7','#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_1212,c_2854])).

tff(c_2870,plain,(
    ~ r2_hidden('#skF_7','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_2863])).

tff(c_2531,plain,(
    ! [D_12403,B_12404] :
      ( r2_hidden(D_12403,B_12404)
      | ~ r2_hidden('#skF_9',B_12404)
      | ~ r2_hidden(D_12403,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_1240,c_2434])).

tff(c_2683,plain,(
    ! [D_12424,A_12425,C_12426] :
      ( r2_hidden(D_12424,k1_enumset1(A_12425,'#skF_9',C_12426))
      | ~ r2_hidden(D_12424,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_36,c_2531])).

tff(c_2918,plain,(
    ! [D_12453,C_12454,A_12455] :
      ( D_12453 = C_12454
      | D_12453 = '#skF_9'
      | D_12453 = A_12455
      | ~ r2_hidden(D_12453,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_2683,c_32])).

tff(c_2939,plain,(
    ! [C_12454,A_12455] :
      ( C_12454 = '#skF_3'('#skF_8')
      | '#skF_3'('#skF_8') = '#skF_9'
      | A_12455 = '#skF_3'('#skF_8')
      | k1_xboole_0 = '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_20,c_2918])).

tff(c_2948,plain,(
    ! [C_12454,A_12455] :
      ( C_12454 = '#skF_3'('#skF_8')
      | '#skF_3'('#skF_8') = '#skF_9'
      | A_12455 = '#skF_3'('#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_2939])).

tff(c_3082,plain,(
    '#skF_3'('#skF_8') = '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_2948])).

tff(c_2357,plain,(
    ! [A_12387,B_12388] :
      ( r2_hidden('#skF_3'(k3_xboole_0(A_12387,B_12388)),A_12387)
      | k3_xboole_0(A_12387,B_12388) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_20,c_214])).

tff(c_2381,plain,
    ( r2_hidden('#skF_3'('#skF_8'),'#skF_8')
    | k3_xboole_0('#skF_8',k1_tarski('#skF_9')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1212,c_2357])).

tff(c_2396,plain,
    ( r2_hidden('#skF_3'('#skF_8'),'#skF_8')
    | k1_xboole_0 = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1212,c_2381])).

tff(c_2397,plain,(
    r2_hidden('#skF_3'('#skF_8'),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_2396])).

tff(c_3086,plain,(
    r2_hidden('#skF_9','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3082,c_2397])).

tff(c_3089,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1224,c_3086])).

tff(c_3090,plain,(
    ! [A_12455,C_12454] :
      ( A_12455 = '#skF_3'('#skF_8')
      | C_12454 = '#skF_3'('#skF_8') ) ),
    inference(splitRight,[status(thm)],[c_2948])).

tff(c_3219,plain,(
    '#skF_3'('#skF_8') = '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_3090])).

tff(c_3220,plain,(
    r2_hidden('#skF_9','#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_3219,c_2397])).

tff(c_3394,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1224,c_3220])).

tff(c_3519,plain,(
    '#skF_3'('#skF_8') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_3090])).

tff(c_3520,plain,(
    r2_hidden('#skF_7','#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_3519,c_2397])).

tff(c_3697,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2870,c_3520])).

tff(c_3699,plain,(
    r2_hidden('#skF_7','#skF_8') ),
    inference(splitRight,[status(thm)],[c_2863])).

tff(c_34,plain,(
    ! [E_20,A_14,B_15] : r2_hidden(E_20,k1_enumset1(A_14,B_15,E_20)) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_2716,plain,(
    ! [D_12429,A_12430,B_12431] :
      ( r2_hidden(D_12429,k1_enumset1(A_12430,B_12431,'#skF_9'))
      | ~ r2_hidden(D_12429,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_34,c_2531])).

tff(c_3890,plain,(
    ! [D_20849,B_20850,A_20851] :
      ( D_20849 = '#skF_9'
      | D_20849 = B_20850
      | D_20849 = A_20851
      | ~ r2_hidden(D_20849,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_2716,c_32])).

tff(c_3921,plain,(
    ! [B_20850,A_20851] :
      ( '#skF_7' = '#skF_9'
      | B_20850 = '#skF_7'
      | A_20851 = '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_3699,c_3890])).

tff(c_4001,plain,(
    '#skF_7' = '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_3921])).

tff(c_4003,plain,(
    r2_hidden('#skF_9','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4001,c_3699])).

tff(c_4020,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1224,c_4003])).

tff(c_4021,plain,(
    ! [A_20851,B_20850] :
      ( A_20851 = '#skF_7'
      | B_20850 = '#skF_7' ) ),
    inference(splitRight,[status(thm)],[c_3921])).

tff(c_4070,plain,(
    '#skF_7' = '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_4021])).

tff(c_4071,plain,(
    r2_hidden('#skF_9','#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_4070,c_3699])).

tff(c_4316,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1224,c_4071])).

tff(c_4354,plain,(
    '#skF_7' = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_4021])).

tff(c_4355,plain,(
    r2_hidden('#skF_9','#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_4354,c_3699])).

tff(c_4600,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1224,c_4355])).

tff(c_4602,plain,(
    ~ r1_tarski('#skF_8',k1_tarski('#skF_9')) ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_4613,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1201,c_4602])).

tff(c_4615,plain,(
    k1_tarski('#skF_9') = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_76,plain,
    ( k1_tarski('#skF_7') = '#skF_6'
    | k1_xboole_0 = '#skF_6'
    | k1_tarski('#skF_9') != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_4621,plain,
    ( k1_tarski('#skF_7') = '#skF_6'
    | k1_xboole_0 = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4615,c_76])).

tff(c_4622,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_4621])).

tff(c_4625,plain,(
    ! [A_13] : r1_tarski('#skF_6',A_13) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4622,c_30])).

tff(c_4614,plain,(
    ~ r1_tarski('#skF_6',k1_tarski('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_4632,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4625,c_4614])).

tff(c_4633,plain,(
    k1_tarski('#skF_7') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_4621])).

tff(c_4635,plain,(
    ~ r1_tarski('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4633,c_4614])).

tff(c_4638,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_4635])).

tff(c_4640,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_4642,plain,(
    ! [A_13] : r1_tarski('#skF_8',A_13) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4640,c_30])).

tff(c_80,plain,
    ( k1_tarski('#skF_7') = '#skF_6'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_4650,plain,
    ( k1_tarski('#skF_7') = '#skF_6'
    | '#skF_6' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4640,c_4640,c_80])).

tff(c_4651,plain,(
    '#skF_6' = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_4650])).

tff(c_4639,plain,(
    ~ r1_tarski('#skF_6',k1_tarski('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_4652,plain,(
    ~ r1_tarski('#skF_8',k1_tarski('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4651,c_4639])).

tff(c_4655,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4642,c_4652])).

tff(c_4656,plain,(
    k1_tarski('#skF_7') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_4650])).

tff(c_4658,plain,(
    ~ r1_tarski('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4656,c_4639])).

tff(c_4661,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_4658])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:21:21 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.50/2.09  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.62/2.12  
% 5.62/2.12  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.62/2.12  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_6 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_5 > #skF_3
% 5.62/2.12  
% 5.62/2.12  %Foreground sorts:
% 5.62/2.12  
% 5.62/2.12  
% 5.62/2.12  %Background operators:
% 5.62/2.12  
% 5.62/2.12  
% 5.62/2.12  %Foreground operators:
% 5.62/2.12  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 5.62/2.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.62/2.12  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.62/2.12  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.62/2.12  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.62/2.12  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 5.62/2.12  tff('#skF_7', type, '#skF_7': $i).
% 5.62/2.12  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.62/2.12  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.62/2.12  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.62/2.12  tff('#skF_6', type, '#skF_6': $i).
% 5.62/2.12  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.62/2.12  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.62/2.12  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.62/2.12  tff('#skF_9', type, '#skF_9': $i).
% 5.62/2.12  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 5.62/2.12  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 5.62/2.12  tff('#skF_8', type, '#skF_8': $i).
% 5.62/2.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.62/2.12  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 5.62/2.12  tff('#skF_3', type, '#skF_3': $i > $i).
% 5.62/2.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.62/2.12  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.62/2.12  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 5.62/2.12  
% 5.74/2.14  tff(f_48, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.74/2.14  tff(f_87, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 5.74/2.14  tff(f_94, negated_conjecture, ~(![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_zfmisc_1)).
% 5.74/2.14  tff(f_52, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 5.74/2.14  tff(f_42, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 5.74/2.14  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 5.74/2.14  tff(f_69, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 5.74/2.14  tff(f_54, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 5.74/2.14  tff(c_26, plain, (![B_10]: (r1_tarski(B_10, B_10))), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.74/2.14  tff(c_72, plain, (![A_49, B_50]: (r1_tarski(k1_tarski(A_49), B_50) | ~r2_hidden(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.74/2.14  tff(c_74, plain, (~r1_tarski('#skF_6', k1_tarski('#skF_7')) | k1_tarski('#skF_9')!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_94])).
% 5.74/2.14  tff(c_102, plain, (k1_tarski('#skF_9')!='#skF_8'), inference(splitLeft, [status(thm)], [c_74])).
% 5.74/2.14  tff(c_84, plain, (k1_tarski('#skF_7')='#skF_6' | k1_xboole_0='#skF_6' | r1_tarski('#skF_8', k1_tarski('#skF_9'))), inference(cnfTransformation, [status(thm)], [f_94])).
% 5.74/2.14  tff(c_234, plain, (r1_tarski('#skF_8', k1_tarski('#skF_9'))), inference(splitLeft, [status(thm)], [c_84])).
% 5.74/2.14  tff(c_22, plain, (![B_10, A_9]: (B_10=A_9 | ~r1_tarski(B_10, A_9) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.74/2.14  tff(c_236, plain, (k1_tarski('#skF_9')='#skF_8' | ~r1_tarski(k1_tarski('#skF_9'), '#skF_8')), inference(resolution, [status(thm)], [c_234, c_22])).
% 5.74/2.14  tff(c_242, plain, (~r1_tarski(k1_tarski('#skF_9'), '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_102, c_236])).
% 5.74/2.14  tff(c_247, plain, (~r2_hidden('#skF_9', '#skF_8')), inference(resolution, [status(thm)], [c_72, c_242])).
% 5.74/2.14  tff(c_78, plain, (~r1_tarski('#skF_6', k1_tarski('#skF_7')) | k1_xboole_0!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_94])).
% 5.74/2.14  tff(c_100, plain, (k1_xboole_0!='#skF_8'), inference(splitLeft, [status(thm)], [c_78])).
% 5.74/2.14  tff(c_28, plain, (![A_11, B_12]: (k3_xboole_0(A_11, B_12)=A_11 | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.74/2.14  tff(c_243, plain, (k3_xboole_0('#skF_8', k1_tarski('#skF_9'))='#skF_8'), inference(resolution, [status(thm)], [c_234, c_28])).
% 5.74/2.14  tff(c_20, plain, (![A_7]: (r2_hidden('#skF_3'(A_7), A_7) | k1_xboole_0=A_7)), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.74/2.14  tff(c_214, plain, (![D_82, A_83, B_84]: (r2_hidden(D_82, A_83) | ~r2_hidden(D_82, k3_xboole_0(A_83, B_84)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.74/2.14  tff(c_396, plain, (![A_104, B_105]: (r2_hidden('#skF_3'(k3_xboole_0(A_104, B_105)), A_104) | k3_xboole_0(A_104, B_105)=k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_214])).
% 5.74/2.14  tff(c_417, plain, (r2_hidden('#skF_3'('#skF_8'), '#skF_8') | k3_xboole_0('#skF_8', k1_tarski('#skF_9'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_243, c_396])).
% 5.74/2.14  tff(c_430, plain, (r2_hidden('#skF_3'('#skF_8'), '#skF_8') | k1_xboole_0='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_243, c_417])).
% 5.74/2.14  tff(c_431, plain, (r2_hidden('#skF_3'('#skF_8'), '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_100, c_430])).
% 5.74/2.14  tff(c_36, plain, (![E_20, A_14, C_16]: (r2_hidden(E_20, k1_enumset1(A_14, E_20, C_16)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.74/2.14  tff(c_255, plain, (![D_86, B_87, A_88]: (r2_hidden(D_86, B_87) | ~r2_hidden(D_86, k3_xboole_0(A_88, B_87)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.74/2.14  tff(c_258, plain, (![D_86]: (r2_hidden(D_86, k1_tarski('#skF_9')) | ~r2_hidden(D_86, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_243, c_255])).
% 5.74/2.14  tff(c_174, plain, (![A_77, B_78]: (r1_tarski(k1_tarski(A_77), B_78) | ~r2_hidden(A_77, B_78))), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.74/2.14  tff(c_286, plain, (![A_95, B_96]: (k3_xboole_0(k1_tarski(A_95), B_96)=k1_tarski(A_95) | ~r2_hidden(A_95, B_96))), inference(resolution, [status(thm)], [c_174, c_28])).
% 5.74/2.14  tff(c_4, plain, (![D_6, B_2, A_1]: (r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k3_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.74/2.14  tff(c_443, plain, (![D_110, B_111, A_112]: (r2_hidden(D_110, B_111) | ~r2_hidden(D_110, k1_tarski(A_112)) | ~r2_hidden(A_112, B_111))), inference(superposition, [status(thm), theory('equality')], [c_286, c_4])).
% 5.74/2.14  tff(c_491, plain, (![D_114, B_115]: (r2_hidden(D_114, B_115) | ~r2_hidden('#skF_9', B_115) | ~r2_hidden(D_114, '#skF_8'))), inference(resolution, [status(thm)], [c_258, c_443])).
% 5.74/2.14  tff(c_607, plain, (![D_130, A_131, C_132]: (r2_hidden(D_130, k1_enumset1(A_131, '#skF_9', C_132)) | ~r2_hidden(D_130, '#skF_8'))), inference(resolution, [status(thm)], [c_36, c_491])).
% 5.74/2.14  tff(c_32, plain, (![E_20, C_16, B_15, A_14]: (E_20=C_16 | E_20=B_15 | E_20=A_14 | ~r2_hidden(E_20, k1_enumset1(A_14, B_15, C_16)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.74/2.14  tff(c_648, plain, (![D_137, C_138, A_139]: (D_137=C_138 | D_137='#skF_9' | D_137=A_139 | ~r2_hidden(D_137, '#skF_8'))), inference(resolution, [status(thm)], [c_607, c_32])).
% 5.74/2.14  tff(c_664, plain, (![C_138, A_139]: (C_138='#skF_3'('#skF_8') | '#skF_3'('#skF_8')='#skF_9' | A_139='#skF_3'('#skF_8'))), inference(resolution, [status(thm)], [c_431, c_648])).
% 5.74/2.14  tff(c_692, plain, ('#skF_3'('#skF_8')='#skF_9'), inference(splitLeft, [status(thm)], [c_664])).
% 5.74/2.14  tff(c_705, plain, (r2_hidden('#skF_9', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_692, c_431])).
% 5.74/2.14  tff(c_708, plain, $false, inference(negUnitSimplification, [status(thm)], [c_247, c_705])).
% 5.74/2.14  tff(c_709, plain, (![A_139, C_138]: (A_139='#skF_3'('#skF_8') | C_138='#skF_3'('#skF_8'))), inference(splitRight, [status(thm)], [c_664])).
% 5.74/2.14  tff(c_793, plain, ('#skF_3'('#skF_8')='#skF_9'), inference(splitLeft, [status(thm)], [c_709])).
% 5.74/2.14  tff(c_794, plain, (r2_hidden('#skF_9', '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_793, c_431])).
% 5.74/2.14  tff(c_945, plain, $false, inference(negUnitSimplification, [status(thm)], [c_247, c_794])).
% 5.74/2.14  tff(c_1020, plain, ('#skF_3'('#skF_8')='#skF_9'), inference(splitRight, [status(thm)], [c_709])).
% 5.74/2.14  tff(c_1021, plain, (r2_hidden('#skF_9', '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_1020, c_431])).
% 5.74/2.14  tff(c_1178, plain, $false, inference(negUnitSimplification, [status(thm)], [c_247, c_1021])).
% 5.74/2.14  tff(c_1179, plain, (k1_xboole_0='#skF_6' | k1_tarski('#skF_7')='#skF_6'), inference(splitRight, [status(thm)], [c_84])).
% 5.74/2.14  tff(c_1181, plain, (k1_tarski('#skF_7')='#skF_6'), inference(splitLeft, [status(thm)], [c_1179])).
% 5.74/2.14  tff(c_82, plain, (~r1_tarski('#skF_6', k1_tarski('#skF_7')) | r1_tarski('#skF_8', k1_tarski('#skF_9'))), inference(cnfTransformation, [status(thm)], [f_94])).
% 5.74/2.14  tff(c_233, plain, (~r1_tarski('#skF_6', k1_tarski('#skF_7'))), inference(splitLeft, [status(thm)], [c_82])).
% 5.74/2.14  tff(c_1182, plain, (~r1_tarski('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1181, c_233])).
% 5.74/2.14  tff(c_1185, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_1182])).
% 5.74/2.14  tff(c_1186, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_1179])).
% 5.74/2.14  tff(c_30, plain, (![A_13]: (r1_tarski(k1_xboole_0, A_13))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.74/2.14  tff(c_1193, plain, (![A_13]: (r1_tarski('#skF_6', A_13))), inference(demodulation, [status(thm), theory('equality')], [c_1186, c_30])).
% 5.74/2.14  tff(c_1200, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1193, c_233])).
% 5.74/2.14  tff(c_1201, plain, (r1_tarski('#skF_8', k1_tarski('#skF_9'))), inference(splitRight, [status(thm)], [c_82])).
% 5.74/2.14  tff(c_1203, plain, (r1_tarski('#skF_8', k1_tarski('#skF_9'))), inference(splitLeft, [status(thm)], [c_84])).
% 5.74/2.14  tff(c_1205, plain, (k1_tarski('#skF_9')='#skF_8' | ~r1_tarski(k1_tarski('#skF_9'), '#skF_8')), inference(resolution, [status(thm)], [c_1203, c_22])).
% 5.74/2.14  tff(c_1211, plain, (~r1_tarski(k1_tarski('#skF_9'), '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_102, c_1205])).
% 5.74/2.14  tff(c_1224, plain, (~r2_hidden('#skF_9', '#skF_8')), inference(resolution, [status(thm)], [c_72, c_1211])).
% 5.74/2.14  tff(c_1212, plain, (k3_xboole_0('#skF_8', k1_tarski('#skF_9'))='#skF_8'), inference(resolution, [status(thm)], [c_1203, c_28])).
% 5.74/2.14  tff(c_1202, plain, (r1_tarski('#skF_6', k1_tarski('#skF_7'))), inference(splitRight, [status(thm)], [c_82])).
% 5.74/2.14  tff(c_1220, plain, (k3_xboole_0('#skF_6', k1_tarski('#skF_7'))='#skF_6'), inference(resolution, [status(thm)], [c_1202, c_28])).
% 5.74/2.14  tff(c_1225, plain, (![D_6046, B_6047, A_6048]: (r2_hidden(D_6046, B_6047) | ~r2_hidden(D_6046, k3_xboole_0(A_6048, B_6047)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.74/2.14  tff(c_1332, plain, (![A_6061, B_6062]: (r2_hidden('#skF_3'(k3_xboole_0(A_6061, B_6062)), B_6062) | k3_xboole_0(A_6061, B_6062)=k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_1225])).
% 5.74/2.14  tff(c_1353, plain, (r2_hidden('#skF_3'('#skF_6'), k1_tarski('#skF_7')) | k3_xboole_0('#skF_6', k1_tarski('#skF_7'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1220, c_1332])).
% 5.74/2.14  tff(c_1367, plain, (r2_hidden('#skF_3'('#skF_6'), k1_tarski('#skF_7')) | k1_xboole_0='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_1220, c_1353])).
% 5.74/2.14  tff(c_1372, plain, (k1_xboole_0='#skF_6'), inference(splitLeft, [status(thm)], [c_1367])).
% 5.74/2.14  tff(c_1378, plain, ('#skF_6'!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_1372, c_100])).
% 5.74/2.14  tff(c_225, plain, (![A_83, B_84]: (r2_hidden('#skF_3'(k3_xboole_0(A_83, B_84)), A_83) | k3_xboole_0(A_83, B_84)=k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_214])).
% 5.74/2.14  tff(c_1531, plain, (![A_6085, B_6086]: (r2_hidden('#skF_3'(k3_xboole_0(A_6085, B_6086)), A_6085) | k3_xboole_0(A_6085, B_6086)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1372, c_225])).
% 5.74/2.14  tff(c_1559, plain, (r2_hidden('#skF_3'('#skF_8'), '#skF_8') | k3_xboole_0('#skF_8', k1_tarski('#skF_9'))='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_1212, c_1531])).
% 5.74/2.14  tff(c_1571, plain, (r2_hidden('#skF_3'('#skF_8'), '#skF_8') | '#skF_6'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_1212, c_1559])).
% 5.74/2.14  tff(c_1572, plain, (r2_hidden('#skF_3'('#skF_8'), '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_1378, c_1571])).
% 5.74/2.14  tff(c_1240, plain, (![D_6]: (r2_hidden(D_6, k1_tarski('#skF_9')) | ~r2_hidden(D_6, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_1212, c_4])).
% 5.74/2.14  tff(c_1300, plain, (![A_6059, B_6060]: (k3_xboole_0(k1_tarski(A_6059), B_6060)=k1_tarski(A_6059) | ~r2_hidden(A_6059, B_6060))), inference(resolution, [status(thm)], [c_174, c_28])).
% 5.74/2.14  tff(c_1574, plain, (![D_6087, B_6088, A_6089]: (r2_hidden(D_6087, B_6088) | ~r2_hidden(D_6087, k1_tarski(A_6089)) | ~r2_hidden(A_6089, B_6088))), inference(superposition, [status(thm), theory('equality')], [c_1300, c_4])).
% 5.74/2.14  tff(c_1622, plain, (![D_6091, B_6092]: (r2_hidden(D_6091, B_6092) | ~r2_hidden('#skF_9', B_6092) | ~r2_hidden(D_6091, '#skF_8'))), inference(resolution, [status(thm)], [c_1240, c_1574])).
% 5.74/2.14  tff(c_1695, plain, (![D_6106, A_6107, C_6108]: (r2_hidden(D_6106, k1_enumset1(A_6107, '#skF_9', C_6108)) | ~r2_hidden(D_6106, '#skF_8'))), inference(resolution, [status(thm)], [c_36, c_1622])).
% 5.74/2.14  tff(c_1749, plain, (![D_6116, C_6117, A_6118]: (D_6116=C_6117 | D_6116='#skF_9' | D_6116=A_6118 | ~r2_hidden(D_6116, '#skF_8'))), inference(resolution, [status(thm)], [c_1695, c_32])).
% 5.74/2.14  tff(c_1762, plain, (![C_6117, A_6118]: (C_6117='#skF_3'('#skF_8') | '#skF_3'('#skF_8')='#skF_9' | A_6118='#skF_3'('#skF_8'))), inference(resolution, [status(thm)], [c_1572, c_1749])).
% 5.74/2.14  tff(c_1841, plain, ('#skF_3'('#skF_8')='#skF_9'), inference(splitLeft, [status(thm)], [c_1762])).
% 5.74/2.14  tff(c_1845, plain, (r2_hidden('#skF_9', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1841, c_1572])).
% 5.74/2.14  tff(c_1848, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1224, c_1845])).
% 5.74/2.14  tff(c_1850, plain, ('#skF_3'('#skF_8')!='#skF_9'), inference(splitRight, [status(thm)], [c_1762])).
% 5.74/2.14  tff(c_1379, plain, (![A_7]: (r2_hidden('#skF_3'(A_7), A_7) | A_7='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1372, c_20])).
% 5.74/2.14  tff(c_1760, plain, (![C_6117, A_6118]: (C_6117='#skF_3'('#skF_8') | '#skF_3'('#skF_8')='#skF_9' | A_6118='#skF_3'('#skF_8') | '#skF_6'='#skF_8')), inference(resolution, [status(thm)], [c_1379, c_1749])).
% 5.74/2.14  tff(c_1766, plain, (![C_6117, A_6118]: (C_6117='#skF_3'('#skF_8') | '#skF_3'('#skF_8')='#skF_9' | A_6118='#skF_3'('#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_1378, c_1760])).
% 5.74/2.14  tff(c_1851, plain, (![C_6117, A_6118]: (C_6117='#skF_3'('#skF_8') | A_6118='#skF_3'('#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_1850, c_1766])).
% 5.74/2.14  tff(c_1937, plain, ('#skF_3'('#skF_8')='#skF_9'), inference(splitLeft, [status(thm)], [c_1851])).
% 5.74/2.14  tff(c_1938, plain, (r2_hidden('#skF_9', '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_1937, c_1572])).
% 5.74/2.14  tff(c_2084, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1224, c_1938])).
% 5.74/2.14  tff(c_2164, plain, ('#skF_3'('#skF_8')='#skF_9'), inference(splitRight, [status(thm)], [c_1851])).
% 5.74/2.14  tff(c_2165, plain, (r2_hidden('#skF_9', '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_2164, c_1572])).
% 5.74/2.14  tff(c_2317, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1224, c_2165])).
% 5.74/2.14  tff(c_2318, plain, (r2_hidden('#skF_3'('#skF_6'), k1_tarski('#skF_7'))), inference(splitRight, [status(thm)], [c_1367])).
% 5.74/2.14  tff(c_2434, plain, (![D_12393, B_12394, A_12395]: (r2_hidden(D_12393, B_12394) | ~r2_hidden(D_12393, k1_tarski(A_12395)) | ~r2_hidden(A_12395, B_12394))), inference(superposition, [status(thm), theory('equality')], [c_1300, c_4])).
% 5.74/2.14  tff(c_2491, plain, (![B_12397]: (r2_hidden('#skF_3'('#skF_6'), B_12397) | ~r2_hidden('#skF_7', B_12397))), inference(resolution, [status(thm)], [c_2318, c_2434])).
% 5.74/2.14  tff(c_2854, plain, (![B_12446, A_12447]: (r2_hidden('#skF_3'('#skF_6'), B_12446) | ~r2_hidden('#skF_7', k3_xboole_0(A_12447, B_12446)))), inference(resolution, [status(thm)], [c_2491, c_4])).
% 5.74/2.14  tff(c_2863, plain, (r2_hidden('#skF_3'('#skF_6'), k1_tarski('#skF_9')) | ~r2_hidden('#skF_7', '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_1212, c_2854])).
% 5.74/2.14  tff(c_2870, plain, (~r2_hidden('#skF_7', '#skF_8')), inference(splitLeft, [status(thm)], [c_2863])).
% 5.74/2.14  tff(c_2531, plain, (![D_12403, B_12404]: (r2_hidden(D_12403, B_12404) | ~r2_hidden('#skF_9', B_12404) | ~r2_hidden(D_12403, '#skF_8'))), inference(resolution, [status(thm)], [c_1240, c_2434])).
% 5.74/2.14  tff(c_2683, plain, (![D_12424, A_12425, C_12426]: (r2_hidden(D_12424, k1_enumset1(A_12425, '#skF_9', C_12426)) | ~r2_hidden(D_12424, '#skF_8'))), inference(resolution, [status(thm)], [c_36, c_2531])).
% 5.74/2.14  tff(c_2918, plain, (![D_12453, C_12454, A_12455]: (D_12453=C_12454 | D_12453='#skF_9' | D_12453=A_12455 | ~r2_hidden(D_12453, '#skF_8'))), inference(resolution, [status(thm)], [c_2683, c_32])).
% 5.74/2.14  tff(c_2939, plain, (![C_12454, A_12455]: (C_12454='#skF_3'('#skF_8') | '#skF_3'('#skF_8')='#skF_9' | A_12455='#skF_3'('#skF_8') | k1_xboole_0='#skF_8')), inference(resolution, [status(thm)], [c_20, c_2918])).
% 5.74/2.14  tff(c_2948, plain, (![C_12454, A_12455]: (C_12454='#skF_3'('#skF_8') | '#skF_3'('#skF_8')='#skF_9' | A_12455='#skF_3'('#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_100, c_2939])).
% 5.74/2.15  tff(c_3082, plain, ('#skF_3'('#skF_8')='#skF_9'), inference(splitLeft, [status(thm)], [c_2948])).
% 5.74/2.15  tff(c_2357, plain, (![A_12387, B_12388]: (r2_hidden('#skF_3'(k3_xboole_0(A_12387, B_12388)), A_12387) | k3_xboole_0(A_12387, B_12388)=k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_214])).
% 5.74/2.15  tff(c_2381, plain, (r2_hidden('#skF_3'('#skF_8'), '#skF_8') | k3_xboole_0('#skF_8', k1_tarski('#skF_9'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1212, c_2357])).
% 5.74/2.15  tff(c_2396, plain, (r2_hidden('#skF_3'('#skF_8'), '#skF_8') | k1_xboole_0='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_1212, c_2381])).
% 5.74/2.15  tff(c_2397, plain, (r2_hidden('#skF_3'('#skF_8'), '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_100, c_2396])).
% 5.74/2.15  tff(c_3086, plain, (r2_hidden('#skF_9', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_3082, c_2397])).
% 5.74/2.15  tff(c_3089, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1224, c_3086])).
% 5.74/2.15  tff(c_3090, plain, (![A_12455, C_12454]: (A_12455='#skF_3'('#skF_8') | C_12454='#skF_3'('#skF_8'))), inference(splitRight, [status(thm)], [c_2948])).
% 5.74/2.15  tff(c_3219, plain, ('#skF_3'('#skF_8')='#skF_9'), inference(splitLeft, [status(thm)], [c_3090])).
% 5.74/2.15  tff(c_3220, plain, (r2_hidden('#skF_9', '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_3219, c_2397])).
% 5.74/2.15  tff(c_3394, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1224, c_3220])).
% 5.74/2.15  tff(c_3519, plain, ('#skF_3'('#skF_8')='#skF_7'), inference(splitRight, [status(thm)], [c_3090])).
% 5.74/2.15  tff(c_3520, plain, (r2_hidden('#skF_7', '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_3519, c_2397])).
% 5.74/2.15  tff(c_3697, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2870, c_3520])).
% 5.74/2.15  tff(c_3699, plain, (r2_hidden('#skF_7', '#skF_8')), inference(splitRight, [status(thm)], [c_2863])).
% 5.74/2.15  tff(c_34, plain, (![E_20, A_14, B_15]: (r2_hidden(E_20, k1_enumset1(A_14, B_15, E_20)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.74/2.15  tff(c_2716, plain, (![D_12429, A_12430, B_12431]: (r2_hidden(D_12429, k1_enumset1(A_12430, B_12431, '#skF_9')) | ~r2_hidden(D_12429, '#skF_8'))), inference(resolution, [status(thm)], [c_34, c_2531])).
% 5.74/2.15  tff(c_3890, plain, (![D_20849, B_20850, A_20851]: (D_20849='#skF_9' | D_20849=B_20850 | D_20849=A_20851 | ~r2_hidden(D_20849, '#skF_8'))), inference(resolution, [status(thm)], [c_2716, c_32])).
% 5.74/2.15  tff(c_3921, plain, (![B_20850, A_20851]: ('#skF_7'='#skF_9' | B_20850='#skF_7' | A_20851='#skF_7')), inference(resolution, [status(thm)], [c_3699, c_3890])).
% 5.74/2.15  tff(c_4001, plain, ('#skF_7'='#skF_9'), inference(splitLeft, [status(thm)], [c_3921])).
% 5.74/2.15  tff(c_4003, plain, (r2_hidden('#skF_9', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_4001, c_3699])).
% 5.74/2.15  tff(c_4020, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1224, c_4003])).
% 5.74/2.15  tff(c_4021, plain, (![A_20851, B_20850]: (A_20851='#skF_7' | B_20850='#skF_7')), inference(splitRight, [status(thm)], [c_3921])).
% 5.74/2.15  tff(c_4070, plain, ('#skF_7'='#skF_9'), inference(splitLeft, [status(thm)], [c_4021])).
% 5.74/2.15  tff(c_4071, plain, (r2_hidden('#skF_9', '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_4070, c_3699])).
% 5.74/2.15  tff(c_4316, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1224, c_4071])).
% 5.74/2.15  tff(c_4354, plain, ('#skF_7'='#skF_9'), inference(splitRight, [status(thm)], [c_4021])).
% 5.74/2.15  tff(c_4355, plain, (r2_hidden('#skF_9', '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_4354, c_3699])).
% 5.74/2.15  tff(c_4600, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1224, c_4355])).
% 5.74/2.15  tff(c_4602, plain, (~r1_tarski('#skF_8', k1_tarski('#skF_9'))), inference(splitRight, [status(thm)], [c_84])).
% 5.74/2.15  tff(c_4613, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1201, c_4602])).
% 5.74/2.15  tff(c_4615, plain, (k1_tarski('#skF_9')='#skF_8'), inference(splitRight, [status(thm)], [c_74])).
% 5.74/2.15  tff(c_76, plain, (k1_tarski('#skF_7')='#skF_6' | k1_xboole_0='#skF_6' | k1_tarski('#skF_9')!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_94])).
% 5.74/2.15  tff(c_4621, plain, (k1_tarski('#skF_7')='#skF_6' | k1_xboole_0='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_4615, c_76])).
% 5.74/2.15  tff(c_4622, plain, (k1_xboole_0='#skF_6'), inference(splitLeft, [status(thm)], [c_4621])).
% 5.74/2.15  tff(c_4625, plain, (![A_13]: (r1_tarski('#skF_6', A_13))), inference(demodulation, [status(thm), theory('equality')], [c_4622, c_30])).
% 5.74/2.15  tff(c_4614, plain, (~r1_tarski('#skF_6', k1_tarski('#skF_7'))), inference(splitRight, [status(thm)], [c_74])).
% 5.74/2.15  tff(c_4632, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4625, c_4614])).
% 5.74/2.15  tff(c_4633, plain, (k1_tarski('#skF_7')='#skF_6'), inference(splitRight, [status(thm)], [c_4621])).
% 5.74/2.15  tff(c_4635, plain, (~r1_tarski('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_4633, c_4614])).
% 5.74/2.15  tff(c_4638, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_4635])).
% 5.74/2.15  tff(c_4640, plain, (k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_78])).
% 5.74/2.15  tff(c_4642, plain, (![A_13]: (r1_tarski('#skF_8', A_13))), inference(demodulation, [status(thm), theory('equality')], [c_4640, c_30])).
% 5.74/2.15  tff(c_80, plain, (k1_tarski('#skF_7')='#skF_6' | k1_xboole_0='#skF_6' | k1_xboole_0!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_94])).
% 5.74/2.15  tff(c_4650, plain, (k1_tarski('#skF_7')='#skF_6' | '#skF_6'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_4640, c_4640, c_80])).
% 5.74/2.15  tff(c_4651, plain, ('#skF_6'='#skF_8'), inference(splitLeft, [status(thm)], [c_4650])).
% 5.74/2.15  tff(c_4639, plain, (~r1_tarski('#skF_6', k1_tarski('#skF_7'))), inference(splitRight, [status(thm)], [c_78])).
% 5.74/2.15  tff(c_4652, plain, (~r1_tarski('#skF_8', k1_tarski('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_4651, c_4639])).
% 5.74/2.15  tff(c_4655, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4642, c_4652])).
% 5.74/2.15  tff(c_4656, plain, (k1_tarski('#skF_7')='#skF_6'), inference(splitRight, [status(thm)], [c_4650])).
% 5.74/2.15  tff(c_4658, plain, (~r1_tarski('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_4656, c_4639])).
% 5.74/2.15  tff(c_4661, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_4658])).
% 5.74/2.15  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.74/2.15  
% 5.74/2.15  Inference rules
% 5.74/2.15  ----------------------
% 5.74/2.15  #Ref     : 0
% 5.74/2.15  #Sup     : 1302
% 5.74/2.15  #Fact    : 0
% 5.74/2.15  #Define  : 0
% 5.74/2.15  #Split   : 27
% 5.74/2.15  #Chain   : 0
% 5.74/2.15  #Close   : 0
% 5.74/2.15  
% 5.74/2.15  Ordering : KBO
% 5.74/2.15  
% 5.74/2.15  Simplification rules
% 5.74/2.15  ----------------------
% 5.74/2.15  #Subsume      : 164
% 5.74/2.15  #Demod        : 146
% 5.74/2.15  #Tautology    : 139
% 5.74/2.15  #SimpNegUnit  : 37
% 5.74/2.15  #BackRed      : 58
% 5.74/2.15  
% 5.74/2.15  #Partial instantiations: 2826
% 5.74/2.15  #Strategies tried      : 1
% 5.74/2.15  
% 5.74/2.15  Timing (in seconds)
% 5.74/2.15  ----------------------
% 5.74/2.15  Preprocessing        : 0.37
% 5.74/2.15  Parsing              : 0.19
% 5.74/2.15  CNF conversion       : 0.03
% 5.74/2.15  Main loop            : 0.96
% 5.74/2.15  Inferencing          : 0.45
% 5.74/2.15  Reduction            : 0.26
% 5.74/2.15  Demodulation         : 0.19
% 5.74/2.15  BG Simplification    : 0.04
% 5.74/2.15  Subsumption          : 0.15
% 5.74/2.15  Abstraction          : 0.04
% 5.74/2.15  MUC search           : 0.00
% 5.74/2.15  Cooper               : 0.00
% 5.74/2.15  Total                : 1.40
% 5.74/2.15  Index Insertion      : 0.00
% 5.74/2.15  Index Deletion       : 0.00
% 5.74/2.15  Index Matching       : 0.00
% 5.74/2.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
