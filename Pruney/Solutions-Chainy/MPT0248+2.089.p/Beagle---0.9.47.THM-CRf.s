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
% DateTime   : Thu Dec  3 09:50:16 EST 2020

% Result     : Theorem 3.83s
% Output     : CNFRefutation 4.29s
% Verified   : 
% Statistics : Number of formulae       :  167 ( 546 expanded)
%              Number of leaves         :   33 ( 188 expanded)
%              Depth                    :   13
%              Number of atoms          :  233 (1307 expanded)
%              Number of equality atoms :  101 ( 792 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_6 > #skF_4 > #skF_7 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_1 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

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

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(f_55,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_109,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & ~ ( B = k1_tarski(A)
              & C = k1_tarski(A) )
          & ~ ( B = k1_xboole_0
              & C = k1_tarski(A) )
          & ~ ( B = k1_tarski(A)
              & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_61,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_49,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_68,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_59,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(c_32,plain,(
    ! [B_15] : r1_tarski(B_15,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_72,plain,
    ( k1_xboole_0 != '#skF_9'
    | k1_tarski('#skF_7') != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_86,plain,(
    k1_tarski('#skF_7') != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_72])).

tff(c_78,plain,(
    k2_xboole_0('#skF_8','#skF_9') = k1_tarski('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_87,plain,(
    ! [A_60,B_61] : r1_tarski(A_60,k2_xboole_0(A_60,B_61)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_90,plain,(
    r1_tarski('#skF_8',k1_tarski('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_87])).

tff(c_558,plain,(
    ! [B_118,A_119] :
      ( B_118 = A_119
      | ~ r1_tarski(B_118,A_119)
      | ~ r1_tarski(A_119,B_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_566,plain,
    ( k1_tarski('#skF_7') = '#skF_8'
    | ~ r1_tarski(k1_tarski('#skF_7'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_90,c_558])).

tff(c_576,plain,(
    ~ r1_tarski(k1_tarski('#skF_7'),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_566])).

tff(c_26,plain,(
    ! [A_12] :
      ( r2_hidden('#skF_4'(A_12),A_12)
      | k1_xboole_0 = A_12 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_213,plain,(
    ! [D_76,B_77,A_78] :
      ( ~ r2_hidden(D_76,B_77)
      | r2_hidden(D_76,k2_xboole_0(A_78,B_77)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_223,plain,(
    ! [D_79] :
      ( ~ r2_hidden(D_79,'#skF_9')
      | r2_hidden(D_79,k1_tarski('#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_213])).

tff(c_38,plain,(
    ! [C_24,A_20] :
      ( C_24 = A_20
      | ~ r2_hidden(C_24,k1_tarski(A_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_228,plain,(
    ! [D_80] :
      ( D_80 = '#skF_7'
      | ~ r2_hidden(D_80,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_223,c_38])).

tff(c_233,plain,
    ( '#skF_4'('#skF_9') = '#skF_7'
    | k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_26,c_228])).

tff(c_245,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_233])).

tff(c_74,plain,
    ( k1_tarski('#skF_7') != '#skF_9'
    | k1_xboole_0 != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_100,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_248,plain,(
    '#skF_9' != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_245,c_100])).

tff(c_247,plain,(
    ! [A_12] :
      ( r2_hidden('#skF_4'(A_12),A_12)
      | A_12 = '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_245,c_26])).

tff(c_280,plain,(
    ! [D_86,A_87,B_88] :
      ( ~ r2_hidden(D_86,A_87)
      | r2_hidden(D_86,k2_xboole_0(A_87,B_88)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_295,plain,(
    ! [D_89] :
      ( ~ r2_hidden(D_89,'#skF_8')
      | r2_hidden(D_89,k1_tarski('#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_280])).

tff(c_331,plain,(
    ! [D_92] :
      ( D_92 = '#skF_7'
      | ~ r2_hidden(D_92,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_295,c_38])).

tff(c_339,plain,
    ( '#skF_4'('#skF_8') = '#skF_7'
    | '#skF_9' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_247,c_331])).

tff(c_343,plain,(
    '#skF_4'('#skF_8') = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_248,c_339])).

tff(c_347,plain,
    ( r2_hidden('#skF_7','#skF_8')
    | '#skF_9' = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_343,c_247])).

tff(c_350,plain,(
    r2_hidden('#skF_7','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_248,c_347])).

tff(c_305,plain,(
    ! [A_90,B_91] :
      ( r2_hidden('#skF_1'(A_90,B_91),A_90)
      | r1_tarski(A_90,B_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_828,plain,(
    ! [A_135,B_136] :
      ( '#skF_1'(k1_tarski(A_135),B_136) = A_135
      | r1_tarski(k1_tarski(A_135),B_136) ) ),
    inference(resolution,[status(thm)],[c_305,c_38])).

tff(c_848,plain,(
    '#skF_1'(k1_tarski('#skF_7'),'#skF_8') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_828,c_576])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_858,plain,
    ( ~ r2_hidden('#skF_7','#skF_8')
    | r1_tarski(k1_tarski('#skF_7'),'#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_848,c_4])).

tff(c_864,plain,(
    r1_tarski(k1_tarski('#skF_7'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_350,c_858])).

tff(c_866,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_576,c_864])).

tff(c_868,plain,(
    k1_xboole_0 != '#skF_9' ),
    inference(splitRight,[status(thm)],[c_233])).

tff(c_867,plain,(
    '#skF_4'('#skF_9') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_233])).

tff(c_887,plain,
    ( r2_hidden('#skF_7','#skF_9')
    | k1_xboole_0 = '#skF_9' ),
    inference(superposition,[status(thm),theory(equality)],[c_867,c_26])).

tff(c_890,plain,(
    r2_hidden('#skF_7','#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_868,c_887])).

tff(c_1005,plain,(
    ! [A_163,B_164] :
      ( r2_hidden('#skF_1'(A_163,B_164),A_163)
      | r1_tarski(A_163,B_164) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_869,plain,(
    ! [D_137,A_138,B_139] :
      ( ~ r2_hidden(D_137,A_138)
      | r2_hidden(D_137,k2_xboole_0(A_138,B_139)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_897,plain,(
    ! [D_140] :
      ( ~ r2_hidden(D_140,'#skF_8')
      | r2_hidden(D_140,k1_tarski('#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_869])).

tff(c_906,plain,(
    ! [D_140] :
      ( D_140 = '#skF_7'
      | ~ r2_hidden(D_140,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_897,c_38])).

tff(c_1083,plain,(
    ! [B_169] :
      ( '#skF_1'('#skF_8',B_169) = '#skF_7'
      | r1_tarski('#skF_8',B_169) ) ),
    inference(resolution,[status(thm)],[c_1005,c_906])).

tff(c_34,plain,(
    ! [A_16,B_17] :
      ( k2_xboole_0(A_16,B_17) = B_17
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1331,plain,(
    ! [B_183] :
      ( k2_xboole_0('#skF_8',B_183) = B_183
      | '#skF_1'('#skF_8',B_183) = '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_1083,c_34])).

tff(c_1360,plain,
    ( k1_tarski('#skF_7') = '#skF_9'
    | '#skF_1'('#skF_8','#skF_9') = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_1331,c_78])).

tff(c_1387,plain,(
    '#skF_1'('#skF_8','#skF_9') = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_1360])).

tff(c_1403,plain,
    ( ~ r2_hidden('#skF_7','#skF_9')
    | r1_tarski('#skF_8','#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_1387,c_4])).

tff(c_1408,plain,(
    r1_tarski('#skF_8','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_890,c_1403])).

tff(c_1416,plain,(
    k2_xboole_0('#skF_8','#skF_9') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_1408,c_34])).

tff(c_1417,plain,(
    k1_tarski('#skF_7') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1416,c_78])).

tff(c_222,plain,(
    ! [D_76] :
      ( ~ r2_hidden(D_76,'#skF_9')
      | r2_hidden(D_76,k1_tarski('#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_213])).

tff(c_234,plain,(
    ! [A_81,B_82] :
      ( ~ r2_hidden('#skF_1'(A_81,B_82),B_82)
      | r1_tarski(A_81,B_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_243,plain,(
    ! [A_81] :
      ( r1_tarski(A_81,k1_tarski('#skF_7'))
      | ~ r2_hidden('#skF_1'(A_81,k1_tarski('#skF_7')),'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_222,c_234])).

tff(c_1026,plain,(
    r1_tarski('#skF_9',k1_tarski('#skF_7')) ),
    inference(resolution,[status(thm)],[c_1005,c_243])).

tff(c_28,plain,(
    ! [B_15,A_14] :
      ( B_15 = A_14
      | ~ r1_tarski(B_15,A_14)
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1052,plain,
    ( k1_tarski('#skF_7') = '#skF_9'
    | ~ r1_tarski(k1_tarski('#skF_7'),'#skF_9') ),
    inference(resolution,[status(thm)],[c_1026,c_28])).

tff(c_1091,plain,(
    ~ r1_tarski(k1_tarski('#skF_7'),'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_1052])).

tff(c_1447,plain,(
    ~ r1_tarski('#skF_9','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1417,c_1091])).

tff(c_1460,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1447])).

tff(c_1461,plain,(
    k1_tarski('#skF_7') = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_1360])).

tff(c_1464,plain,(
    ~ r1_tarski('#skF_9','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1461,c_1091])).

tff(c_1478,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1464])).

tff(c_1479,plain,(
    k1_tarski('#skF_7') = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_1052])).

tff(c_1032,plain,(
    ! [B_165,A_166] :
      ( B_165 = A_166
      | ~ r1_tarski(B_165,A_166)
      | ~ r1_tarski(A_166,B_165) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1034,plain,
    ( k1_tarski('#skF_7') = '#skF_8'
    | ~ r1_tarski(k1_tarski('#skF_7'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_90,c_1032])).

tff(c_1041,plain,(
    ~ r1_tarski(k1_tarski('#skF_7'),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_1034])).

tff(c_1484,plain,(
    ~ r1_tarski('#skF_9','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1479,c_1041])).

tff(c_907,plain,(
    ! [D_141] :
      ( D_141 = '#skF_7'
      | ~ r2_hidden(D_141,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_897,c_38])).

tff(c_911,plain,
    ( '#skF_4'('#skF_8') = '#skF_7'
    | k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_26,c_907])).

tff(c_914,plain,(
    '#skF_4'('#skF_8') = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_911])).

tff(c_918,plain,
    ( r2_hidden('#skF_7','#skF_8')
    | k1_xboole_0 = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_914,c_26])).

tff(c_921,plain,(
    r2_hidden('#skF_7','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_918])).

tff(c_227,plain,(
    ! [D_79] :
      ( D_79 = '#skF_7'
      | ~ r2_hidden(D_79,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_223,c_38])).

tff(c_1030,plain,(
    ! [B_164] :
      ( '#skF_1'('#skF_9',B_164) = '#skF_7'
      | r1_tarski('#skF_9',B_164) ) ),
    inference(resolution,[status(thm)],[c_1005,c_227])).

tff(c_1522,plain,(
    '#skF_1'('#skF_9','#skF_8') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_1030,c_1484])).

tff(c_1594,plain,
    ( ~ r2_hidden('#skF_7','#skF_8')
    | r1_tarski('#skF_9','#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_1522,c_4])).

tff(c_1600,plain,(
    r1_tarski('#skF_9','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_921,c_1594])).

tff(c_1602,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1484,c_1600])).

tff(c_1603,plain,(
    k1_tarski('#skF_7') != '#skF_9' ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_1663,plain,(
    ! [A_198,B_199] :
      ( k2_xboole_0(A_198,B_199) = B_199
      | ~ r1_tarski(A_198,B_199) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1675,plain,(
    ! [B_15] : k2_xboole_0(B_15,B_15) = B_15 ),
    inference(resolution,[status(thm)],[c_32,c_1663])).

tff(c_1604,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_1609,plain,(
    ! [A_12] :
      ( r2_hidden('#skF_4'(A_12),A_12)
      | A_12 = '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1604,c_26])).

tff(c_1744,plain,(
    ! [D_208,B_209,A_210] :
      ( ~ r2_hidden(D_208,B_209)
      | r2_hidden(D_208,k2_xboole_0(A_210,B_209)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1754,plain,(
    ! [D_211] :
      ( ~ r2_hidden(D_211,'#skF_9')
      | r2_hidden(D_211,k1_tarski('#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_1744])).

tff(c_1759,plain,(
    ! [D_212] :
      ( D_212 = '#skF_7'
      | ~ r2_hidden(D_212,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_1754,c_38])).

tff(c_1764,plain,
    ( '#skF_4'('#skF_9') = '#skF_7'
    | '#skF_9' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_1609,c_1759])).

tff(c_1765,plain,(
    '#skF_9' = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_1764])).

tff(c_1769,plain,(
    k2_xboole_0('#skF_8','#skF_8') = k1_tarski('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1765,c_78])).

tff(c_1770,plain,(
    k1_tarski('#skF_7') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1675,c_1769])).

tff(c_1772,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_1770])).

tff(c_1774,plain,(
    '#skF_9' != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_1764])).

tff(c_1773,plain,(
    '#skF_4'('#skF_9') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_1764])).

tff(c_1794,plain,
    ( r2_hidden('#skF_7','#skF_9')
    | '#skF_9' = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_1773,c_1609])).

tff(c_1797,plain,(
    r2_hidden('#skF_7','#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_1774,c_1794])).

tff(c_1775,plain,(
    ! [A_213,B_214] :
      ( r2_hidden('#skF_1'(A_213,B_214),A_213)
      | r1_tarski(A_213,B_214) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1722,plain,(
    ! [D_203,A_204,B_205] :
      ( ~ r2_hidden(D_203,A_204)
      | r2_hidden(D_203,k2_xboole_0(A_204,B_205)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1732,plain,(
    ! [D_206] :
      ( ~ r2_hidden(D_206,'#skF_8')
      | r2_hidden(D_206,k1_tarski('#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_1722])).

tff(c_1736,plain,(
    ! [D_206] :
      ( D_206 = '#skF_7'
      | ~ r2_hidden(D_206,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_1732,c_38])).

tff(c_1809,plain,(
    ! [B_216] :
      ( '#skF_1'('#skF_8',B_216) = '#skF_7'
      | r1_tarski('#skF_8',B_216) ) ),
    inference(resolution,[status(thm)],[c_1775,c_1736])).

tff(c_2000,plain,(
    ! [B_244] :
      ( k2_xboole_0('#skF_8',B_244) = B_244
      | '#skF_1'('#skF_8',B_244) = '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_1809,c_34])).

tff(c_2029,plain,
    ( k1_tarski('#skF_7') = '#skF_9'
    | '#skF_1'('#skF_8','#skF_9') = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_2000,c_78])).

tff(c_2052,plain,(
    '#skF_1'('#skF_8','#skF_9') = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_1603,c_2029])).

tff(c_2061,plain,
    ( ~ r2_hidden('#skF_7','#skF_9')
    | r1_tarski('#skF_8','#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_2052,c_4])).

tff(c_2068,plain,(
    r1_tarski('#skF_8','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1797,c_2061])).

tff(c_2118,plain,(
    k2_xboole_0('#skF_8','#skF_9') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_2068,c_34])).

tff(c_2133,plain,(
    k1_tarski('#skF_7') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2118,c_78])).

tff(c_2135,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1603,c_2133])).

tff(c_2137,plain,(
    k1_tarski('#skF_7') = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_76,plain,
    ( k1_tarski('#skF_7') != '#skF_9'
    | k1_tarski('#skF_7') != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_2167,plain,(
    '#skF_9' != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2137,c_2137,c_76])).

tff(c_2454,plain,(
    ! [A_297,B_298] :
      ( r2_hidden('#skF_1'(A_297,B_298),A_297)
      | r1_tarski(A_297,B_298) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2138,plain,(
    k2_xboole_0('#skF_8','#skF_9') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2137,c_78])).

tff(c_2284,plain,(
    ! [D_266,B_267,A_268] :
      ( ~ r2_hidden(D_266,B_267)
      | r2_hidden(D_266,k2_xboole_0(A_268,B_267)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2290,plain,(
    ! [D_266] :
      ( ~ r2_hidden(D_266,'#skF_9')
      | r2_hidden(D_266,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2138,c_2284])).

tff(c_2583,plain,(
    ! [B_309] :
      ( r2_hidden('#skF_1'('#skF_9',B_309),'#skF_8')
      | r1_tarski('#skF_9',B_309) ) ),
    inference(resolution,[status(thm)],[c_2454,c_2290])).

tff(c_2591,plain,(
    r1_tarski('#skF_9','#skF_8') ),
    inference(resolution,[status(thm)],[c_2583,c_4])).

tff(c_2594,plain,
    ( '#skF_9' = '#skF_8'
    | ~ r1_tarski('#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_2591,c_28])).

tff(c_2600,plain,(
    ~ r1_tarski('#skF_8','#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_2167,c_2594])).

tff(c_2136,plain,(
    k1_xboole_0 != '#skF_9' ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_2291,plain,(
    ! [D_269] :
      ( ~ r2_hidden(D_269,'#skF_9')
      | r2_hidden(D_269,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2138,c_2284])).

tff(c_2295,plain,
    ( r2_hidden('#skF_4'('#skF_9'),'#skF_8')
    | k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_26,c_2291])).

tff(c_2298,plain,(
    r2_hidden('#skF_4'('#skF_9'),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_2136,c_2295])).

tff(c_2169,plain,(
    ! [C_254,A_255] :
      ( C_254 = A_255
      | ~ r2_hidden(C_254,k1_tarski(A_255)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_2176,plain,(
    ! [C_254] :
      ( C_254 = '#skF_7'
      | ~ r2_hidden(C_254,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2137,c_2169])).

tff(c_2302,plain,(
    '#skF_4'('#skF_9') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_2298,c_2176])).

tff(c_2308,plain,
    ( r2_hidden('#skF_7','#skF_9')
    | k1_xboole_0 = '#skF_9' ),
    inference(superposition,[status(thm),theory(equality)],[c_2302,c_26])).

tff(c_2311,plain,(
    r2_hidden('#skF_7','#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_2136,c_2308])).

tff(c_2474,plain,(
    ! [B_298] :
      ( '#skF_1'('#skF_8',B_298) = '#skF_7'
      | r1_tarski('#skF_8',B_298) ) ),
    inference(resolution,[status(thm)],[c_2454,c_2176])).

tff(c_2605,plain,(
    '#skF_1'('#skF_8','#skF_9') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_2474,c_2600])).

tff(c_2612,plain,
    ( ~ r2_hidden('#skF_7','#skF_9')
    | r1_tarski('#skF_8','#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_2605,c_4])).

tff(c_2618,plain,(
    r1_tarski('#skF_8','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2311,c_2612])).

tff(c_2620,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2600,c_2618])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.36  % Computer   : n007.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % DateTime   : Tue Dec  1 16:45:21 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.37  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.83/1.75  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.20/1.77  
% 4.20/1.77  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.20/1.77  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_6 > #skF_4 > #skF_7 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_1 > #skF_5
% 4.20/1.77  
% 4.20/1.77  %Foreground sorts:
% 4.20/1.77  
% 4.20/1.77  
% 4.20/1.77  %Background operators:
% 4.20/1.77  
% 4.20/1.77  
% 4.20/1.77  %Foreground operators:
% 4.20/1.77  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 4.20/1.77  tff('#skF_4', type, '#skF_4': $i > $i).
% 4.20/1.77  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.20/1.77  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.20/1.77  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.20/1.77  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.20/1.77  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.20/1.77  tff('#skF_7', type, '#skF_7': $i).
% 4.20/1.77  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.20/1.77  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.20/1.77  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.20/1.77  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.20/1.77  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.20/1.77  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.20/1.77  tff('#skF_9', type, '#skF_9': $i).
% 4.20/1.77  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.20/1.77  tff('#skF_8', type, '#skF_8': $i).
% 4.20/1.77  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.20/1.77  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.20/1.77  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 4.20/1.77  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.20/1.77  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.20/1.77  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.20/1.77  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.20/1.77  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 4.20/1.77  
% 4.29/1.80  tff(f_55, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.29/1.80  tff(f_109, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 4.29/1.80  tff(f_61, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 4.29/1.80  tff(f_49, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 4.29/1.80  tff(f_41, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 4.29/1.80  tff(f_68, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 4.29/1.80  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 4.29/1.80  tff(f_59, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 4.29/1.80  tff(c_32, plain, (![B_15]: (r1_tarski(B_15, B_15))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.29/1.80  tff(c_72, plain, (k1_xboole_0!='#skF_9' | k1_tarski('#skF_7')!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.29/1.80  tff(c_86, plain, (k1_tarski('#skF_7')!='#skF_8'), inference(splitLeft, [status(thm)], [c_72])).
% 4.29/1.80  tff(c_78, plain, (k2_xboole_0('#skF_8', '#skF_9')=k1_tarski('#skF_7')), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.29/1.80  tff(c_87, plain, (![A_60, B_61]: (r1_tarski(A_60, k2_xboole_0(A_60, B_61)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.29/1.80  tff(c_90, plain, (r1_tarski('#skF_8', k1_tarski('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_78, c_87])).
% 4.29/1.80  tff(c_558, plain, (![B_118, A_119]: (B_118=A_119 | ~r1_tarski(B_118, A_119) | ~r1_tarski(A_119, B_118))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.29/1.80  tff(c_566, plain, (k1_tarski('#skF_7')='#skF_8' | ~r1_tarski(k1_tarski('#skF_7'), '#skF_8')), inference(resolution, [status(thm)], [c_90, c_558])).
% 4.29/1.80  tff(c_576, plain, (~r1_tarski(k1_tarski('#skF_7'), '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_86, c_566])).
% 4.29/1.80  tff(c_26, plain, (![A_12]: (r2_hidden('#skF_4'(A_12), A_12) | k1_xboole_0=A_12)), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.29/1.80  tff(c_213, plain, (![D_76, B_77, A_78]: (~r2_hidden(D_76, B_77) | r2_hidden(D_76, k2_xboole_0(A_78, B_77)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.29/1.80  tff(c_223, plain, (![D_79]: (~r2_hidden(D_79, '#skF_9') | r2_hidden(D_79, k1_tarski('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_78, c_213])).
% 4.29/1.80  tff(c_38, plain, (![C_24, A_20]: (C_24=A_20 | ~r2_hidden(C_24, k1_tarski(A_20)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.29/1.80  tff(c_228, plain, (![D_80]: (D_80='#skF_7' | ~r2_hidden(D_80, '#skF_9'))), inference(resolution, [status(thm)], [c_223, c_38])).
% 4.29/1.80  tff(c_233, plain, ('#skF_4'('#skF_9')='#skF_7' | k1_xboole_0='#skF_9'), inference(resolution, [status(thm)], [c_26, c_228])).
% 4.29/1.80  tff(c_245, plain, (k1_xboole_0='#skF_9'), inference(splitLeft, [status(thm)], [c_233])).
% 4.29/1.80  tff(c_74, plain, (k1_tarski('#skF_7')!='#skF_9' | k1_xboole_0!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.29/1.80  tff(c_100, plain, (k1_xboole_0!='#skF_8'), inference(splitLeft, [status(thm)], [c_74])).
% 4.29/1.80  tff(c_248, plain, ('#skF_9'!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_245, c_100])).
% 4.29/1.80  tff(c_247, plain, (![A_12]: (r2_hidden('#skF_4'(A_12), A_12) | A_12='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_245, c_26])).
% 4.29/1.80  tff(c_280, plain, (![D_86, A_87, B_88]: (~r2_hidden(D_86, A_87) | r2_hidden(D_86, k2_xboole_0(A_87, B_88)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.29/1.80  tff(c_295, plain, (![D_89]: (~r2_hidden(D_89, '#skF_8') | r2_hidden(D_89, k1_tarski('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_78, c_280])).
% 4.29/1.80  tff(c_331, plain, (![D_92]: (D_92='#skF_7' | ~r2_hidden(D_92, '#skF_8'))), inference(resolution, [status(thm)], [c_295, c_38])).
% 4.29/1.80  tff(c_339, plain, ('#skF_4'('#skF_8')='#skF_7' | '#skF_9'='#skF_8'), inference(resolution, [status(thm)], [c_247, c_331])).
% 4.29/1.80  tff(c_343, plain, ('#skF_4'('#skF_8')='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_248, c_339])).
% 4.29/1.80  tff(c_347, plain, (r2_hidden('#skF_7', '#skF_8') | '#skF_9'='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_343, c_247])).
% 4.29/1.80  tff(c_350, plain, (r2_hidden('#skF_7', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_248, c_347])).
% 4.29/1.80  tff(c_305, plain, (![A_90, B_91]: (r2_hidden('#skF_1'(A_90, B_91), A_90) | r1_tarski(A_90, B_91))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.29/1.80  tff(c_828, plain, (![A_135, B_136]: ('#skF_1'(k1_tarski(A_135), B_136)=A_135 | r1_tarski(k1_tarski(A_135), B_136))), inference(resolution, [status(thm)], [c_305, c_38])).
% 4.29/1.80  tff(c_848, plain, ('#skF_1'(k1_tarski('#skF_7'), '#skF_8')='#skF_7'), inference(resolution, [status(thm)], [c_828, c_576])).
% 4.29/1.80  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.29/1.80  tff(c_858, plain, (~r2_hidden('#skF_7', '#skF_8') | r1_tarski(k1_tarski('#skF_7'), '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_848, c_4])).
% 4.29/1.80  tff(c_864, plain, (r1_tarski(k1_tarski('#skF_7'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_350, c_858])).
% 4.29/1.80  tff(c_866, plain, $false, inference(negUnitSimplification, [status(thm)], [c_576, c_864])).
% 4.29/1.80  tff(c_868, plain, (k1_xboole_0!='#skF_9'), inference(splitRight, [status(thm)], [c_233])).
% 4.29/1.80  tff(c_867, plain, ('#skF_4'('#skF_9')='#skF_7'), inference(splitRight, [status(thm)], [c_233])).
% 4.29/1.80  tff(c_887, plain, (r2_hidden('#skF_7', '#skF_9') | k1_xboole_0='#skF_9'), inference(superposition, [status(thm), theory('equality')], [c_867, c_26])).
% 4.29/1.80  tff(c_890, plain, (r2_hidden('#skF_7', '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_868, c_887])).
% 4.29/1.80  tff(c_1005, plain, (![A_163, B_164]: (r2_hidden('#skF_1'(A_163, B_164), A_163) | r1_tarski(A_163, B_164))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.29/1.80  tff(c_869, plain, (![D_137, A_138, B_139]: (~r2_hidden(D_137, A_138) | r2_hidden(D_137, k2_xboole_0(A_138, B_139)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.29/1.80  tff(c_897, plain, (![D_140]: (~r2_hidden(D_140, '#skF_8') | r2_hidden(D_140, k1_tarski('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_78, c_869])).
% 4.29/1.80  tff(c_906, plain, (![D_140]: (D_140='#skF_7' | ~r2_hidden(D_140, '#skF_8'))), inference(resolution, [status(thm)], [c_897, c_38])).
% 4.29/1.80  tff(c_1083, plain, (![B_169]: ('#skF_1'('#skF_8', B_169)='#skF_7' | r1_tarski('#skF_8', B_169))), inference(resolution, [status(thm)], [c_1005, c_906])).
% 4.29/1.80  tff(c_34, plain, (![A_16, B_17]: (k2_xboole_0(A_16, B_17)=B_17 | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.29/1.80  tff(c_1331, plain, (![B_183]: (k2_xboole_0('#skF_8', B_183)=B_183 | '#skF_1'('#skF_8', B_183)='#skF_7')), inference(resolution, [status(thm)], [c_1083, c_34])).
% 4.29/1.80  tff(c_1360, plain, (k1_tarski('#skF_7')='#skF_9' | '#skF_1'('#skF_8', '#skF_9')='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_1331, c_78])).
% 4.29/1.80  tff(c_1387, plain, ('#skF_1'('#skF_8', '#skF_9')='#skF_7'), inference(splitLeft, [status(thm)], [c_1360])).
% 4.29/1.80  tff(c_1403, plain, (~r2_hidden('#skF_7', '#skF_9') | r1_tarski('#skF_8', '#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_1387, c_4])).
% 4.29/1.80  tff(c_1408, plain, (r1_tarski('#skF_8', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_890, c_1403])).
% 4.29/1.80  tff(c_1416, plain, (k2_xboole_0('#skF_8', '#skF_9')='#skF_9'), inference(resolution, [status(thm)], [c_1408, c_34])).
% 4.29/1.80  tff(c_1417, plain, (k1_tarski('#skF_7')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_1416, c_78])).
% 4.29/1.80  tff(c_222, plain, (![D_76]: (~r2_hidden(D_76, '#skF_9') | r2_hidden(D_76, k1_tarski('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_78, c_213])).
% 4.29/1.80  tff(c_234, plain, (![A_81, B_82]: (~r2_hidden('#skF_1'(A_81, B_82), B_82) | r1_tarski(A_81, B_82))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.29/1.80  tff(c_243, plain, (![A_81]: (r1_tarski(A_81, k1_tarski('#skF_7')) | ~r2_hidden('#skF_1'(A_81, k1_tarski('#skF_7')), '#skF_9'))), inference(resolution, [status(thm)], [c_222, c_234])).
% 4.29/1.80  tff(c_1026, plain, (r1_tarski('#skF_9', k1_tarski('#skF_7'))), inference(resolution, [status(thm)], [c_1005, c_243])).
% 4.29/1.80  tff(c_28, plain, (![B_15, A_14]: (B_15=A_14 | ~r1_tarski(B_15, A_14) | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.29/1.80  tff(c_1052, plain, (k1_tarski('#skF_7')='#skF_9' | ~r1_tarski(k1_tarski('#skF_7'), '#skF_9')), inference(resolution, [status(thm)], [c_1026, c_28])).
% 4.29/1.80  tff(c_1091, plain, (~r1_tarski(k1_tarski('#skF_7'), '#skF_9')), inference(splitLeft, [status(thm)], [c_1052])).
% 4.29/1.80  tff(c_1447, plain, (~r1_tarski('#skF_9', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_1417, c_1091])).
% 4.29/1.80  tff(c_1460, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_1447])).
% 4.29/1.80  tff(c_1461, plain, (k1_tarski('#skF_7')='#skF_9'), inference(splitRight, [status(thm)], [c_1360])).
% 4.29/1.80  tff(c_1464, plain, (~r1_tarski('#skF_9', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_1461, c_1091])).
% 4.29/1.80  tff(c_1478, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_1464])).
% 4.29/1.80  tff(c_1479, plain, (k1_tarski('#skF_7')='#skF_9'), inference(splitRight, [status(thm)], [c_1052])).
% 4.29/1.80  tff(c_1032, plain, (![B_165, A_166]: (B_165=A_166 | ~r1_tarski(B_165, A_166) | ~r1_tarski(A_166, B_165))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.29/1.80  tff(c_1034, plain, (k1_tarski('#skF_7')='#skF_8' | ~r1_tarski(k1_tarski('#skF_7'), '#skF_8')), inference(resolution, [status(thm)], [c_90, c_1032])).
% 4.29/1.80  tff(c_1041, plain, (~r1_tarski(k1_tarski('#skF_7'), '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_86, c_1034])).
% 4.29/1.80  tff(c_1484, plain, (~r1_tarski('#skF_9', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1479, c_1041])).
% 4.29/1.80  tff(c_907, plain, (![D_141]: (D_141='#skF_7' | ~r2_hidden(D_141, '#skF_8'))), inference(resolution, [status(thm)], [c_897, c_38])).
% 4.29/1.80  tff(c_911, plain, ('#skF_4'('#skF_8')='#skF_7' | k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_26, c_907])).
% 4.29/1.80  tff(c_914, plain, ('#skF_4'('#skF_8')='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_100, c_911])).
% 4.29/1.80  tff(c_918, plain, (r2_hidden('#skF_7', '#skF_8') | k1_xboole_0='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_914, c_26])).
% 4.29/1.80  tff(c_921, plain, (r2_hidden('#skF_7', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_100, c_918])).
% 4.29/1.80  tff(c_227, plain, (![D_79]: (D_79='#skF_7' | ~r2_hidden(D_79, '#skF_9'))), inference(resolution, [status(thm)], [c_223, c_38])).
% 4.29/1.80  tff(c_1030, plain, (![B_164]: ('#skF_1'('#skF_9', B_164)='#skF_7' | r1_tarski('#skF_9', B_164))), inference(resolution, [status(thm)], [c_1005, c_227])).
% 4.29/1.80  tff(c_1522, plain, ('#skF_1'('#skF_9', '#skF_8')='#skF_7'), inference(resolution, [status(thm)], [c_1030, c_1484])).
% 4.29/1.80  tff(c_1594, plain, (~r2_hidden('#skF_7', '#skF_8') | r1_tarski('#skF_9', '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_1522, c_4])).
% 4.29/1.80  tff(c_1600, plain, (r1_tarski('#skF_9', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_921, c_1594])).
% 4.29/1.80  tff(c_1602, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1484, c_1600])).
% 4.29/1.80  tff(c_1603, plain, (k1_tarski('#skF_7')!='#skF_9'), inference(splitRight, [status(thm)], [c_74])).
% 4.29/1.80  tff(c_1663, plain, (![A_198, B_199]: (k2_xboole_0(A_198, B_199)=B_199 | ~r1_tarski(A_198, B_199))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.29/1.80  tff(c_1675, plain, (![B_15]: (k2_xboole_0(B_15, B_15)=B_15)), inference(resolution, [status(thm)], [c_32, c_1663])).
% 4.29/1.80  tff(c_1604, plain, (k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_74])).
% 4.29/1.80  tff(c_1609, plain, (![A_12]: (r2_hidden('#skF_4'(A_12), A_12) | A_12='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1604, c_26])).
% 4.29/1.80  tff(c_1744, plain, (![D_208, B_209, A_210]: (~r2_hidden(D_208, B_209) | r2_hidden(D_208, k2_xboole_0(A_210, B_209)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.29/1.80  tff(c_1754, plain, (![D_211]: (~r2_hidden(D_211, '#skF_9') | r2_hidden(D_211, k1_tarski('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_78, c_1744])).
% 4.29/1.80  tff(c_1759, plain, (![D_212]: (D_212='#skF_7' | ~r2_hidden(D_212, '#skF_9'))), inference(resolution, [status(thm)], [c_1754, c_38])).
% 4.29/1.80  tff(c_1764, plain, ('#skF_4'('#skF_9')='#skF_7' | '#skF_9'='#skF_8'), inference(resolution, [status(thm)], [c_1609, c_1759])).
% 4.29/1.80  tff(c_1765, plain, ('#skF_9'='#skF_8'), inference(splitLeft, [status(thm)], [c_1764])).
% 4.29/1.80  tff(c_1769, plain, (k2_xboole_0('#skF_8', '#skF_8')=k1_tarski('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_1765, c_78])).
% 4.29/1.80  tff(c_1770, plain, (k1_tarski('#skF_7')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_1675, c_1769])).
% 4.29/1.80  tff(c_1772, plain, $false, inference(negUnitSimplification, [status(thm)], [c_86, c_1770])).
% 4.29/1.80  tff(c_1774, plain, ('#skF_9'!='#skF_8'), inference(splitRight, [status(thm)], [c_1764])).
% 4.29/1.80  tff(c_1773, plain, ('#skF_4'('#skF_9')='#skF_7'), inference(splitRight, [status(thm)], [c_1764])).
% 4.29/1.80  tff(c_1794, plain, (r2_hidden('#skF_7', '#skF_9') | '#skF_9'='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_1773, c_1609])).
% 4.29/1.80  tff(c_1797, plain, (r2_hidden('#skF_7', '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_1774, c_1794])).
% 4.29/1.80  tff(c_1775, plain, (![A_213, B_214]: (r2_hidden('#skF_1'(A_213, B_214), A_213) | r1_tarski(A_213, B_214))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.29/1.80  tff(c_1722, plain, (![D_203, A_204, B_205]: (~r2_hidden(D_203, A_204) | r2_hidden(D_203, k2_xboole_0(A_204, B_205)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.29/1.80  tff(c_1732, plain, (![D_206]: (~r2_hidden(D_206, '#skF_8') | r2_hidden(D_206, k1_tarski('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_78, c_1722])).
% 4.29/1.80  tff(c_1736, plain, (![D_206]: (D_206='#skF_7' | ~r2_hidden(D_206, '#skF_8'))), inference(resolution, [status(thm)], [c_1732, c_38])).
% 4.29/1.80  tff(c_1809, plain, (![B_216]: ('#skF_1'('#skF_8', B_216)='#skF_7' | r1_tarski('#skF_8', B_216))), inference(resolution, [status(thm)], [c_1775, c_1736])).
% 4.29/1.80  tff(c_2000, plain, (![B_244]: (k2_xboole_0('#skF_8', B_244)=B_244 | '#skF_1'('#skF_8', B_244)='#skF_7')), inference(resolution, [status(thm)], [c_1809, c_34])).
% 4.29/1.80  tff(c_2029, plain, (k1_tarski('#skF_7')='#skF_9' | '#skF_1'('#skF_8', '#skF_9')='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_2000, c_78])).
% 4.29/1.80  tff(c_2052, plain, ('#skF_1'('#skF_8', '#skF_9')='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_1603, c_2029])).
% 4.29/1.80  tff(c_2061, plain, (~r2_hidden('#skF_7', '#skF_9') | r1_tarski('#skF_8', '#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_2052, c_4])).
% 4.29/1.80  tff(c_2068, plain, (r1_tarski('#skF_8', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_1797, c_2061])).
% 4.29/1.80  tff(c_2118, plain, (k2_xboole_0('#skF_8', '#skF_9')='#skF_9'), inference(resolution, [status(thm)], [c_2068, c_34])).
% 4.29/1.80  tff(c_2133, plain, (k1_tarski('#skF_7')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_2118, c_78])).
% 4.29/1.80  tff(c_2135, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1603, c_2133])).
% 4.29/1.80  tff(c_2137, plain, (k1_tarski('#skF_7')='#skF_8'), inference(splitRight, [status(thm)], [c_72])).
% 4.29/1.80  tff(c_76, plain, (k1_tarski('#skF_7')!='#skF_9' | k1_tarski('#skF_7')!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.29/1.80  tff(c_2167, plain, ('#skF_9'!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_2137, c_2137, c_76])).
% 4.29/1.80  tff(c_2454, plain, (![A_297, B_298]: (r2_hidden('#skF_1'(A_297, B_298), A_297) | r1_tarski(A_297, B_298))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.29/1.80  tff(c_2138, plain, (k2_xboole_0('#skF_8', '#skF_9')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_2137, c_78])).
% 4.29/1.80  tff(c_2284, plain, (![D_266, B_267, A_268]: (~r2_hidden(D_266, B_267) | r2_hidden(D_266, k2_xboole_0(A_268, B_267)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.29/1.80  tff(c_2290, plain, (![D_266]: (~r2_hidden(D_266, '#skF_9') | r2_hidden(D_266, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_2138, c_2284])).
% 4.29/1.80  tff(c_2583, plain, (![B_309]: (r2_hidden('#skF_1'('#skF_9', B_309), '#skF_8') | r1_tarski('#skF_9', B_309))), inference(resolution, [status(thm)], [c_2454, c_2290])).
% 4.29/1.80  tff(c_2591, plain, (r1_tarski('#skF_9', '#skF_8')), inference(resolution, [status(thm)], [c_2583, c_4])).
% 4.29/1.80  tff(c_2594, plain, ('#skF_9'='#skF_8' | ~r1_tarski('#skF_8', '#skF_9')), inference(resolution, [status(thm)], [c_2591, c_28])).
% 4.29/1.80  tff(c_2600, plain, (~r1_tarski('#skF_8', '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_2167, c_2594])).
% 4.29/1.80  tff(c_2136, plain, (k1_xboole_0!='#skF_9'), inference(splitRight, [status(thm)], [c_72])).
% 4.29/1.80  tff(c_2291, plain, (![D_269]: (~r2_hidden(D_269, '#skF_9') | r2_hidden(D_269, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_2138, c_2284])).
% 4.29/1.80  tff(c_2295, plain, (r2_hidden('#skF_4'('#skF_9'), '#skF_8') | k1_xboole_0='#skF_9'), inference(resolution, [status(thm)], [c_26, c_2291])).
% 4.29/1.80  tff(c_2298, plain, (r2_hidden('#skF_4'('#skF_9'), '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_2136, c_2295])).
% 4.29/1.80  tff(c_2169, plain, (![C_254, A_255]: (C_254=A_255 | ~r2_hidden(C_254, k1_tarski(A_255)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.29/1.80  tff(c_2176, plain, (![C_254]: (C_254='#skF_7' | ~r2_hidden(C_254, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_2137, c_2169])).
% 4.29/1.80  tff(c_2302, plain, ('#skF_4'('#skF_9')='#skF_7'), inference(resolution, [status(thm)], [c_2298, c_2176])).
% 4.29/1.80  tff(c_2308, plain, (r2_hidden('#skF_7', '#skF_9') | k1_xboole_0='#skF_9'), inference(superposition, [status(thm), theory('equality')], [c_2302, c_26])).
% 4.29/1.80  tff(c_2311, plain, (r2_hidden('#skF_7', '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_2136, c_2308])).
% 4.29/1.80  tff(c_2474, plain, (![B_298]: ('#skF_1'('#skF_8', B_298)='#skF_7' | r1_tarski('#skF_8', B_298))), inference(resolution, [status(thm)], [c_2454, c_2176])).
% 4.29/1.80  tff(c_2605, plain, ('#skF_1'('#skF_8', '#skF_9')='#skF_7'), inference(resolution, [status(thm)], [c_2474, c_2600])).
% 4.29/1.80  tff(c_2612, plain, (~r2_hidden('#skF_7', '#skF_9') | r1_tarski('#skF_8', '#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_2605, c_4])).
% 4.29/1.80  tff(c_2618, plain, (r1_tarski('#skF_8', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_2311, c_2612])).
% 4.29/1.80  tff(c_2620, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2600, c_2618])).
% 4.29/1.80  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.29/1.80  
% 4.29/1.80  Inference rules
% 4.29/1.80  ----------------------
% 4.29/1.80  #Ref     : 0
% 4.29/1.80  #Sup     : 581
% 4.29/1.80  #Fact    : 0
% 4.29/1.80  #Define  : 0
% 4.29/1.80  #Split   : 10
% 4.29/1.80  #Chain   : 0
% 4.29/1.80  #Close   : 0
% 4.29/1.80  
% 4.29/1.80  Ordering : KBO
% 4.29/1.80  
% 4.29/1.80  Simplification rules
% 4.29/1.80  ----------------------
% 4.29/1.80  #Subsume      : 52
% 4.29/1.80  #Demod        : 249
% 4.29/1.80  #Tautology    : 330
% 4.29/1.80  #SimpNegUnit  : 30
% 4.29/1.80  #BackRed      : 46
% 4.29/1.80  
% 4.29/1.80  #Partial instantiations: 0
% 4.29/1.80  #Strategies tried      : 1
% 4.29/1.80  
% 4.29/1.80  Timing (in seconds)
% 4.29/1.80  ----------------------
% 4.29/1.80  Preprocessing        : 0.35
% 4.29/1.80  Parsing              : 0.18
% 4.29/1.80  CNF conversion       : 0.03
% 4.29/1.80  Main loop            : 0.61
% 4.29/1.80  Inferencing          : 0.22
% 4.29/1.80  Reduction            : 0.19
% 4.29/1.80  Demodulation         : 0.14
% 4.29/1.80  BG Simplification    : 0.03
% 4.29/1.80  Subsumption          : 0.11
% 4.29/1.80  Abstraction          : 0.03
% 4.29/1.80  MUC search           : 0.00
% 4.29/1.80  Cooper               : 0.00
% 4.29/1.80  Total                : 1.01
% 4.29/1.80  Index Insertion      : 0.00
% 4.29/1.80  Index Deletion       : 0.00
% 4.29/1.80  Index Matching       : 0.00
% 4.29/1.80  BG Taut test         : 0.00
%------------------------------------------------------------------------------
