%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:20 EST 2020

% Result     : Theorem 10.76s
% Output     : CNFRefutation 11.02s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 446 expanded)
%              Number of leaves         :   32 ( 152 expanded)
%              Depth                    :   13
%              Number of atoms          :  183 (1119 expanded)
%              Number of equality atoms :   85 ( 753 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_6 > #skF_2 > #skF_8 > #skF_3 > #skF_5 > #skF_4

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

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_100,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & ~ ( B = k1_tarski(A)
              & C = k1_tarski(A) )
          & ~ ( B = k1_xboole_0
              & C = k1_tarski(A) )
          & ~ ( B = k1_tarski(A)
              & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_48,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_42,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_46,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(c_66,plain,
    ( k1_tarski('#skF_6') != '#skF_8'
    | k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_92,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_64,plain,
    ( k1_xboole_0 != '#skF_8'
    | k1_tarski('#skF_6') != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_82,plain,(
    k1_tarski('#skF_6') != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_70,plain,(
    k2_xboole_0('#skF_7','#skF_8') = k1_tarski('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_88,plain,(
    ! [A_56,B_57] : r1_tarski(A_56,k2_xboole_0(A_56,B_57)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_91,plain,(
    r1_tarski('#skF_7',k1_tarski('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_88])).

tff(c_575,plain,(
    ! [B_105,A_106] :
      ( k1_tarski(B_105) = A_106
      | k1_xboole_0 = A_106
      | ~ r1_tarski(A_106,k1_tarski(B_105)) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_582,plain,
    ( k1_tarski('#skF_6') = '#skF_7'
    | k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_91,c_575])).

tff(c_593,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_82,c_582])).

tff(c_594,plain,(
    k1_tarski('#skF_6') != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_595,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_20,plain,(
    ! [A_7] :
      ( r2_hidden('#skF_3'(A_7),A_7)
      | k1_xboole_0 = A_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_603,plain,(
    ! [A_7] :
      ( r2_hidden('#skF_3'(A_7),A_7)
      | A_7 = '#skF_7' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_595,c_20])).

tff(c_605,plain,(
    ! [C_109,A_110] :
      ( C_109 = A_110
      | ~ r2_hidden(C_109,k1_tarski(A_110)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_613,plain,(
    ! [A_110] :
      ( '#skF_3'(k1_tarski(A_110)) = A_110
      | k1_tarski(A_110) = '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_603,c_605])).

tff(c_2015,plain,(
    ! [D_4526,B_4527,A_4528] :
      ( r2_hidden(D_4526,B_4527)
      | r2_hidden(D_4526,A_4528)
      | ~ r2_hidden(D_4526,k2_xboole_0(A_4528,B_4527)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_2153,plain,(
    ! [D_4536] :
      ( r2_hidden(D_4536,'#skF_8')
      | r2_hidden(D_4536,'#skF_7')
      | ~ r2_hidden(D_4536,k1_tarski('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_2015])).

tff(c_2164,plain,
    ( r2_hidden('#skF_3'(k1_tarski('#skF_6')),'#skF_8')
    | r2_hidden('#skF_3'(k1_tarski('#skF_6')),'#skF_7')
    | k1_tarski('#skF_6') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_603,c_2153])).

tff(c_2173,plain,
    ( r2_hidden('#skF_3'(k1_tarski('#skF_6')),'#skF_8')
    | r2_hidden('#skF_3'(k1_tarski('#skF_6')),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_2164])).

tff(c_2176,plain,(
    r2_hidden('#skF_3'(k1_tarski('#skF_6')),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_2173])).

tff(c_2188,plain,
    ( r2_hidden('#skF_6','#skF_7')
    | k1_tarski('#skF_6') = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_613,c_2176])).

tff(c_2193,plain,(
    r2_hidden('#skF_6','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_2188])).

tff(c_60,plain,(
    ! [B_49] : r1_tarski(k1_xboole_0,k1_tarski(B_49)) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_596,plain,(
    ! [B_49] : r1_tarski('#skF_7',k1_tarski(B_49)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_595,c_60])).

tff(c_642,plain,(
    ! [A_119,B_120] :
      ( k2_xboole_0(A_119,B_120) = B_120
      | ~ r1_tarski(A_119,B_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_656,plain,(
    ! [B_49] : k2_xboole_0('#skF_7',k1_tarski(B_49)) = k1_tarski(B_49) ),
    inference(resolution,[status(thm)],[c_596,c_642])).

tff(c_684,plain,(
    ! [D_124,A_125,B_126] :
      ( ~ r2_hidden(D_124,A_125)
      | r2_hidden(D_124,k2_xboole_0(A_125,B_126)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1631,plain,(
    ! [D_4498,B_4499] :
      ( ~ r2_hidden(D_4498,'#skF_7')
      | r2_hidden(D_4498,k1_tarski(B_4499)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_656,c_684])).

tff(c_26,plain,(
    ! [C_17,A_13] :
      ( C_17 = A_13
      | ~ r2_hidden(C_17,k1_tarski(A_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1635,plain,(
    ! [D_4498,B_4499] :
      ( D_4498 = B_4499
      | ~ r2_hidden(D_4498,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_1631,c_26])).

tff(c_2212,plain,(
    '#skF_6' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_2193,c_1635])).

tff(c_2210,plain,(
    ! [B_4499] : B_4499 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_2193,c_1635])).

tff(c_2387,plain,(
    ! [B_7188] : B_7188 = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_2212,c_2210])).

tff(c_28,plain,(
    ! [C_17] : r2_hidden(C_17,k1_tarski(C_17)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_739,plain,(
    ! [D_131,B_132,A_133] :
      ( ~ r2_hidden(D_131,B_132)
      | r2_hidden(D_131,k2_xboole_0(A_133,B_132)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_800,plain,(
    ! [D_137] :
      ( ~ r2_hidden(D_137,'#skF_8')
      | r2_hidden(D_137,k1_tarski('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_739])).

tff(c_805,plain,(
    ! [D_138] :
      ( D_138 = '#skF_6'
      | ~ r2_hidden(D_138,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_800,c_26])).

tff(c_810,plain,
    ( '#skF_3'('#skF_8') = '#skF_6'
    | '#skF_7' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_603,c_805])).

tff(c_811,plain,(
    '#skF_7' = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_810])).

tff(c_818,plain,(
    k2_xboole_0('#skF_8','#skF_8') = k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_811,c_70])).

tff(c_1162,plain,(
    ! [D_166,B_167,A_168] :
      ( r2_hidden(D_166,B_167)
      | r2_hidden(D_166,A_168)
      | ~ r2_hidden(D_166,k2_xboole_0(A_168,B_167)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1306,plain,(
    ! [D_176] :
      ( r2_hidden(D_176,'#skF_8')
      | r2_hidden(D_176,'#skF_8')
      | ~ r2_hidden(D_176,k1_tarski('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_818,c_1162])).

tff(c_1323,plain,(
    r2_hidden('#skF_6','#skF_8') ),
    inference(resolution,[status(thm)],[c_28,c_1306])).

tff(c_687,plain,(
    ! [D_124,B_49] :
      ( ~ r2_hidden(D_124,'#skF_7')
      | r2_hidden(D_124,k1_tarski(B_49)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_656,c_684])).

tff(c_922,plain,(
    ! [D_148,B_149] :
      ( ~ r2_hidden(D_148,'#skF_8')
      | r2_hidden(D_148,k1_tarski(B_149)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_811,c_687])).

tff(c_926,plain,(
    ! [D_148,B_149] :
      ( D_148 = B_149
      | ~ r2_hidden(D_148,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_922,c_26])).

tff(c_1331,plain,(
    '#skF_6' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_1323,c_926])).

tff(c_1329,plain,(
    ! [B_149] : B_149 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_1323,c_926])).

tff(c_1459,plain,(
    ! [B_2441] : B_2441 = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_1331,c_1329])).

tff(c_1512,plain,(
    k1_tarski('#skF_6') = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_1459,c_818])).

tff(c_1574,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_594,c_1512])).

tff(c_1576,plain,(
    '#skF_7' != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_810])).

tff(c_2558,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_2387,c_1576])).

tff(c_2559,plain,(
    r2_hidden('#skF_3'(k1_tarski('#skF_6')),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_2173])).

tff(c_804,plain,(
    ! [D_137] :
      ( D_137 = '#skF_6'
      | ~ r2_hidden(D_137,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_800,c_26])).

tff(c_2606,plain,(
    '#skF_3'(k1_tarski('#skF_6')) = '#skF_6' ),
    inference(resolution,[status(thm)],[c_2559,c_804])).

tff(c_2560,plain,(
    ~ r2_hidden('#skF_3'(k1_tarski('#skF_6')),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_2173])).

tff(c_2630,plain,(
    ~ r2_hidden('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2606,c_2560])).

tff(c_28650,plain,(
    ! [A_30694,B_30695,C_30696] :
      ( r2_hidden('#skF_1'(A_30694,B_30695,C_30696),B_30695)
      | r2_hidden('#skF_1'(A_30694,B_30695,C_30696),A_30694)
      | r2_hidden('#skF_2'(A_30694,B_30695,C_30696),C_30696)
      | k2_xboole_0(A_30694,B_30695) = C_30696 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_16,plain,(
    ! [A_1,B_2,C_3] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2,C_3),C_3)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k2_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_29635,plain,(
    ! [A_31210,B_31211] :
      ( r2_hidden('#skF_1'(A_31210,B_31211,B_31211),A_31210)
      | r2_hidden('#skF_2'(A_31210,B_31211,B_31211),B_31211)
      | k2_xboole_0(A_31210,B_31211) = B_31211 ) ),
    inference(resolution,[status(thm)],[c_28650,c_16])).

tff(c_28442,plain,(
    ! [A_30641,B_30642,C_30643] :
      ( r2_hidden('#skF_1'(A_30641,B_30642,C_30643),B_30642)
      | r2_hidden('#skF_1'(A_30641,B_30642,C_30643),A_30641)
      | ~ r2_hidden('#skF_2'(A_30641,B_30642,C_30643),B_30642)
      | k2_xboole_0(A_30641,B_30642) = C_30643 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_8,plain,(
    ! [A_1,B_2,C_3] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2,C_3),C_3)
      | ~ r2_hidden('#skF_2'(A_1,B_2,C_3),B_2)
      | k2_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_28588,plain,(
    ! [A_30641,B_30642] :
      ( r2_hidden('#skF_1'(A_30641,B_30642,B_30642),A_30641)
      | ~ r2_hidden('#skF_2'(A_30641,B_30642,B_30642),B_30642)
      | k2_xboole_0(A_30641,B_30642) = B_30642 ) ),
    inference(resolution,[status(thm)],[c_28442,c_8])).

tff(c_29766,plain,(
    ! [A_31262,B_31263] :
      ( r2_hidden('#skF_1'(A_31262,B_31263,B_31263),A_31262)
      | k2_xboole_0(A_31262,B_31263) = B_31263 ) ),
    inference(resolution,[status(thm)],[c_29635,c_28588])).

tff(c_30090,plain,(
    ! [B_31468,B_31469] :
      ( B_31468 = '#skF_1'('#skF_7',B_31469,B_31469)
      | k2_xboole_0('#skF_7',B_31469) = B_31469 ) ),
    inference(resolution,[status(thm)],[c_29766,c_1635])).

tff(c_31170,plain,(
    ! [B_31468] :
      ( k1_tarski('#skF_6') = '#skF_8'
      | B_31468 = '#skF_1'('#skF_7','#skF_8','#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30090,c_70])).

tff(c_31449,plain,(
    '#skF_1'('#skF_7','#skF_8','#skF_8') = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_594,c_31170])).

tff(c_29750,plain,(
    ! [A_31210,B_31211] :
      ( r2_hidden('#skF_1'(A_31210,B_31211,B_31211),A_31210)
      | k2_xboole_0(A_31210,B_31211) = B_31211 ) ),
    inference(resolution,[status(thm)],[c_29635,c_28588])).

tff(c_31452,plain,
    ( r2_hidden('#skF_6','#skF_7')
    | k2_xboole_0('#skF_7','#skF_8') = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_31449,c_29750])).

tff(c_31942,plain,
    ( r2_hidden('#skF_6','#skF_7')
    | k1_tarski('#skF_6') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_31452])).

tff(c_31944,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_594,c_2630,c_31942])).

tff(c_31946,plain,(
    k1_tarski('#skF_6') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_68,plain,
    ( k1_tarski('#skF_6') != '#skF_8'
    | k1_tarski('#skF_6') != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_31978,plain,(
    '#skF_7' != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_31946,c_31946,c_68])).

tff(c_31945,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_31951,plain,(
    k2_xboole_0('#skF_7','#skF_8') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_31946,c_70])).

tff(c_32181,plain,(
    ! [D_40395,B_40396,A_40397] :
      ( ~ r2_hidden(D_40395,B_40396)
      | r2_hidden(D_40395,k2_xboole_0(A_40397,B_40396)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_32261,plain,(
    ! [D_40400] :
      ( ~ r2_hidden(D_40400,'#skF_8')
      | r2_hidden(D_40400,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_31951,c_32181])).

tff(c_31984,plain,(
    ! [C_40374,A_40375] :
      ( C_40374 = A_40375
      | ~ r2_hidden(C_40374,k1_tarski(A_40375)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_31987,plain,(
    ! [C_40374] :
      ( C_40374 = '#skF_6'
      | ~ r2_hidden(C_40374,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_31946,c_31984])).

tff(c_32296,plain,(
    ! [D_40404] :
      ( D_40404 = '#skF_6'
      | ~ r2_hidden(D_40404,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_32261,c_31987])).

tff(c_32304,plain,
    ( '#skF_3'('#skF_8') = '#skF_6'
    | k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_20,c_32296])).

tff(c_32309,plain,(
    '#skF_3'('#skF_8') = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_31945,c_32304])).

tff(c_32313,plain,
    ( r2_hidden('#skF_6','#skF_8')
    | k1_xboole_0 = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_32309,c_20])).

tff(c_32316,plain,(
    r2_hidden('#skF_6','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_31945,c_32313])).

tff(c_32064,plain,(
    ! [A_40385,B_40386] :
      ( r1_tarski(k1_tarski(A_40385),B_40386)
      | ~ r2_hidden(A_40385,B_40386) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_32070,plain,(
    ! [B_40386] :
      ( r1_tarski('#skF_7',B_40386)
      | ~ r2_hidden('#skF_6',B_40386) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_31946,c_32064])).

tff(c_32326,plain,(
    r1_tarski('#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_32316,c_32070])).

tff(c_22,plain,(
    ! [A_9,B_10] :
      ( k2_xboole_0(A_9,B_10) = B_10
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_32330,plain,(
    k2_xboole_0('#skF_7','#skF_8') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_32326,c_22])).

tff(c_32331,plain,(
    '#skF_7' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32330,c_31951])).

tff(c_32333,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_31978,c_32331])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:13:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.76/3.84  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.76/3.85  
% 10.76/3.85  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.76/3.85  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_6 > #skF_2 > #skF_8 > #skF_3 > #skF_5 > #skF_4
% 10.76/3.85  
% 10.76/3.85  %Foreground sorts:
% 10.76/3.85  
% 10.76/3.85  
% 10.76/3.85  %Background operators:
% 10.76/3.85  
% 10.76/3.85  
% 10.76/3.85  %Foreground operators:
% 10.76/3.85  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 10.76/3.85  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.76/3.85  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.76/3.85  tff(k1_tarski, type, k1_tarski: $i > $i).
% 10.76/3.85  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.76/3.85  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 10.76/3.85  tff('#skF_7', type, '#skF_7': $i).
% 10.76/3.85  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.76/3.85  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 10.76/3.85  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 10.76/3.85  tff('#skF_6', type, '#skF_6': $i).
% 10.76/3.85  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 10.76/3.85  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 10.76/3.85  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 10.76/3.85  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 10.76/3.85  tff('#skF_8', type, '#skF_8': $i).
% 10.76/3.85  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.76/3.85  tff(k3_tarski, type, k3_tarski: $i > $i).
% 10.76/3.85  tff('#skF_3', type, '#skF_3': $i > $i).
% 10.76/3.85  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.76/3.85  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 10.76/3.85  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 10.76/3.85  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 10.76/3.85  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 10.76/3.85  
% 11.02/3.87  tff(f_100, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 11.02/3.87  tff(f_48, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 11.02/3.87  tff(f_79, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 11.02/3.87  tff(f_42, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 11.02/3.87  tff(f_55, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 11.02/3.87  tff(f_34, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 11.02/3.87  tff(f_46, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 11.02/3.87  tff(f_73, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 11.02/3.87  tff(c_66, plain, (k1_tarski('#skF_6')!='#skF_8' | k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_100])).
% 11.02/3.87  tff(c_92, plain, (k1_xboole_0!='#skF_7'), inference(splitLeft, [status(thm)], [c_66])).
% 11.02/3.87  tff(c_64, plain, (k1_xboole_0!='#skF_8' | k1_tarski('#skF_6')!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_100])).
% 11.02/3.87  tff(c_82, plain, (k1_tarski('#skF_6')!='#skF_7'), inference(splitLeft, [status(thm)], [c_64])).
% 11.02/3.87  tff(c_70, plain, (k2_xboole_0('#skF_7', '#skF_8')=k1_tarski('#skF_6')), inference(cnfTransformation, [status(thm)], [f_100])).
% 11.02/3.87  tff(c_88, plain, (![A_56, B_57]: (r1_tarski(A_56, k2_xboole_0(A_56, B_57)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 11.02/3.87  tff(c_91, plain, (r1_tarski('#skF_7', k1_tarski('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_70, c_88])).
% 11.02/3.87  tff(c_575, plain, (![B_105, A_106]: (k1_tarski(B_105)=A_106 | k1_xboole_0=A_106 | ~r1_tarski(A_106, k1_tarski(B_105)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 11.02/3.87  tff(c_582, plain, (k1_tarski('#skF_6')='#skF_7' | k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_91, c_575])).
% 11.02/3.87  tff(c_593, plain, $false, inference(negUnitSimplification, [status(thm)], [c_92, c_82, c_582])).
% 11.02/3.87  tff(c_594, plain, (k1_tarski('#skF_6')!='#skF_8'), inference(splitRight, [status(thm)], [c_66])).
% 11.02/3.87  tff(c_595, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_66])).
% 11.02/3.87  tff(c_20, plain, (![A_7]: (r2_hidden('#skF_3'(A_7), A_7) | k1_xboole_0=A_7)), inference(cnfTransformation, [status(thm)], [f_42])).
% 11.02/3.87  tff(c_603, plain, (![A_7]: (r2_hidden('#skF_3'(A_7), A_7) | A_7='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_595, c_20])).
% 11.02/3.87  tff(c_605, plain, (![C_109, A_110]: (C_109=A_110 | ~r2_hidden(C_109, k1_tarski(A_110)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 11.02/3.87  tff(c_613, plain, (![A_110]: ('#skF_3'(k1_tarski(A_110))=A_110 | k1_tarski(A_110)='#skF_7')), inference(resolution, [status(thm)], [c_603, c_605])).
% 11.02/3.87  tff(c_2015, plain, (![D_4526, B_4527, A_4528]: (r2_hidden(D_4526, B_4527) | r2_hidden(D_4526, A_4528) | ~r2_hidden(D_4526, k2_xboole_0(A_4528, B_4527)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 11.02/3.87  tff(c_2153, plain, (![D_4536]: (r2_hidden(D_4536, '#skF_8') | r2_hidden(D_4536, '#skF_7') | ~r2_hidden(D_4536, k1_tarski('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_70, c_2015])).
% 11.02/3.87  tff(c_2164, plain, (r2_hidden('#skF_3'(k1_tarski('#skF_6')), '#skF_8') | r2_hidden('#skF_3'(k1_tarski('#skF_6')), '#skF_7') | k1_tarski('#skF_6')='#skF_7'), inference(resolution, [status(thm)], [c_603, c_2153])).
% 11.02/3.87  tff(c_2173, plain, (r2_hidden('#skF_3'(k1_tarski('#skF_6')), '#skF_8') | r2_hidden('#skF_3'(k1_tarski('#skF_6')), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_82, c_2164])).
% 11.02/3.87  tff(c_2176, plain, (r2_hidden('#skF_3'(k1_tarski('#skF_6')), '#skF_7')), inference(splitLeft, [status(thm)], [c_2173])).
% 11.02/3.87  tff(c_2188, plain, (r2_hidden('#skF_6', '#skF_7') | k1_tarski('#skF_6')='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_613, c_2176])).
% 11.02/3.87  tff(c_2193, plain, (r2_hidden('#skF_6', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_82, c_2188])).
% 11.02/3.87  tff(c_60, plain, (![B_49]: (r1_tarski(k1_xboole_0, k1_tarski(B_49)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 11.02/3.87  tff(c_596, plain, (![B_49]: (r1_tarski('#skF_7', k1_tarski(B_49)))), inference(demodulation, [status(thm), theory('equality')], [c_595, c_60])).
% 11.02/3.87  tff(c_642, plain, (![A_119, B_120]: (k2_xboole_0(A_119, B_120)=B_120 | ~r1_tarski(A_119, B_120))), inference(cnfTransformation, [status(thm)], [f_46])).
% 11.02/3.87  tff(c_656, plain, (![B_49]: (k2_xboole_0('#skF_7', k1_tarski(B_49))=k1_tarski(B_49))), inference(resolution, [status(thm)], [c_596, c_642])).
% 11.02/3.87  tff(c_684, plain, (![D_124, A_125, B_126]: (~r2_hidden(D_124, A_125) | r2_hidden(D_124, k2_xboole_0(A_125, B_126)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 11.02/3.87  tff(c_1631, plain, (![D_4498, B_4499]: (~r2_hidden(D_4498, '#skF_7') | r2_hidden(D_4498, k1_tarski(B_4499)))), inference(superposition, [status(thm), theory('equality')], [c_656, c_684])).
% 11.02/3.87  tff(c_26, plain, (![C_17, A_13]: (C_17=A_13 | ~r2_hidden(C_17, k1_tarski(A_13)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 11.02/3.87  tff(c_1635, plain, (![D_4498, B_4499]: (D_4498=B_4499 | ~r2_hidden(D_4498, '#skF_7'))), inference(resolution, [status(thm)], [c_1631, c_26])).
% 11.02/3.87  tff(c_2212, plain, ('#skF_6'='#skF_8'), inference(resolution, [status(thm)], [c_2193, c_1635])).
% 11.02/3.87  tff(c_2210, plain, (![B_4499]: (B_4499='#skF_6')), inference(resolution, [status(thm)], [c_2193, c_1635])).
% 11.02/3.87  tff(c_2387, plain, (![B_7188]: (B_7188='#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_2212, c_2210])).
% 11.02/3.87  tff(c_28, plain, (![C_17]: (r2_hidden(C_17, k1_tarski(C_17)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 11.02/3.87  tff(c_739, plain, (![D_131, B_132, A_133]: (~r2_hidden(D_131, B_132) | r2_hidden(D_131, k2_xboole_0(A_133, B_132)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 11.02/3.87  tff(c_800, plain, (![D_137]: (~r2_hidden(D_137, '#skF_8') | r2_hidden(D_137, k1_tarski('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_70, c_739])).
% 11.02/3.87  tff(c_805, plain, (![D_138]: (D_138='#skF_6' | ~r2_hidden(D_138, '#skF_8'))), inference(resolution, [status(thm)], [c_800, c_26])).
% 11.02/3.87  tff(c_810, plain, ('#skF_3'('#skF_8')='#skF_6' | '#skF_7'='#skF_8'), inference(resolution, [status(thm)], [c_603, c_805])).
% 11.02/3.87  tff(c_811, plain, ('#skF_7'='#skF_8'), inference(splitLeft, [status(thm)], [c_810])).
% 11.02/3.87  tff(c_818, plain, (k2_xboole_0('#skF_8', '#skF_8')=k1_tarski('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_811, c_70])).
% 11.02/3.87  tff(c_1162, plain, (![D_166, B_167, A_168]: (r2_hidden(D_166, B_167) | r2_hidden(D_166, A_168) | ~r2_hidden(D_166, k2_xboole_0(A_168, B_167)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 11.02/3.87  tff(c_1306, plain, (![D_176]: (r2_hidden(D_176, '#skF_8') | r2_hidden(D_176, '#skF_8') | ~r2_hidden(D_176, k1_tarski('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_818, c_1162])).
% 11.02/3.87  tff(c_1323, plain, (r2_hidden('#skF_6', '#skF_8')), inference(resolution, [status(thm)], [c_28, c_1306])).
% 11.02/3.87  tff(c_687, plain, (![D_124, B_49]: (~r2_hidden(D_124, '#skF_7') | r2_hidden(D_124, k1_tarski(B_49)))), inference(superposition, [status(thm), theory('equality')], [c_656, c_684])).
% 11.02/3.87  tff(c_922, plain, (![D_148, B_149]: (~r2_hidden(D_148, '#skF_8') | r2_hidden(D_148, k1_tarski(B_149)))), inference(demodulation, [status(thm), theory('equality')], [c_811, c_687])).
% 11.02/3.87  tff(c_926, plain, (![D_148, B_149]: (D_148=B_149 | ~r2_hidden(D_148, '#skF_8'))), inference(resolution, [status(thm)], [c_922, c_26])).
% 11.02/3.87  tff(c_1331, plain, ('#skF_6'='#skF_8'), inference(resolution, [status(thm)], [c_1323, c_926])).
% 11.02/3.87  tff(c_1329, plain, (![B_149]: (B_149='#skF_6')), inference(resolution, [status(thm)], [c_1323, c_926])).
% 11.02/3.87  tff(c_1459, plain, (![B_2441]: (B_2441='#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_1331, c_1329])).
% 11.02/3.87  tff(c_1512, plain, (k1_tarski('#skF_6')='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_1459, c_818])).
% 11.02/3.87  tff(c_1574, plain, $false, inference(negUnitSimplification, [status(thm)], [c_594, c_1512])).
% 11.02/3.87  tff(c_1576, plain, ('#skF_7'!='#skF_8'), inference(splitRight, [status(thm)], [c_810])).
% 11.02/3.87  tff(c_2558, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_2387, c_1576])).
% 11.02/3.87  tff(c_2559, plain, (r2_hidden('#skF_3'(k1_tarski('#skF_6')), '#skF_8')), inference(splitRight, [status(thm)], [c_2173])).
% 11.02/3.87  tff(c_804, plain, (![D_137]: (D_137='#skF_6' | ~r2_hidden(D_137, '#skF_8'))), inference(resolution, [status(thm)], [c_800, c_26])).
% 11.02/3.87  tff(c_2606, plain, ('#skF_3'(k1_tarski('#skF_6'))='#skF_6'), inference(resolution, [status(thm)], [c_2559, c_804])).
% 11.02/3.87  tff(c_2560, plain, (~r2_hidden('#skF_3'(k1_tarski('#skF_6')), '#skF_7')), inference(splitRight, [status(thm)], [c_2173])).
% 11.02/3.87  tff(c_2630, plain, (~r2_hidden('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_2606, c_2560])).
% 11.02/3.87  tff(c_28650, plain, (![A_30694, B_30695, C_30696]: (r2_hidden('#skF_1'(A_30694, B_30695, C_30696), B_30695) | r2_hidden('#skF_1'(A_30694, B_30695, C_30696), A_30694) | r2_hidden('#skF_2'(A_30694, B_30695, C_30696), C_30696) | k2_xboole_0(A_30694, B_30695)=C_30696)), inference(cnfTransformation, [status(thm)], [f_34])).
% 11.02/3.87  tff(c_16, plain, (![A_1, B_2, C_3]: (~r2_hidden('#skF_1'(A_1, B_2, C_3), C_3) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k2_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 11.02/3.87  tff(c_29635, plain, (![A_31210, B_31211]: (r2_hidden('#skF_1'(A_31210, B_31211, B_31211), A_31210) | r2_hidden('#skF_2'(A_31210, B_31211, B_31211), B_31211) | k2_xboole_0(A_31210, B_31211)=B_31211)), inference(resolution, [status(thm)], [c_28650, c_16])).
% 11.02/3.87  tff(c_28442, plain, (![A_30641, B_30642, C_30643]: (r2_hidden('#skF_1'(A_30641, B_30642, C_30643), B_30642) | r2_hidden('#skF_1'(A_30641, B_30642, C_30643), A_30641) | ~r2_hidden('#skF_2'(A_30641, B_30642, C_30643), B_30642) | k2_xboole_0(A_30641, B_30642)=C_30643)), inference(cnfTransformation, [status(thm)], [f_34])).
% 11.02/3.87  tff(c_8, plain, (![A_1, B_2, C_3]: (~r2_hidden('#skF_1'(A_1, B_2, C_3), C_3) | ~r2_hidden('#skF_2'(A_1, B_2, C_3), B_2) | k2_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 11.02/3.87  tff(c_28588, plain, (![A_30641, B_30642]: (r2_hidden('#skF_1'(A_30641, B_30642, B_30642), A_30641) | ~r2_hidden('#skF_2'(A_30641, B_30642, B_30642), B_30642) | k2_xboole_0(A_30641, B_30642)=B_30642)), inference(resolution, [status(thm)], [c_28442, c_8])).
% 11.02/3.87  tff(c_29766, plain, (![A_31262, B_31263]: (r2_hidden('#skF_1'(A_31262, B_31263, B_31263), A_31262) | k2_xboole_0(A_31262, B_31263)=B_31263)), inference(resolution, [status(thm)], [c_29635, c_28588])).
% 11.02/3.87  tff(c_30090, plain, (![B_31468, B_31469]: (B_31468='#skF_1'('#skF_7', B_31469, B_31469) | k2_xboole_0('#skF_7', B_31469)=B_31469)), inference(resolution, [status(thm)], [c_29766, c_1635])).
% 11.02/3.87  tff(c_31170, plain, (![B_31468]: (k1_tarski('#skF_6')='#skF_8' | B_31468='#skF_1'('#skF_7', '#skF_8', '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_30090, c_70])).
% 11.02/3.87  tff(c_31449, plain, ('#skF_1'('#skF_7', '#skF_8', '#skF_8')='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_594, c_31170])).
% 11.02/3.87  tff(c_29750, plain, (![A_31210, B_31211]: (r2_hidden('#skF_1'(A_31210, B_31211, B_31211), A_31210) | k2_xboole_0(A_31210, B_31211)=B_31211)), inference(resolution, [status(thm)], [c_29635, c_28588])).
% 11.02/3.87  tff(c_31452, plain, (r2_hidden('#skF_6', '#skF_7') | k2_xboole_0('#skF_7', '#skF_8')='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_31449, c_29750])).
% 11.02/3.87  tff(c_31942, plain, (r2_hidden('#skF_6', '#skF_7') | k1_tarski('#skF_6')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_31452])).
% 11.02/3.87  tff(c_31944, plain, $false, inference(negUnitSimplification, [status(thm)], [c_594, c_2630, c_31942])).
% 11.02/3.87  tff(c_31946, plain, (k1_tarski('#skF_6')='#skF_7'), inference(splitRight, [status(thm)], [c_64])).
% 11.02/3.87  tff(c_68, plain, (k1_tarski('#skF_6')!='#skF_8' | k1_tarski('#skF_6')!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_100])).
% 11.02/3.87  tff(c_31978, plain, ('#skF_7'!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_31946, c_31946, c_68])).
% 11.02/3.87  tff(c_31945, plain, (k1_xboole_0!='#skF_8'), inference(splitRight, [status(thm)], [c_64])).
% 11.02/3.87  tff(c_31951, plain, (k2_xboole_0('#skF_7', '#skF_8')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_31946, c_70])).
% 11.02/3.87  tff(c_32181, plain, (![D_40395, B_40396, A_40397]: (~r2_hidden(D_40395, B_40396) | r2_hidden(D_40395, k2_xboole_0(A_40397, B_40396)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 11.02/3.87  tff(c_32261, plain, (![D_40400]: (~r2_hidden(D_40400, '#skF_8') | r2_hidden(D_40400, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_31951, c_32181])).
% 11.02/3.87  tff(c_31984, plain, (![C_40374, A_40375]: (C_40374=A_40375 | ~r2_hidden(C_40374, k1_tarski(A_40375)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 11.02/3.87  tff(c_31987, plain, (![C_40374]: (C_40374='#skF_6' | ~r2_hidden(C_40374, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_31946, c_31984])).
% 11.02/3.87  tff(c_32296, plain, (![D_40404]: (D_40404='#skF_6' | ~r2_hidden(D_40404, '#skF_8'))), inference(resolution, [status(thm)], [c_32261, c_31987])).
% 11.02/3.87  tff(c_32304, plain, ('#skF_3'('#skF_8')='#skF_6' | k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_20, c_32296])).
% 11.02/3.87  tff(c_32309, plain, ('#skF_3'('#skF_8')='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_31945, c_32304])).
% 11.02/3.87  tff(c_32313, plain, (r2_hidden('#skF_6', '#skF_8') | k1_xboole_0='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_32309, c_20])).
% 11.02/3.87  tff(c_32316, plain, (r2_hidden('#skF_6', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_31945, c_32313])).
% 11.02/3.87  tff(c_32064, plain, (![A_40385, B_40386]: (r1_tarski(k1_tarski(A_40385), B_40386) | ~r2_hidden(A_40385, B_40386))), inference(cnfTransformation, [status(thm)], [f_73])).
% 11.02/3.87  tff(c_32070, plain, (![B_40386]: (r1_tarski('#skF_7', B_40386) | ~r2_hidden('#skF_6', B_40386))), inference(superposition, [status(thm), theory('equality')], [c_31946, c_32064])).
% 11.02/3.87  tff(c_32326, plain, (r1_tarski('#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_32316, c_32070])).
% 11.02/3.87  tff(c_22, plain, (![A_9, B_10]: (k2_xboole_0(A_9, B_10)=B_10 | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_46])).
% 11.02/3.87  tff(c_32330, plain, (k2_xboole_0('#skF_7', '#skF_8')='#skF_8'), inference(resolution, [status(thm)], [c_32326, c_22])).
% 11.02/3.87  tff(c_32331, plain, ('#skF_7'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_32330, c_31951])).
% 11.02/3.87  tff(c_32333, plain, $false, inference(negUnitSimplification, [status(thm)], [c_31978, c_32331])).
% 11.02/3.87  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.02/3.87  
% 11.02/3.87  Inference rules
% 11.02/3.87  ----------------------
% 11.02/3.87  #Ref     : 0
% 11.02/3.87  #Sup     : 5833
% 11.02/3.87  #Fact    : 10
% 11.02/3.87  #Define  : 0
% 11.02/3.87  #Split   : 11
% 11.02/3.87  #Chain   : 0
% 11.02/3.87  #Close   : 0
% 11.02/3.87  
% 11.02/3.87  Ordering : KBO
% 11.02/3.87  
% 11.02/3.87  Simplification rules
% 11.02/3.87  ----------------------
% 11.02/3.87  #Subsume      : 1537
% 11.02/3.87  #Demod        : 1697
% 11.02/3.87  #Tautology    : 821
% 11.02/3.87  #SimpNegUnit  : 96
% 11.02/3.87  #BackRed      : 40
% 11.02/3.87  
% 11.02/3.87  #Partial instantiations: 10733
% 11.02/3.87  #Strategies tried      : 1
% 11.02/3.87  
% 11.02/3.87  Timing (in seconds)
% 11.02/3.87  ----------------------
% 11.02/3.87  Preprocessing        : 0.37
% 11.02/3.87  Parsing              : 0.17
% 11.02/3.87  CNF conversion       : 0.03
% 11.02/3.87  Main loop            : 2.71
% 11.02/3.87  Inferencing          : 0.92
% 11.02/3.87  Reduction            : 0.80
% 11.02/3.87  Demodulation         : 0.59
% 11.02/3.87  BG Simplification    : 0.11
% 11.02/3.87  Subsumption          : 0.68
% 11.02/3.87  Abstraction          : 0.15
% 11.02/3.87  MUC search           : 0.00
% 11.02/3.87  Cooper               : 0.00
% 11.02/3.87  Total                : 3.12
% 11.02/3.87  Index Insertion      : 0.00
% 11.02/3.87  Index Deletion       : 0.00
% 11.02/3.87  Index Matching       : 0.00
% 11.02/3.87  BG Taut test         : 0.00
%------------------------------------------------------------------------------
