%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:21 EST 2020

% Result     : Theorem 9.37s
% Output     : CNFRefutation 9.37s
% Verified   : 
% Statistics : Number of formulae       :   56 (  77 expanded)
%              Number of leaves         :   25 (  38 expanded)
%              Depth                    :   19
%              Number of atoms          :  139 ( 211 expanded)
%              Number of equality atoms :   32 (  47 expanded)
%              Maximal formula depth    :   22 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k4_zfmisc_1 > k4_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff(k4_zfmisc_1,type,(
    k4_zfmisc_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(k4_mcart_1,type,(
    k4_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_68,negated_conjecture,(
    ~ ! [A,B,C,D,E] :
        ~ ( r2_hidden(A,k4_zfmisc_1(B,C,D,E))
          & ! [F,G,H,I] :
              ~ ( r2_hidden(F,B)
                & r2_hidden(G,C)
                & r2_hidden(H,D)
                & r2_hidden(I,E)
                & A = k4_mcart_1(F,G,H,I) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_mcart_1)).

tff(f_52,axiom,(
    ! [A,B,C,D] : k4_zfmisc_1(A,B,C,D) = k2_zfmisc_1(k3_zfmisc_1(A,B,C),D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_zfmisc_1)).

tff(f_44,axiom,(
    ! [A,B,C,D] :
      ~ ( r1_tarski(A,k2_zfmisc_1(B,C))
        & r2_hidden(D,A)
        & ! [E,F] :
            ~ ( r2_hidden(E,B)
              & r2_hidden(F,C)
              & D = k4_tarski(E,F) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_zfmisc_1)).

tff(f_48,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_46,axiom,(
    ! [A,B,C] : k3_mcart_1(A,B,C) = k4_tarski(k4_tarski(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

tff(f_50,axiom,(
    ! [A,B,C,D] : k4_mcart_1(A,B,C,D) = k4_tarski(k3_mcart_1(A,B,C),D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_mcart_1)).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_24,plain,(
    r2_hidden('#skF_3',k4_zfmisc_1('#skF_4','#skF_5','#skF_6','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_20,plain,(
    ! [A_19,B_20,C_21,D_22] : k2_zfmisc_1(k3_zfmisc_1(A_19,B_20,C_21),D_22) = k4_zfmisc_1(A_19,B_20,C_21,D_22) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_12,plain,(
    ! [A_3,B_4,C_5,D_6] :
      ( r2_hidden('#skF_1'(A_3,B_4,C_5,D_6),B_4)
      | ~ r2_hidden(D_6,A_3)
      | ~ r1_tarski(A_3,k2_zfmisc_1(B_4,C_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_16,plain,(
    ! [A_12,B_13,C_14] : k2_zfmisc_1(k2_zfmisc_1(A_12,B_13),C_14) = k3_zfmisc_1(A_12,B_13,C_14) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_10,plain,(
    ! [A_3,B_4,C_5,D_6] :
      ( r2_hidden('#skF_2'(A_3,B_4,C_5,D_6),C_5)
      | ~ r2_hidden(D_6,A_3)
      | ~ r1_tarski(A_3,k2_zfmisc_1(B_4,C_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_8,plain,(
    ! [A_3,B_4,C_5,D_6] :
      ( k4_tarski('#skF_1'(A_3,B_4,C_5,D_6),'#skF_2'(A_3,B_4,C_5,D_6)) = D_6
      | ~ r2_hidden(D_6,A_3)
      | ~ r1_tarski(A_3,k2_zfmisc_1(B_4,C_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_261,plain,(
    ! [A_105,B_106,C_107,D_108] :
      ( k4_tarski('#skF_1'(A_105,B_106,C_107,D_108),'#skF_2'(A_105,B_106,C_107,D_108)) = D_108
      | ~ r2_hidden(D_108,A_105)
      | ~ r1_tarski(A_105,k2_zfmisc_1(B_106,C_107)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_14,plain,(
    ! [A_9,B_10,C_11] : k4_tarski(k4_tarski(A_9,B_10),C_11) = k3_mcart_1(A_9,B_10,C_11) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_273,plain,(
    ! [C_11,D_108,A_105,C_107,B_106] :
      ( k3_mcart_1('#skF_1'(A_105,B_106,C_107,D_108),'#skF_2'(A_105,B_106,C_107,D_108),C_11) = k4_tarski(D_108,C_11)
      | ~ r2_hidden(D_108,A_105)
      | ~ r1_tarski(A_105,k2_zfmisc_1(B_106,C_107)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_261,c_14])).

tff(c_18,plain,(
    ! [A_15,B_16,C_17,D_18] : k4_tarski(k3_mcart_1(A_15,B_16,C_17),D_18) = k4_mcart_1(A_15,B_16,C_17,D_18) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_49,plain,(
    ! [A_37,B_38,C_39] : k4_tarski(k4_tarski(A_37,B_38),C_39) = k3_mcart_1(A_37,B_38,C_39) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_58,plain,(
    ! [A_9,B_10,C_11,C_39] : k3_mcart_1(k4_tarski(A_9,B_10),C_11,C_39) = k4_tarski(k3_mcart_1(A_9,B_10,C_11),C_39) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_49])).

tff(c_88,plain,(
    ! [A_9,B_10,C_11,C_39] : k3_mcart_1(k4_tarski(A_9,B_10),C_11,C_39) = k4_mcart_1(A_9,B_10,C_11,C_39) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_58])).

tff(c_317,plain,(
    ! [C_125,B_121,C_122,A_120,D_124,C_123] :
      ( k4_mcart_1('#skF_1'(A_120,B_121,C_123,D_124),'#skF_2'(A_120,B_121,C_123,D_124),C_125,C_122) = k3_mcart_1(D_124,C_125,C_122)
      | ~ r2_hidden(D_124,A_120)
      | ~ r1_tarski(A_120,k2_zfmisc_1(B_121,C_123)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_261,c_88])).

tff(c_22,plain,(
    ! [F_27,G_28,H_29,I_30] :
      ( k4_mcart_1(F_27,G_28,H_29,I_30) != '#skF_3'
      | ~ r2_hidden(I_30,'#skF_7')
      | ~ r2_hidden(H_29,'#skF_6')
      | ~ r2_hidden(G_28,'#skF_5')
      | ~ r2_hidden(F_27,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_406,plain,(
    ! [C_154,C_155,B_152,D_153,C_150,A_151] :
      ( k3_mcart_1(D_153,C_150,C_155) != '#skF_3'
      | ~ r2_hidden(C_155,'#skF_7')
      | ~ r2_hidden(C_150,'#skF_6')
      | ~ r2_hidden('#skF_2'(A_151,B_152,C_154,D_153),'#skF_5')
      | ~ r2_hidden('#skF_1'(A_151,B_152,C_154,D_153),'#skF_4')
      | ~ r2_hidden(D_153,A_151)
      | ~ r1_tarski(A_151,k2_zfmisc_1(B_152,C_154)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_317,c_22])).

tff(c_818,plain,(
    ! [C_331,A_325,C_326,B_328,C_329,D_330,A_327,B_324] :
      ( k4_tarski(D_330,C_331) != '#skF_3'
      | ~ r2_hidden(C_331,'#skF_7')
      | ~ r2_hidden('#skF_2'(A_325,B_328,C_329,D_330),'#skF_6')
      | ~ r2_hidden('#skF_2'(A_327,B_324,C_326,'#skF_1'(A_325,B_328,C_329,D_330)),'#skF_5')
      | ~ r2_hidden('#skF_1'(A_327,B_324,C_326,'#skF_1'(A_325,B_328,C_329,D_330)),'#skF_4')
      | ~ r2_hidden('#skF_1'(A_325,B_328,C_329,D_330),A_327)
      | ~ r1_tarski(A_327,k2_zfmisc_1(B_324,C_326))
      | ~ r2_hidden(D_330,A_325)
      | ~ r1_tarski(A_325,k2_zfmisc_1(B_328,C_329)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_273,c_406])).

tff(c_5161,plain,(
    ! [A_1472,C_1477,B_1479,D_1470,A_1478,A_1474,B_1475,B_1471,C_1476,C_1473] :
      ( D_1470 != '#skF_3'
      | ~ r2_hidden('#skF_2'(A_1474,B_1479,C_1477,D_1470),'#skF_7')
      | ~ r2_hidden('#skF_2'(A_1472,B_1475,C_1476,'#skF_1'(A_1474,B_1479,C_1477,D_1470)),'#skF_6')
      | ~ r2_hidden('#skF_2'(A_1478,B_1471,C_1473,'#skF_1'(A_1472,B_1475,C_1476,'#skF_1'(A_1474,B_1479,C_1477,D_1470))),'#skF_5')
      | ~ r2_hidden('#skF_1'(A_1478,B_1471,C_1473,'#skF_1'(A_1472,B_1475,C_1476,'#skF_1'(A_1474,B_1479,C_1477,D_1470))),'#skF_4')
      | ~ r2_hidden('#skF_1'(A_1472,B_1475,C_1476,'#skF_1'(A_1474,B_1479,C_1477,D_1470)),A_1478)
      | ~ r1_tarski(A_1478,k2_zfmisc_1(B_1471,C_1473))
      | ~ r2_hidden('#skF_1'(A_1474,B_1479,C_1477,D_1470),A_1472)
      | ~ r1_tarski(A_1472,k2_zfmisc_1(B_1475,C_1476))
      | ~ r2_hidden(D_1470,A_1474)
      | ~ r1_tarski(A_1474,k2_zfmisc_1(B_1479,C_1477)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_818])).

tff(c_5168,plain,(
    ! [C_1485,B_1481,A_1486,B_1488,A_1480,C_1482,A_1484,B_1483,D_1487] :
      ( D_1487 != '#skF_3'
      | ~ r2_hidden('#skF_2'(A_1480,B_1481,C_1482,D_1487),'#skF_7')
      | ~ r2_hidden('#skF_2'(A_1484,B_1483,C_1485,'#skF_1'(A_1480,B_1481,C_1482,D_1487)),'#skF_6')
      | ~ r2_hidden('#skF_1'(A_1486,B_1488,'#skF_5','#skF_1'(A_1484,B_1483,C_1485,'#skF_1'(A_1480,B_1481,C_1482,D_1487))),'#skF_4')
      | ~ r2_hidden('#skF_1'(A_1480,B_1481,C_1482,D_1487),A_1484)
      | ~ r1_tarski(A_1484,k2_zfmisc_1(B_1483,C_1485))
      | ~ r2_hidden(D_1487,A_1480)
      | ~ r1_tarski(A_1480,k2_zfmisc_1(B_1481,C_1482))
      | ~ r2_hidden('#skF_1'(A_1484,B_1483,C_1485,'#skF_1'(A_1480,B_1481,C_1482,D_1487)),A_1486)
      | ~ r1_tarski(A_1486,k2_zfmisc_1(B_1488,'#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_10,c_5161])).

tff(c_5175,plain,(
    ! [B_1495,A_1494,D_1496,A_1490,C_1492,B_1489,C_1491,A_1493] :
      ( D_1496 != '#skF_3'
      | ~ r2_hidden('#skF_2'(A_1490,B_1495,C_1492,D_1496),'#skF_7')
      | ~ r2_hidden('#skF_2'(A_1494,B_1489,C_1491,'#skF_1'(A_1490,B_1495,C_1492,D_1496)),'#skF_6')
      | ~ r2_hidden('#skF_1'(A_1490,B_1495,C_1492,D_1496),A_1494)
      | ~ r1_tarski(A_1494,k2_zfmisc_1(B_1489,C_1491))
      | ~ r2_hidden(D_1496,A_1490)
      | ~ r1_tarski(A_1490,k2_zfmisc_1(B_1495,C_1492))
      | ~ r2_hidden('#skF_1'(A_1494,B_1489,C_1491,'#skF_1'(A_1490,B_1495,C_1492,D_1496)),A_1493)
      | ~ r1_tarski(A_1493,k2_zfmisc_1('#skF_4','#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_12,c_5168])).

tff(c_5181,plain,(
    ! [D_1499,A_1500,B_1501,A_1497,A_1502,C_1498,B_1503] :
      ( D_1499 != '#skF_3'
      | ~ r2_hidden('#skF_2'(A_1502,B_1501,C_1498,D_1499),'#skF_7')
      | ~ r2_hidden(D_1499,A_1502)
      | ~ r1_tarski(A_1502,k2_zfmisc_1(B_1501,C_1498))
      | ~ r2_hidden('#skF_1'(A_1500,B_1503,'#skF_6','#skF_1'(A_1502,B_1501,C_1498,D_1499)),A_1497)
      | ~ r1_tarski(A_1497,k2_zfmisc_1('#skF_4','#skF_5'))
      | ~ r2_hidden('#skF_1'(A_1502,B_1501,C_1498,D_1499),A_1500)
      | ~ r1_tarski(A_1500,k2_zfmisc_1(B_1503,'#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_10,c_5175])).

tff(c_5281,plain,(
    ! [D_1530,C_1534,B_1532,A_1531,B_1535,A_1533] :
      ( D_1530 != '#skF_3'
      | ~ r2_hidden('#skF_2'(A_1533,B_1532,C_1534,D_1530),'#skF_7')
      | ~ r2_hidden(D_1530,A_1533)
      | ~ r1_tarski(A_1533,k2_zfmisc_1(B_1532,C_1534))
      | ~ r1_tarski(B_1535,k2_zfmisc_1('#skF_4','#skF_5'))
      | ~ r2_hidden('#skF_1'(A_1533,B_1532,C_1534,D_1530),A_1531)
      | ~ r1_tarski(A_1531,k2_zfmisc_1(B_1535,'#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_12,c_5181])).

tff(c_5287,plain,(
    ! [B_1540,B_1538,D_1536,A_1539,A_1537] :
      ( D_1536 != '#skF_3'
      | ~ r1_tarski(B_1538,k2_zfmisc_1('#skF_4','#skF_5'))
      | ~ r2_hidden('#skF_1'(A_1539,B_1540,'#skF_7',D_1536),A_1537)
      | ~ r1_tarski(A_1537,k2_zfmisc_1(B_1538,'#skF_6'))
      | ~ r2_hidden(D_1536,A_1539)
      | ~ r1_tarski(A_1539,k2_zfmisc_1(B_1540,'#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_10,c_5281])).

tff(c_5290,plain,(
    ! [D_1536,A_1539,B_1540,A_1537] :
      ( D_1536 != '#skF_3'
      | ~ r2_hidden('#skF_1'(A_1539,B_1540,'#skF_7',D_1536),A_1537)
      | ~ r1_tarski(A_1537,k2_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'),'#skF_6'))
      | ~ r2_hidden(D_1536,A_1539)
      | ~ r1_tarski(A_1539,k2_zfmisc_1(B_1540,'#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_6,c_5287])).

tff(c_5294,plain,(
    ! [D_1541,A_1542,B_1543,A_1544] :
      ( D_1541 != '#skF_3'
      | ~ r2_hidden('#skF_1'(A_1542,B_1543,'#skF_7',D_1541),A_1544)
      | ~ r1_tarski(A_1544,k3_zfmisc_1('#skF_4','#skF_5','#skF_6'))
      | ~ r2_hidden(D_1541,A_1542)
      | ~ r1_tarski(A_1542,k2_zfmisc_1(B_1543,'#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_5290])).

tff(c_5301,plain,(
    ! [D_1545,B_1546,A_1547] :
      ( D_1545 != '#skF_3'
      | ~ r1_tarski(B_1546,k3_zfmisc_1('#skF_4','#skF_5','#skF_6'))
      | ~ r2_hidden(D_1545,A_1547)
      | ~ r1_tarski(A_1547,k2_zfmisc_1(B_1546,'#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_12,c_5294])).

tff(c_5304,plain,(
    ! [D_1545,A_1547] :
      ( D_1545 != '#skF_3'
      | ~ r2_hidden(D_1545,A_1547)
      | ~ r1_tarski(A_1547,k2_zfmisc_1(k3_zfmisc_1('#skF_4','#skF_5','#skF_6'),'#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_6,c_5301])).

tff(c_5308,plain,(
    ! [D_1548,A_1549] :
      ( D_1548 != '#skF_3'
      | ~ r2_hidden(D_1548,A_1549)
      | ~ r1_tarski(A_1549,k4_zfmisc_1('#skF_4','#skF_5','#skF_6','#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_5304])).

tff(c_5314,plain,(
    ~ r1_tarski(k4_zfmisc_1('#skF_4','#skF_5','#skF_6','#skF_7'),k4_zfmisc_1('#skF_4','#skF_5','#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_24,c_5308])).

tff(c_5320,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_5314])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:28:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.37/3.69  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.37/3.69  
% 9.37/3.69  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.37/3.69  %$ r2_hidden > r1_tarski > k4_zfmisc_1 > k4_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_4 > #skF_1
% 9.37/3.69  
% 9.37/3.69  %Foreground sorts:
% 9.37/3.69  
% 9.37/3.69  
% 9.37/3.69  %Background operators:
% 9.37/3.69  
% 9.37/3.69  
% 9.37/3.69  %Foreground operators:
% 9.37/3.69  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.37/3.69  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.37/3.69  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 9.37/3.69  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 9.37/3.69  tff(k4_zfmisc_1, type, k4_zfmisc_1: ($i * $i * $i * $i) > $i).
% 9.37/3.69  tff('#skF_7', type, '#skF_7': $i).
% 9.37/3.69  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.37/3.69  tff('#skF_5', type, '#skF_5': $i).
% 9.37/3.69  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 9.37/3.69  tff('#skF_6', type, '#skF_6': $i).
% 9.37/3.69  tff('#skF_3', type, '#skF_3': $i).
% 9.37/3.69  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 9.37/3.69  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.37/3.69  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.37/3.69  tff('#skF_4', type, '#skF_4': $i).
% 9.37/3.69  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.37/3.69  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 9.37/3.69  tff(k4_mcart_1, type, k4_mcart_1: ($i * $i * $i * $i) > $i).
% 9.37/3.69  
% 9.37/3.71  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 9.37/3.71  tff(f_68, negated_conjecture, ~(![A, B, C, D, E]: ~(r2_hidden(A, k4_zfmisc_1(B, C, D, E)) & (![F, G, H, I]: ~((((r2_hidden(F, B) & r2_hidden(G, C)) & r2_hidden(H, D)) & r2_hidden(I, E)) & (A = k4_mcart_1(F, G, H, I)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_mcart_1)).
% 9.37/3.71  tff(f_52, axiom, (![A, B, C, D]: (k4_zfmisc_1(A, B, C, D) = k2_zfmisc_1(k3_zfmisc_1(A, B, C), D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_zfmisc_1)).
% 9.37/3.71  tff(f_44, axiom, (![A, B, C, D]: ~((r1_tarski(A, k2_zfmisc_1(B, C)) & r2_hidden(D, A)) & (![E, F]: ~((r2_hidden(E, B) & r2_hidden(F, C)) & (D = k4_tarski(E, F)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t103_zfmisc_1)).
% 9.37/3.71  tff(f_48, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 9.37/3.71  tff(f_46, axiom, (![A, B, C]: (k3_mcart_1(A, B, C) = k4_tarski(k4_tarski(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_mcart_1)).
% 9.37/3.71  tff(f_50, axiom, (![A, B, C, D]: (k4_mcart_1(A, B, C, D) = k4_tarski(k3_mcart_1(A, B, C), D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_mcart_1)).
% 9.37/3.71  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.37/3.71  tff(c_24, plain, (r2_hidden('#skF_3', k4_zfmisc_1('#skF_4', '#skF_5', '#skF_6', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_68])).
% 9.37/3.71  tff(c_20, plain, (![A_19, B_20, C_21, D_22]: (k2_zfmisc_1(k3_zfmisc_1(A_19, B_20, C_21), D_22)=k4_zfmisc_1(A_19, B_20, C_21, D_22))), inference(cnfTransformation, [status(thm)], [f_52])).
% 9.37/3.71  tff(c_12, plain, (![A_3, B_4, C_5, D_6]: (r2_hidden('#skF_1'(A_3, B_4, C_5, D_6), B_4) | ~r2_hidden(D_6, A_3) | ~r1_tarski(A_3, k2_zfmisc_1(B_4, C_5)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 9.37/3.71  tff(c_16, plain, (![A_12, B_13, C_14]: (k2_zfmisc_1(k2_zfmisc_1(A_12, B_13), C_14)=k3_zfmisc_1(A_12, B_13, C_14))), inference(cnfTransformation, [status(thm)], [f_48])).
% 9.37/3.71  tff(c_10, plain, (![A_3, B_4, C_5, D_6]: (r2_hidden('#skF_2'(A_3, B_4, C_5, D_6), C_5) | ~r2_hidden(D_6, A_3) | ~r1_tarski(A_3, k2_zfmisc_1(B_4, C_5)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 9.37/3.71  tff(c_8, plain, (![A_3, B_4, C_5, D_6]: (k4_tarski('#skF_1'(A_3, B_4, C_5, D_6), '#skF_2'(A_3, B_4, C_5, D_6))=D_6 | ~r2_hidden(D_6, A_3) | ~r1_tarski(A_3, k2_zfmisc_1(B_4, C_5)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 9.37/3.71  tff(c_261, plain, (![A_105, B_106, C_107, D_108]: (k4_tarski('#skF_1'(A_105, B_106, C_107, D_108), '#skF_2'(A_105, B_106, C_107, D_108))=D_108 | ~r2_hidden(D_108, A_105) | ~r1_tarski(A_105, k2_zfmisc_1(B_106, C_107)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 9.37/3.71  tff(c_14, plain, (![A_9, B_10, C_11]: (k4_tarski(k4_tarski(A_9, B_10), C_11)=k3_mcart_1(A_9, B_10, C_11))), inference(cnfTransformation, [status(thm)], [f_46])).
% 9.37/3.71  tff(c_273, plain, (![C_11, D_108, A_105, C_107, B_106]: (k3_mcart_1('#skF_1'(A_105, B_106, C_107, D_108), '#skF_2'(A_105, B_106, C_107, D_108), C_11)=k4_tarski(D_108, C_11) | ~r2_hidden(D_108, A_105) | ~r1_tarski(A_105, k2_zfmisc_1(B_106, C_107)))), inference(superposition, [status(thm), theory('equality')], [c_261, c_14])).
% 9.37/3.71  tff(c_18, plain, (![A_15, B_16, C_17, D_18]: (k4_tarski(k3_mcart_1(A_15, B_16, C_17), D_18)=k4_mcart_1(A_15, B_16, C_17, D_18))), inference(cnfTransformation, [status(thm)], [f_50])).
% 9.37/3.71  tff(c_49, plain, (![A_37, B_38, C_39]: (k4_tarski(k4_tarski(A_37, B_38), C_39)=k3_mcart_1(A_37, B_38, C_39))), inference(cnfTransformation, [status(thm)], [f_46])).
% 9.37/3.71  tff(c_58, plain, (![A_9, B_10, C_11, C_39]: (k3_mcart_1(k4_tarski(A_9, B_10), C_11, C_39)=k4_tarski(k3_mcart_1(A_9, B_10, C_11), C_39))), inference(superposition, [status(thm), theory('equality')], [c_14, c_49])).
% 9.37/3.71  tff(c_88, plain, (![A_9, B_10, C_11, C_39]: (k3_mcart_1(k4_tarski(A_9, B_10), C_11, C_39)=k4_mcart_1(A_9, B_10, C_11, C_39))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_58])).
% 9.37/3.71  tff(c_317, plain, (![C_125, B_121, C_122, A_120, D_124, C_123]: (k4_mcart_1('#skF_1'(A_120, B_121, C_123, D_124), '#skF_2'(A_120, B_121, C_123, D_124), C_125, C_122)=k3_mcart_1(D_124, C_125, C_122) | ~r2_hidden(D_124, A_120) | ~r1_tarski(A_120, k2_zfmisc_1(B_121, C_123)))), inference(superposition, [status(thm), theory('equality')], [c_261, c_88])).
% 9.37/3.71  tff(c_22, plain, (![F_27, G_28, H_29, I_30]: (k4_mcart_1(F_27, G_28, H_29, I_30)!='#skF_3' | ~r2_hidden(I_30, '#skF_7') | ~r2_hidden(H_29, '#skF_6') | ~r2_hidden(G_28, '#skF_5') | ~r2_hidden(F_27, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_68])).
% 9.37/3.71  tff(c_406, plain, (![C_154, C_155, B_152, D_153, C_150, A_151]: (k3_mcart_1(D_153, C_150, C_155)!='#skF_3' | ~r2_hidden(C_155, '#skF_7') | ~r2_hidden(C_150, '#skF_6') | ~r2_hidden('#skF_2'(A_151, B_152, C_154, D_153), '#skF_5') | ~r2_hidden('#skF_1'(A_151, B_152, C_154, D_153), '#skF_4') | ~r2_hidden(D_153, A_151) | ~r1_tarski(A_151, k2_zfmisc_1(B_152, C_154)))), inference(superposition, [status(thm), theory('equality')], [c_317, c_22])).
% 9.37/3.71  tff(c_818, plain, (![C_331, A_325, C_326, B_328, C_329, D_330, A_327, B_324]: (k4_tarski(D_330, C_331)!='#skF_3' | ~r2_hidden(C_331, '#skF_7') | ~r2_hidden('#skF_2'(A_325, B_328, C_329, D_330), '#skF_6') | ~r2_hidden('#skF_2'(A_327, B_324, C_326, '#skF_1'(A_325, B_328, C_329, D_330)), '#skF_5') | ~r2_hidden('#skF_1'(A_327, B_324, C_326, '#skF_1'(A_325, B_328, C_329, D_330)), '#skF_4') | ~r2_hidden('#skF_1'(A_325, B_328, C_329, D_330), A_327) | ~r1_tarski(A_327, k2_zfmisc_1(B_324, C_326)) | ~r2_hidden(D_330, A_325) | ~r1_tarski(A_325, k2_zfmisc_1(B_328, C_329)))), inference(superposition, [status(thm), theory('equality')], [c_273, c_406])).
% 9.37/3.71  tff(c_5161, plain, (![A_1472, C_1477, B_1479, D_1470, A_1478, A_1474, B_1475, B_1471, C_1476, C_1473]: (D_1470!='#skF_3' | ~r2_hidden('#skF_2'(A_1474, B_1479, C_1477, D_1470), '#skF_7') | ~r2_hidden('#skF_2'(A_1472, B_1475, C_1476, '#skF_1'(A_1474, B_1479, C_1477, D_1470)), '#skF_6') | ~r2_hidden('#skF_2'(A_1478, B_1471, C_1473, '#skF_1'(A_1472, B_1475, C_1476, '#skF_1'(A_1474, B_1479, C_1477, D_1470))), '#skF_5') | ~r2_hidden('#skF_1'(A_1478, B_1471, C_1473, '#skF_1'(A_1472, B_1475, C_1476, '#skF_1'(A_1474, B_1479, C_1477, D_1470))), '#skF_4') | ~r2_hidden('#skF_1'(A_1472, B_1475, C_1476, '#skF_1'(A_1474, B_1479, C_1477, D_1470)), A_1478) | ~r1_tarski(A_1478, k2_zfmisc_1(B_1471, C_1473)) | ~r2_hidden('#skF_1'(A_1474, B_1479, C_1477, D_1470), A_1472) | ~r1_tarski(A_1472, k2_zfmisc_1(B_1475, C_1476)) | ~r2_hidden(D_1470, A_1474) | ~r1_tarski(A_1474, k2_zfmisc_1(B_1479, C_1477)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_818])).
% 9.37/3.71  tff(c_5168, plain, (![C_1485, B_1481, A_1486, B_1488, A_1480, C_1482, A_1484, B_1483, D_1487]: (D_1487!='#skF_3' | ~r2_hidden('#skF_2'(A_1480, B_1481, C_1482, D_1487), '#skF_7') | ~r2_hidden('#skF_2'(A_1484, B_1483, C_1485, '#skF_1'(A_1480, B_1481, C_1482, D_1487)), '#skF_6') | ~r2_hidden('#skF_1'(A_1486, B_1488, '#skF_5', '#skF_1'(A_1484, B_1483, C_1485, '#skF_1'(A_1480, B_1481, C_1482, D_1487))), '#skF_4') | ~r2_hidden('#skF_1'(A_1480, B_1481, C_1482, D_1487), A_1484) | ~r1_tarski(A_1484, k2_zfmisc_1(B_1483, C_1485)) | ~r2_hidden(D_1487, A_1480) | ~r1_tarski(A_1480, k2_zfmisc_1(B_1481, C_1482)) | ~r2_hidden('#skF_1'(A_1484, B_1483, C_1485, '#skF_1'(A_1480, B_1481, C_1482, D_1487)), A_1486) | ~r1_tarski(A_1486, k2_zfmisc_1(B_1488, '#skF_5')))), inference(resolution, [status(thm)], [c_10, c_5161])).
% 9.37/3.71  tff(c_5175, plain, (![B_1495, A_1494, D_1496, A_1490, C_1492, B_1489, C_1491, A_1493]: (D_1496!='#skF_3' | ~r2_hidden('#skF_2'(A_1490, B_1495, C_1492, D_1496), '#skF_7') | ~r2_hidden('#skF_2'(A_1494, B_1489, C_1491, '#skF_1'(A_1490, B_1495, C_1492, D_1496)), '#skF_6') | ~r2_hidden('#skF_1'(A_1490, B_1495, C_1492, D_1496), A_1494) | ~r1_tarski(A_1494, k2_zfmisc_1(B_1489, C_1491)) | ~r2_hidden(D_1496, A_1490) | ~r1_tarski(A_1490, k2_zfmisc_1(B_1495, C_1492)) | ~r2_hidden('#skF_1'(A_1494, B_1489, C_1491, '#skF_1'(A_1490, B_1495, C_1492, D_1496)), A_1493) | ~r1_tarski(A_1493, k2_zfmisc_1('#skF_4', '#skF_5')))), inference(resolution, [status(thm)], [c_12, c_5168])).
% 9.37/3.71  tff(c_5181, plain, (![D_1499, A_1500, B_1501, A_1497, A_1502, C_1498, B_1503]: (D_1499!='#skF_3' | ~r2_hidden('#skF_2'(A_1502, B_1501, C_1498, D_1499), '#skF_7') | ~r2_hidden(D_1499, A_1502) | ~r1_tarski(A_1502, k2_zfmisc_1(B_1501, C_1498)) | ~r2_hidden('#skF_1'(A_1500, B_1503, '#skF_6', '#skF_1'(A_1502, B_1501, C_1498, D_1499)), A_1497) | ~r1_tarski(A_1497, k2_zfmisc_1('#skF_4', '#skF_5')) | ~r2_hidden('#skF_1'(A_1502, B_1501, C_1498, D_1499), A_1500) | ~r1_tarski(A_1500, k2_zfmisc_1(B_1503, '#skF_6')))), inference(resolution, [status(thm)], [c_10, c_5175])).
% 9.37/3.71  tff(c_5281, plain, (![D_1530, C_1534, B_1532, A_1531, B_1535, A_1533]: (D_1530!='#skF_3' | ~r2_hidden('#skF_2'(A_1533, B_1532, C_1534, D_1530), '#skF_7') | ~r2_hidden(D_1530, A_1533) | ~r1_tarski(A_1533, k2_zfmisc_1(B_1532, C_1534)) | ~r1_tarski(B_1535, k2_zfmisc_1('#skF_4', '#skF_5')) | ~r2_hidden('#skF_1'(A_1533, B_1532, C_1534, D_1530), A_1531) | ~r1_tarski(A_1531, k2_zfmisc_1(B_1535, '#skF_6')))), inference(resolution, [status(thm)], [c_12, c_5181])).
% 9.37/3.71  tff(c_5287, plain, (![B_1540, B_1538, D_1536, A_1539, A_1537]: (D_1536!='#skF_3' | ~r1_tarski(B_1538, k2_zfmisc_1('#skF_4', '#skF_5')) | ~r2_hidden('#skF_1'(A_1539, B_1540, '#skF_7', D_1536), A_1537) | ~r1_tarski(A_1537, k2_zfmisc_1(B_1538, '#skF_6')) | ~r2_hidden(D_1536, A_1539) | ~r1_tarski(A_1539, k2_zfmisc_1(B_1540, '#skF_7')))), inference(resolution, [status(thm)], [c_10, c_5281])).
% 9.37/3.71  tff(c_5290, plain, (![D_1536, A_1539, B_1540, A_1537]: (D_1536!='#skF_3' | ~r2_hidden('#skF_1'(A_1539, B_1540, '#skF_7', D_1536), A_1537) | ~r1_tarski(A_1537, k2_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'), '#skF_6')) | ~r2_hidden(D_1536, A_1539) | ~r1_tarski(A_1539, k2_zfmisc_1(B_1540, '#skF_7')))), inference(resolution, [status(thm)], [c_6, c_5287])).
% 9.37/3.71  tff(c_5294, plain, (![D_1541, A_1542, B_1543, A_1544]: (D_1541!='#skF_3' | ~r2_hidden('#skF_1'(A_1542, B_1543, '#skF_7', D_1541), A_1544) | ~r1_tarski(A_1544, k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')) | ~r2_hidden(D_1541, A_1542) | ~r1_tarski(A_1542, k2_zfmisc_1(B_1543, '#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_5290])).
% 9.37/3.71  tff(c_5301, plain, (![D_1545, B_1546, A_1547]: (D_1545!='#skF_3' | ~r1_tarski(B_1546, k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')) | ~r2_hidden(D_1545, A_1547) | ~r1_tarski(A_1547, k2_zfmisc_1(B_1546, '#skF_7')))), inference(resolution, [status(thm)], [c_12, c_5294])).
% 9.37/3.71  tff(c_5304, plain, (![D_1545, A_1547]: (D_1545!='#skF_3' | ~r2_hidden(D_1545, A_1547) | ~r1_tarski(A_1547, k2_zfmisc_1(k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6'), '#skF_7')))), inference(resolution, [status(thm)], [c_6, c_5301])).
% 9.37/3.71  tff(c_5308, plain, (![D_1548, A_1549]: (D_1548!='#skF_3' | ~r2_hidden(D_1548, A_1549) | ~r1_tarski(A_1549, k4_zfmisc_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_5304])).
% 9.37/3.71  tff(c_5314, plain, (~r1_tarski(k4_zfmisc_1('#skF_4', '#skF_5', '#skF_6', '#skF_7'), k4_zfmisc_1('#skF_4', '#skF_5', '#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_24, c_5308])).
% 9.37/3.71  tff(c_5320, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_5314])).
% 9.37/3.71  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.37/3.71  
% 9.37/3.71  Inference rules
% 9.37/3.71  ----------------------
% 9.37/3.71  #Ref     : 0
% 9.37/3.71  #Sup     : 1797
% 9.37/3.71  #Fact    : 0
% 9.37/3.71  #Define  : 0
% 9.37/3.71  #Split   : 0
% 9.37/3.71  #Chain   : 0
% 9.37/3.71  #Close   : 0
% 9.37/3.71  
% 9.37/3.71  Ordering : KBO
% 9.37/3.71  
% 9.37/3.71  Simplification rules
% 9.37/3.71  ----------------------
% 9.37/3.71  #Subsume      : 126
% 9.37/3.71  #Demod        : 3216
% 9.37/3.71  #Tautology    : 169
% 9.37/3.71  #SimpNegUnit  : 0
% 9.37/3.71  #BackRed      : 0
% 9.37/3.71  
% 9.37/3.71  #Partial instantiations: 0
% 9.37/3.71  #Strategies tried      : 1
% 9.37/3.71  
% 9.37/3.71  Timing (in seconds)
% 9.37/3.71  ----------------------
% 9.52/3.71  Preprocessing        : 0.27
% 9.52/3.71  Parsing              : 0.15
% 9.52/3.71  CNF conversion       : 0.02
% 9.52/3.71  Main loop            : 2.68
% 9.52/3.71  Inferencing          : 0.56
% 9.52/3.71  Reduction            : 0.80
% 9.52/3.71  Demodulation         : 0.72
% 9.52/3.71  BG Simplification    : 0.09
% 9.52/3.71  Subsumption          : 1.16
% 9.52/3.71  Abstraction          : 0.13
% 9.52/3.71  MUC search           : 0.00
% 9.52/3.71  Cooper               : 0.00
% 9.52/3.71  Total                : 2.98
% 9.52/3.71  Index Insertion      : 0.00
% 9.52/3.71  Index Deletion       : 0.00
% 9.52/3.71  Index Matching       : 0.00
% 9.52/3.71  BG Taut test         : 0.00
%------------------------------------------------------------------------------
