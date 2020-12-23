%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:07 EST 2020

% Result     : Theorem 3.52s
% Output     : CNFRefutation 3.52s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 224 expanded)
%              Number of leaves         :   25 (  82 expanded)
%              Depth                    :   12
%              Number of atoms          :  125 ( 550 expanded)
%              Number of equality atoms :   80 ( 426 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_78,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & ~ ( B = k1_tarski(A)
              & C = k1_tarski(A) )
          & ~ ( B = k1_xboole_0
              & C = k1_tarski(A) )
          & ~ ( B = k1_tarski(A)
              & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_38,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

tff(c_50,plain,
    ( k1_xboole_0 != '#skF_7'
    | k1_tarski('#skF_5') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_59,plain,(
    k1_tarski('#skF_5') != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_26,plain,(
    ! [C_15] : r2_hidden(C_15,k1_tarski(C_15)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_52,plain,
    ( k1_tarski('#skF_5') != '#skF_7'
    | k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_71,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_56,plain,(
    k2_xboole_0('#skF_6','#skF_7') = k1_tarski('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_22,plain,(
    ! [A_9,B_10] : r1_tarski(A_9,k2_xboole_0(A_9,B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_75,plain,(
    r1_tarski('#skF_6',k1_tarski('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_22])).

tff(c_236,plain,(
    ! [B_59,A_60] :
      ( k1_tarski(B_59) = A_60
      | k1_xboole_0 = A_60
      | ~ r1_tarski(A_60,k1_tarski(B_59)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_242,plain,
    ( k1_tarski('#skF_5') = '#skF_6'
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_75,c_236])).

tff(c_253,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_71,c_59,c_242])).

tff(c_254,plain,(
    k1_tarski('#skF_5') != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_270,plain,(
    ! [B_62,A_63] : k2_xboole_0(B_62,A_63) = k2_xboole_0(A_63,B_62) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_309,plain,(
    ! [A_64,B_65] : r1_tarski(A_64,k2_xboole_0(B_65,A_64)) ),
    inference(superposition,[status(thm),theory(equality)],[c_270,c_22])).

tff(c_318,plain,(
    r1_tarski('#skF_7',k1_tarski('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_309])).

tff(c_255,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_42,plain,(
    ! [B_23,A_22] :
      ( k1_tarski(B_23) = A_22
      | k1_xboole_0 = A_22
      | ~ r1_tarski(A_22,k1_tarski(B_23)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_415,plain,(
    ! [B_84,A_85] :
      ( k1_tarski(B_84) = A_85
      | A_85 = '#skF_6'
      | ~ r1_tarski(A_85,k1_tarski(B_84)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_255,c_42])).

tff(c_418,plain,
    ( k1_tarski('#skF_5') = '#skF_7'
    | '#skF_7' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_318,c_415])).

tff(c_427,plain,(
    '#skF_7' = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_254,c_418])).

tff(c_435,plain,(
    k2_xboole_0('#skF_6','#skF_6') = k1_tarski('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_427,c_56])).

tff(c_473,plain,(
    ! [D_91,B_92,A_93] :
      ( r2_hidden(D_91,B_92)
      | r2_hidden(D_91,A_93)
      | ~ r2_hidden(D_91,k2_xboole_0(A_93,B_92)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_494,plain,(
    ! [D_94] :
      ( r2_hidden(D_94,'#skF_6')
      | r2_hidden(D_94,'#skF_6')
      | ~ r2_hidden(D_94,k1_tarski('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_435,c_473])).

tff(c_503,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_26,c_494])).

tff(c_1213,plain,(
    ! [A_1042,B_1043] :
      ( '#skF_3'(A_1042,B_1043) = A_1042
      | r2_hidden('#skF_4'(A_1042,B_1043),B_1043)
      | k1_tarski(A_1042) = B_1043 ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_395,plain,(
    ! [D_79,A_80,B_81] :
      ( ~ r2_hidden(D_79,A_80)
      | r2_hidden(D_79,k2_xboole_0(A_80,B_81)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_408,plain,(
    ! [D_82] :
      ( ~ r2_hidden(D_82,'#skF_6')
      | r2_hidden(D_82,k1_tarski('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_395])).

tff(c_24,plain,(
    ! [C_15,A_11] :
      ( C_15 = A_11
      | ~ r2_hidden(C_15,k1_tarski(A_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_412,plain,(
    ! [D_82] :
      ( D_82 = '#skF_5'
      | ~ r2_hidden(D_82,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_408,c_24])).

tff(c_1260,plain,(
    ! [A_1067] :
      ( '#skF_4'(A_1067,'#skF_6') = '#skF_5'
      | '#skF_3'(A_1067,'#skF_6') = A_1067
      | k1_tarski(A_1067) = '#skF_6' ) ),
    inference(resolution,[status(thm)],[c_1213,c_412])).

tff(c_1355,plain,
    ( '#skF_4'('#skF_5','#skF_6') = '#skF_5'
    | '#skF_3'('#skF_5','#skF_6') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_1260,c_59])).

tff(c_1360,plain,(
    '#skF_3'('#skF_5','#skF_6') = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_1355])).

tff(c_28,plain,(
    ! [A_11,B_12] :
      ( ~ r2_hidden('#skF_3'(A_11,B_12),B_12)
      | '#skF_4'(A_11,B_12) != A_11
      | k1_tarski(A_11) = B_12 ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1364,plain,
    ( ~ r2_hidden('#skF_5','#skF_6')
    | '#skF_4'('#skF_5','#skF_6') != '#skF_5'
    | k1_tarski('#skF_5') = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_1360,c_28])).

tff(c_1382,plain,
    ( '#skF_4'('#skF_5','#skF_6') != '#skF_5'
    | k1_tarski('#skF_5') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_503,c_1364])).

tff(c_1383,plain,(
    '#skF_4'('#skF_5','#skF_6') != '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_59,c_1382])).

tff(c_1503,plain,(
    ! [A_1209,B_1210] :
      ( ~ r2_hidden('#skF_3'(A_1209,B_1210),B_1210)
      | r2_hidden('#skF_4'(A_1209,B_1210),B_1210)
      | k1_tarski(A_1209) = B_1210 ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1513,plain,
    ( ~ r2_hidden('#skF_5','#skF_6')
    | r2_hidden('#skF_4'('#skF_5','#skF_6'),'#skF_6')
    | k1_tarski('#skF_5') = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_1360,c_1503])).

tff(c_1564,plain,
    ( r2_hidden('#skF_4'('#skF_5','#skF_6'),'#skF_6')
    | k1_tarski('#skF_5') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_503,c_1513])).

tff(c_1565,plain,(
    r2_hidden('#skF_4'('#skF_5','#skF_6'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_59,c_1564])).

tff(c_1574,plain,(
    '#skF_4'('#skF_5','#skF_6') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_1565,c_412])).

tff(c_1578,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1383,c_1574])).

tff(c_1579,plain,(
    '#skF_4'('#skF_5','#skF_6') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_1355])).

tff(c_506,plain,(
    ! [A_95,B_96] :
      ( '#skF_3'(A_95,B_96) = A_95
      | '#skF_4'(A_95,B_96) != A_95
      | k1_tarski(A_95) = B_96 ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_904,plain,(
    ! [B_96] :
      ( B_96 != '#skF_6'
      | '#skF_3'('#skF_5',B_96) = '#skF_5'
      | '#skF_4'('#skF_5',B_96) != '#skF_5' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_506,c_59])).

tff(c_1580,plain,(
    '#skF_3'('#skF_5','#skF_6') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_1355])).

tff(c_1595,plain,(
    '#skF_4'('#skF_5','#skF_6') != '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_904,c_1580])).

tff(c_1604,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1579,c_1595])).

tff(c_1605,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_1606,plain,(
    k1_tarski('#skF_5') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_54,plain,
    ( k1_tarski('#skF_5') != '#skF_7'
    | k1_tarski('#skF_5') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1699,plain,(
    '#skF_7' != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1606,c_1606,c_54])).

tff(c_1636,plain,(
    k2_xboole_0('#skF_6','#skF_7') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1606,c_56])).

tff(c_1646,plain,(
    ! [B_1307,A_1308] : k2_xboole_0(B_1307,A_1308) = k2_xboole_0(A_1308,B_1307) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_1685,plain,(
    ! [A_1309,B_1310] : r1_tarski(A_1309,k2_xboole_0(B_1310,A_1309)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1646,c_22])).

tff(c_1694,plain,(
    r1_tarski('#skF_7','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_1636,c_1685])).

tff(c_1831,plain,(
    ! [B_1333,A_1334] :
      ( k1_tarski(B_1333) = A_1334
      | k1_xboole_0 = A_1334
      | ~ r1_tarski(A_1334,k1_tarski(B_1333)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1837,plain,(
    ! [A_1334] :
      ( k1_tarski('#skF_5') = A_1334
      | k1_xboole_0 = A_1334
      | ~ r1_tarski(A_1334,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1606,c_1831])).

tff(c_1870,plain,(
    ! [A_1338] :
      ( A_1338 = '#skF_6'
      | k1_xboole_0 = A_1338
      | ~ r1_tarski(A_1338,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1606,c_1837])).

tff(c_1873,plain,
    ( '#skF_7' = '#skF_6'
    | k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_1694,c_1870])).

tff(c_1883,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1605,c_1699,c_1873])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.20/0.35  % CPULimit   : 60
% 0.20/0.35  % DateTime   : Tue Dec  1 20:22:51 EST 2020
% 0.20/0.35  % CPUTime    : 
% 0.20/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.52/1.65  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.52/1.66  
% 3.52/1.66  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.52/1.66  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 3.52/1.66  
% 3.52/1.66  %Foreground sorts:
% 3.52/1.66  
% 3.52/1.66  
% 3.52/1.66  %Background operators:
% 3.52/1.66  
% 3.52/1.66  
% 3.52/1.66  %Foreground operators:
% 3.52/1.66  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.52/1.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.52/1.66  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.52/1.66  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.52/1.66  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.52/1.66  tff('#skF_7', type, '#skF_7': $i).
% 3.52/1.66  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.52/1.66  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.52/1.66  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.52/1.66  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.52/1.66  tff('#skF_5', type, '#skF_5': $i).
% 3.52/1.66  tff('#skF_6', type, '#skF_6': $i).
% 3.52/1.66  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.52/1.66  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.52/1.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.52/1.66  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.52/1.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.52/1.66  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.52/1.66  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.52/1.66  
% 3.52/1.67  tff(f_78, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 3.52/1.67  tff(f_45, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 3.52/1.67  tff(f_38, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.52/1.67  tff(f_57, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 3.52/1.67  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.52/1.67  tff(f_36, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 3.52/1.67  tff(c_50, plain, (k1_xboole_0!='#skF_7' | k1_tarski('#skF_5')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.52/1.67  tff(c_59, plain, (k1_tarski('#skF_5')!='#skF_6'), inference(splitLeft, [status(thm)], [c_50])).
% 3.52/1.67  tff(c_26, plain, (![C_15]: (r2_hidden(C_15, k1_tarski(C_15)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.52/1.67  tff(c_52, plain, (k1_tarski('#skF_5')!='#skF_7' | k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.52/1.67  tff(c_71, plain, (k1_xboole_0!='#skF_6'), inference(splitLeft, [status(thm)], [c_52])).
% 3.52/1.67  tff(c_56, plain, (k2_xboole_0('#skF_6', '#skF_7')=k1_tarski('#skF_5')), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.52/1.67  tff(c_22, plain, (![A_9, B_10]: (r1_tarski(A_9, k2_xboole_0(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.52/1.67  tff(c_75, plain, (r1_tarski('#skF_6', k1_tarski('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_56, c_22])).
% 3.52/1.67  tff(c_236, plain, (![B_59, A_60]: (k1_tarski(B_59)=A_60 | k1_xboole_0=A_60 | ~r1_tarski(A_60, k1_tarski(B_59)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.52/1.67  tff(c_242, plain, (k1_tarski('#skF_5')='#skF_6' | k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_75, c_236])).
% 3.52/1.67  tff(c_253, plain, $false, inference(negUnitSimplification, [status(thm)], [c_71, c_59, c_242])).
% 3.52/1.67  tff(c_254, plain, (k1_tarski('#skF_5')!='#skF_7'), inference(splitRight, [status(thm)], [c_52])).
% 3.52/1.67  tff(c_270, plain, (![B_62, A_63]: (k2_xboole_0(B_62, A_63)=k2_xboole_0(A_63, B_62))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.52/1.67  tff(c_309, plain, (![A_64, B_65]: (r1_tarski(A_64, k2_xboole_0(B_65, A_64)))), inference(superposition, [status(thm), theory('equality')], [c_270, c_22])).
% 3.52/1.67  tff(c_318, plain, (r1_tarski('#skF_7', k1_tarski('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_56, c_309])).
% 3.52/1.67  tff(c_255, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_52])).
% 3.52/1.67  tff(c_42, plain, (![B_23, A_22]: (k1_tarski(B_23)=A_22 | k1_xboole_0=A_22 | ~r1_tarski(A_22, k1_tarski(B_23)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.52/1.67  tff(c_415, plain, (![B_84, A_85]: (k1_tarski(B_84)=A_85 | A_85='#skF_6' | ~r1_tarski(A_85, k1_tarski(B_84)))), inference(demodulation, [status(thm), theory('equality')], [c_255, c_42])).
% 3.52/1.67  tff(c_418, plain, (k1_tarski('#skF_5')='#skF_7' | '#skF_7'='#skF_6'), inference(resolution, [status(thm)], [c_318, c_415])).
% 3.52/1.67  tff(c_427, plain, ('#skF_7'='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_254, c_418])).
% 3.52/1.67  tff(c_435, plain, (k2_xboole_0('#skF_6', '#skF_6')=k1_tarski('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_427, c_56])).
% 3.52/1.67  tff(c_473, plain, (![D_91, B_92, A_93]: (r2_hidden(D_91, B_92) | r2_hidden(D_91, A_93) | ~r2_hidden(D_91, k2_xboole_0(A_93, B_92)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.52/1.67  tff(c_494, plain, (![D_94]: (r2_hidden(D_94, '#skF_6') | r2_hidden(D_94, '#skF_6') | ~r2_hidden(D_94, k1_tarski('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_435, c_473])).
% 3.52/1.67  tff(c_503, plain, (r2_hidden('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_26, c_494])).
% 3.52/1.67  tff(c_1213, plain, (![A_1042, B_1043]: ('#skF_3'(A_1042, B_1043)=A_1042 | r2_hidden('#skF_4'(A_1042, B_1043), B_1043) | k1_tarski(A_1042)=B_1043)), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.52/1.67  tff(c_395, plain, (![D_79, A_80, B_81]: (~r2_hidden(D_79, A_80) | r2_hidden(D_79, k2_xboole_0(A_80, B_81)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.52/1.67  tff(c_408, plain, (![D_82]: (~r2_hidden(D_82, '#skF_6') | r2_hidden(D_82, k1_tarski('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_56, c_395])).
% 3.52/1.67  tff(c_24, plain, (![C_15, A_11]: (C_15=A_11 | ~r2_hidden(C_15, k1_tarski(A_11)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.52/1.67  tff(c_412, plain, (![D_82]: (D_82='#skF_5' | ~r2_hidden(D_82, '#skF_6'))), inference(resolution, [status(thm)], [c_408, c_24])).
% 3.52/1.67  tff(c_1260, plain, (![A_1067]: ('#skF_4'(A_1067, '#skF_6')='#skF_5' | '#skF_3'(A_1067, '#skF_6')=A_1067 | k1_tarski(A_1067)='#skF_6')), inference(resolution, [status(thm)], [c_1213, c_412])).
% 3.52/1.67  tff(c_1355, plain, ('#skF_4'('#skF_5', '#skF_6')='#skF_5' | '#skF_3'('#skF_5', '#skF_6')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_1260, c_59])).
% 3.52/1.67  tff(c_1360, plain, ('#skF_3'('#skF_5', '#skF_6')='#skF_5'), inference(splitLeft, [status(thm)], [c_1355])).
% 3.52/1.67  tff(c_28, plain, (![A_11, B_12]: (~r2_hidden('#skF_3'(A_11, B_12), B_12) | '#skF_4'(A_11, B_12)!=A_11 | k1_tarski(A_11)=B_12)), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.52/1.67  tff(c_1364, plain, (~r2_hidden('#skF_5', '#skF_6') | '#skF_4'('#skF_5', '#skF_6')!='#skF_5' | k1_tarski('#skF_5')='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_1360, c_28])).
% 3.52/1.67  tff(c_1382, plain, ('#skF_4'('#skF_5', '#skF_6')!='#skF_5' | k1_tarski('#skF_5')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_503, c_1364])).
% 3.52/1.67  tff(c_1383, plain, ('#skF_4'('#skF_5', '#skF_6')!='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_59, c_1382])).
% 3.52/1.67  tff(c_1503, plain, (![A_1209, B_1210]: (~r2_hidden('#skF_3'(A_1209, B_1210), B_1210) | r2_hidden('#skF_4'(A_1209, B_1210), B_1210) | k1_tarski(A_1209)=B_1210)), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.52/1.67  tff(c_1513, plain, (~r2_hidden('#skF_5', '#skF_6') | r2_hidden('#skF_4'('#skF_5', '#skF_6'), '#skF_6') | k1_tarski('#skF_5')='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_1360, c_1503])).
% 3.52/1.67  tff(c_1564, plain, (r2_hidden('#skF_4'('#skF_5', '#skF_6'), '#skF_6') | k1_tarski('#skF_5')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_503, c_1513])).
% 3.52/1.67  tff(c_1565, plain, (r2_hidden('#skF_4'('#skF_5', '#skF_6'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_59, c_1564])).
% 3.52/1.67  tff(c_1574, plain, ('#skF_4'('#skF_5', '#skF_6')='#skF_5'), inference(resolution, [status(thm)], [c_1565, c_412])).
% 3.52/1.67  tff(c_1578, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1383, c_1574])).
% 3.52/1.67  tff(c_1579, plain, ('#skF_4'('#skF_5', '#skF_6')='#skF_5'), inference(splitRight, [status(thm)], [c_1355])).
% 3.52/1.67  tff(c_506, plain, (![A_95, B_96]: ('#skF_3'(A_95, B_96)=A_95 | '#skF_4'(A_95, B_96)!=A_95 | k1_tarski(A_95)=B_96)), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.52/1.67  tff(c_904, plain, (![B_96]: (B_96!='#skF_6' | '#skF_3'('#skF_5', B_96)='#skF_5' | '#skF_4'('#skF_5', B_96)!='#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_506, c_59])).
% 3.52/1.67  tff(c_1580, plain, ('#skF_3'('#skF_5', '#skF_6')!='#skF_5'), inference(splitRight, [status(thm)], [c_1355])).
% 3.52/1.67  tff(c_1595, plain, ('#skF_4'('#skF_5', '#skF_6')!='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_904, c_1580])).
% 3.52/1.67  tff(c_1604, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1579, c_1595])).
% 3.52/1.67  tff(c_1605, plain, (k1_xboole_0!='#skF_7'), inference(splitRight, [status(thm)], [c_50])).
% 3.52/1.67  tff(c_1606, plain, (k1_tarski('#skF_5')='#skF_6'), inference(splitRight, [status(thm)], [c_50])).
% 3.52/1.67  tff(c_54, plain, (k1_tarski('#skF_5')!='#skF_7' | k1_tarski('#skF_5')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.52/1.67  tff(c_1699, plain, ('#skF_7'!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_1606, c_1606, c_54])).
% 3.52/1.67  tff(c_1636, plain, (k2_xboole_0('#skF_6', '#skF_7')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_1606, c_56])).
% 3.52/1.67  tff(c_1646, plain, (![B_1307, A_1308]: (k2_xboole_0(B_1307, A_1308)=k2_xboole_0(A_1308, B_1307))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.52/1.67  tff(c_1685, plain, (![A_1309, B_1310]: (r1_tarski(A_1309, k2_xboole_0(B_1310, A_1309)))), inference(superposition, [status(thm), theory('equality')], [c_1646, c_22])).
% 3.52/1.67  tff(c_1694, plain, (r1_tarski('#skF_7', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_1636, c_1685])).
% 3.52/1.67  tff(c_1831, plain, (![B_1333, A_1334]: (k1_tarski(B_1333)=A_1334 | k1_xboole_0=A_1334 | ~r1_tarski(A_1334, k1_tarski(B_1333)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.52/1.67  tff(c_1837, plain, (![A_1334]: (k1_tarski('#skF_5')=A_1334 | k1_xboole_0=A_1334 | ~r1_tarski(A_1334, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_1606, c_1831])).
% 3.52/1.67  tff(c_1870, plain, (![A_1338]: (A_1338='#skF_6' | k1_xboole_0=A_1338 | ~r1_tarski(A_1338, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_1606, c_1837])).
% 3.52/1.67  tff(c_1873, plain, ('#skF_7'='#skF_6' | k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_1694, c_1870])).
% 3.52/1.67  tff(c_1883, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1605, c_1699, c_1873])).
% 3.52/1.67  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.52/1.67  
% 3.52/1.67  Inference rules
% 3.52/1.67  ----------------------
% 3.52/1.67  #Ref     : 0
% 3.52/1.67  #Sup     : 330
% 3.52/1.67  #Fact    : 0
% 3.52/1.67  #Define  : 0
% 3.52/1.67  #Split   : 7
% 3.52/1.67  #Chain   : 0
% 3.52/1.67  #Close   : 0
% 3.52/1.67  
% 3.52/1.67  Ordering : KBO
% 3.52/1.67  
% 3.52/1.67  Simplification rules
% 3.52/1.67  ----------------------
% 3.52/1.67  #Subsume      : 48
% 3.52/1.67  #Demod        : 125
% 3.52/1.67  #Tautology    : 157
% 3.52/1.67  #SimpNegUnit  : 11
% 3.52/1.67  #BackRed      : 6
% 3.52/1.67  
% 3.52/1.67  #Partial instantiations: 700
% 3.52/1.67  #Strategies tried      : 1
% 3.52/1.67  
% 3.52/1.67  Timing (in seconds)
% 3.52/1.67  ----------------------
% 3.52/1.68  Preprocessing        : 0.34
% 3.52/1.68  Parsing              : 0.17
% 3.52/1.68  CNF conversion       : 0.03
% 3.52/1.68  Main loop            : 0.48
% 3.52/1.68  Inferencing          : 0.21
% 3.52/1.68  Reduction            : 0.14
% 3.52/1.68  Demodulation         : 0.10
% 3.52/1.68  BG Simplification    : 0.03
% 3.52/1.68  Subsumption          : 0.08
% 3.52/1.68  Abstraction          : 0.02
% 3.52/1.68  MUC search           : 0.00
% 3.52/1.68  Cooper               : 0.00
% 3.52/1.68  Total                : 0.86
% 3.52/1.68  Index Insertion      : 0.00
% 3.52/1.68  Index Deletion       : 0.00
% 3.52/1.68  Index Matching       : 0.00
% 3.52/1.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
