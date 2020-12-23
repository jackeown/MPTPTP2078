%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:07 EST 2020

% Result     : Theorem 4.89s
% Output     : CNFRefutation 4.89s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 160 expanded)
%              Number of leaves         :   27 (  66 expanded)
%              Depth                    :    7
%              Number of atoms          :  103 ( 334 expanded)
%              Number of equality atoms :   34 ( 134 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_4

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

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_87,negated_conjecture,(
    ~ ! [A,B,C,D,E] :
        ( r2_hidden(A,k2_zfmisc_1(k2_tarski(B,C),k2_tarski(D,E)))
       => ( ( k1_mcart_1(A) = B
            | k1_mcart_1(A) = C )
          & ( k2_mcart_1(A) = D
            | k2_mcart_1(A) = E ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_mcart_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ~ ( ~ r2_hidden(A,C)
        & ~ r2_hidden(B,C)
        & C != k4_xboole_0(C,k2_tarski(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(c_60,plain,
    ( k1_mcart_1('#skF_5') != '#skF_6'
    | k2_mcart_1('#skF_5') != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_84,plain,(
    k2_mcart_1('#skF_5') != '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_62,plain,
    ( k1_mcart_1('#skF_5') != '#skF_7'
    | k2_mcart_1('#skF_5') != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_77,plain,(
    k2_mcart_1('#skF_5') != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_28,plain,(
    ! [C_13] : r2_hidden(C_13,k1_tarski(C_13)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_56,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k2_tarski('#skF_6','#skF_7'),k2_tarski('#skF_8','#skF_9'))) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_142,plain,(
    ! [A_59,C_60,B_61] :
      ( r2_hidden(k2_mcart_1(A_59),C_60)
      | ~ r2_hidden(A_59,k2_zfmisc_1(B_61,C_60)) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_145,plain,(
    r2_hidden(k2_mcart_1('#skF_5'),k2_tarski('#skF_8','#skF_9')) ),
    inference(resolution,[status(thm)],[c_56,c_142])).

tff(c_543,plain,(
    ! [C_981,A_982,B_983] :
      ( k4_xboole_0(C_981,k2_tarski(A_982,B_983)) = C_981
      | r2_hidden(B_983,C_981)
      | r2_hidden(A_982,C_981) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( ~ r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1072,plain,(
    ! [D_1265,A_1266,B_1267,C_1268] :
      ( ~ r2_hidden(D_1265,k2_tarski(A_1266,B_1267))
      | ~ r2_hidden(D_1265,C_1268)
      | r2_hidden(B_1267,C_1268)
      | r2_hidden(A_1266,C_1268) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_543,c_4])).

tff(c_1092,plain,(
    ! [C_1295] :
      ( ~ r2_hidden(k2_mcart_1('#skF_5'),C_1295)
      | r2_hidden('#skF_9',C_1295)
      | r2_hidden('#skF_8',C_1295) ) ),
    inference(resolution,[status(thm)],[c_145,c_1072])).

tff(c_1143,plain,
    ( r2_hidden('#skF_9',k1_tarski(k2_mcart_1('#skF_5')))
    | r2_hidden('#skF_8',k1_tarski(k2_mcart_1('#skF_5'))) ),
    inference(resolution,[status(thm)],[c_28,c_1092])).

tff(c_1224,plain,(
    r2_hidden('#skF_8',k1_tarski(k2_mcart_1('#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_1143])).

tff(c_26,plain,(
    ! [C_13,A_9] :
      ( C_13 = A_9
      | ~ r2_hidden(C_13,k1_tarski(A_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_1233,plain,(
    k2_mcart_1('#skF_5') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_1224,c_26])).

tff(c_1291,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_77,c_1233])).

tff(c_1292,plain,(
    r2_hidden('#skF_9',k1_tarski(k2_mcart_1('#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_1143])).

tff(c_1302,plain,(
    k2_mcart_1('#skF_5') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_1292,c_26])).

tff(c_1360,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_1302])).

tff(c_1362,plain,(
    k2_mcart_1('#skF_5') = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_58,plain,
    ( k1_mcart_1('#skF_5') != '#skF_7'
    | k2_mcart_1('#skF_5') != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1369,plain,(
    k1_mcart_1('#skF_5') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1362,c_58])).

tff(c_1361,plain,(
    k1_mcart_1('#skF_5') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_1438,plain,(
    ! [A_1456,B_1457,C_1458] :
      ( r2_hidden(k1_mcart_1(A_1456),B_1457)
      | ~ r2_hidden(A_1456,k2_zfmisc_1(B_1457,C_1458)) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1441,plain,(
    r2_hidden(k1_mcart_1('#skF_5'),k2_tarski('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_56,c_1438])).

tff(c_1817,plain,(
    ! [C_2362,A_2363,B_2364] :
      ( k4_xboole_0(C_2362,k2_tarski(A_2363,B_2364)) = C_2362
      | r2_hidden(B_2364,C_2362)
      | r2_hidden(A_2363,C_2362) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_2392,plain,(
    ! [D_2646,A_2647,B_2648,C_2649] :
      ( ~ r2_hidden(D_2646,k2_tarski(A_2647,B_2648))
      | ~ r2_hidden(D_2646,C_2649)
      | r2_hidden(B_2648,C_2649)
      | r2_hidden(A_2647,C_2649) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1817,c_4])).

tff(c_2494,plain,(
    ! [C_2733] :
      ( ~ r2_hidden(k1_mcart_1('#skF_5'),C_2733)
      | r2_hidden('#skF_7',C_2733)
      | r2_hidden('#skF_6',C_2733) ) ),
    inference(resolution,[status(thm)],[c_1441,c_2392])).

tff(c_2544,plain,
    ( r2_hidden('#skF_7',k1_tarski(k1_mcart_1('#skF_5')))
    | r2_hidden('#skF_6',k1_tarski(k1_mcart_1('#skF_5'))) ),
    inference(resolution,[status(thm)],[c_28,c_2494])).

tff(c_2545,plain,(
    r2_hidden('#skF_6',k1_tarski(k1_mcart_1('#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_2544])).

tff(c_2583,plain,(
    k1_mcart_1('#skF_5') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_2545,c_26])).

tff(c_2640,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1361,c_2583])).

tff(c_2641,plain,(
    r2_hidden('#skF_7',k1_tarski(k1_mcart_1('#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_2544])).

tff(c_2651,plain,(
    k1_mcart_1('#skF_5') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_2641,c_26])).

tff(c_2708,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1369,c_2651])).

tff(c_2709,plain,(
    k1_mcart_1('#skF_5') != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_2710,plain,(
    k2_mcart_1('#skF_5') = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_64,plain,
    ( k1_mcart_1('#skF_5') != '#skF_6'
    | k2_mcart_1('#skF_5') != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_2724,plain,(
    k1_mcart_1('#skF_5') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2710,c_64])).

tff(c_2779,plain,(
    ! [A_2863,B_2864,C_2865] :
      ( r2_hidden(k1_mcart_1(A_2863),B_2864)
      | ~ r2_hidden(A_2863,k2_zfmisc_1(B_2864,C_2865)) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_2782,plain,(
    r2_hidden(k1_mcart_1('#skF_5'),k2_tarski('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_56,c_2779])).

tff(c_3224,plain,(
    ! [C_3803,A_3804,B_3805] :
      ( k4_xboole_0(C_3803,k2_tarski(A_3804,B_3805)) = C_3803
      | r2_hidden(B_3805,C_3803)
      | r2_hidden(A_3804,C_3803) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_3572,plain,(
    ! [D_4031,A_4032,B_4033,C_4034] :
      ( ~ r2_hidden(D_4031,k2_tarski(A_4032,B_4033))
      | ~ r2_hidden(D_4031,C_4034)
      | r2_hidden(B_4033,C_4034)
      | r2_hidden(A_4032,C_4034) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3224,c_4])).

tff(c_3589,plain,(
    ! [C_4061] :
      ( ~ r2_hidden(k1_mcart_1('#skF_5'),C_4061)
      | r2_hidden('#skF_7',C_4061)
      | r2_hidden('#skF_6',C_4061) ) ),
    inference(resolution,[status(thm)],[c_2782,c_3572])).

tff(c_3639,plain,
    ( r2_hidden('#skF_7',k1_tarski(k1_mcart_1('#skF_5')))
    | r2_hidden('#skF_6',k1_tarski(k1_mcart_1('#skF_5'))) ),
    inference(resolution,[status(thm)],[c_28,c_3589])).

tff(c_3764,plain,(
    r2_hidden('#skF_6',k1_tarski(k1_mcart_1('#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_3639])).

tff(c_3773,plain,(
    k1_mcart_1('#skF_5') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_3764,c_26])).

tff(c_3830,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2724,c_3773])).

tff(c_3831,plain,(
    r2_hidden('#skF_7',k1_tarski(k1_mcart_1('#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_3639])).

tff(c_3870,plain,(
    k1_mcart_1('#skF_5') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_3831,c_26])).

tff(c_3927,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2709,c_3870])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:07:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.89/1.93  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.89/1.95  
% 4.89/1.95  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.89/1.95  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_4
% 4.89/1.95  
% 4.89/1.95  %Foreground sorts:
% 4.89/1.95  
% 4.89/1.95  
% 4.89/1.95  %Background operators:
% 4.89/1.95  
% 4.89/1.95  
% 4.89/1.95  %Foreground operators:
% 4.89/1.95  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.89/1.95  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.89/1.95  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.89/1.95  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.89/1.95  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.89/1.95  tff('#skF_7', type, '#skF_7': $i).
% 4.89/1.95  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.89/1.95  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.89/1.95  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.89/1.95  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.89/1.95  tff('#skF_5', type, '#skF_5': $i).
% 4.89/1.95  tff('#skF_6', type, '#skF_6': $i).
% 4.89/1.95  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.89/1.95  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.89/1.95  tff('#skF_9', type, '#skF_9': $i).
% 4.89/1.95  tff('#skF_8', type, '#skF_8': $i).
% 4.89/1.95  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.89/1.95  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 4.89/1.95  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.89/1.95  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.89/1.95  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 4.89/1.95  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 4.89/1.95  
% 4.89/1.96  tff(f_87, negated_conjecture, ~(![A, B, C, D, E]: (r2_hidden(A, k2_zfmisc_1(k2_tarski(B, C), k2_tarski(D, E))) => (((k1_mcart_1(A) = B) | (k1_mcart_1(A) = C)) & ((k2_mcart_1(A) = D) | (k2_mcart_1(A) = E))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_mcart_1)).
% 4.89/1.96  tff(f_48, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 4.89/1.96  tff(f_76, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 4.89/1.96  tff(f_64, axiom, (![A, B, C]: ~((~r2_hidden(A, C) & ~r2_hidden(B, C)) & ~(C = k4_xboole_0(C, k2_tarski(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t144_zfmisc_1)).
% 4.89/1.96  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 4.89/1.96  tff(c_60, plain, (k1_mcart_1('#skF_5')!='#skF_6' | k2_mcart_1('#skF_5')!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.89/1.96  tff(c_84, plain, (k2_mcart_1('#skF_5')!='#skF_9'), inference(splitLeft, [status(thm)], [c_60])).
% 4.89/1.96  tff(c_62, plain, (k1_mcart_1('#skF_5')!='#skF_7' | k2_mcart_1('#skF_5')!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.89/1.96  tff(c_77, plain, (k2_mcart_1('#skF_5')!='#skF_8'), inference(splitLeft, [status(thm)], [c_62])).
% 4.89/1.96  tff(c_28, plain, (![C_13]: (r2_hidden(C_13, k1_tarski(C_13)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.89/1.96  tff(c_56, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k2_tarski('#skF_6', '#skF_7'), k2_tarski('#skF_8', '#skF_9')))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.89/1.96  tff(c_142, plain, (![A_59, C_60, B_61]: (r2_hidden(k2_mcart_1(A_59), C_60) | ~r2_hidden(A_59, k2_zfmisc_1(B_61, C_60)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.89/1.96  tff(c_145, plain, (r2_hidden(k2_mcart_1('#skF_5'), k2_tarski('#skF_8', '#skF_9'))), inference(resolution, [status(thm)], [c_56, c_142])).
% 4.89/1.96  tff(c_543, plain, (![C_981, A_982, B_983]: (k4_xboole_0(C_981, k2_tarski(A_982, B_983))=C_981 | r2_hidden(B_983, C_981) | r2_hidden(A_982, C_981))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.89/1.96  tff(c_4, plain, (![D_6, B_2, A_1]: (~r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.89/1.96  tff(c_1072, plain, (![D_1265, A_1266, B_1267, C_1268]: (~r2_hidden(D_1265, k2_tarski(A_1266, B_1267)) | ~r2_hidden(D_1265, C_1268) | r2_hidden(B_1267, C_1268) | r2_hidden(A_1266, C_1268))), inference(superposition, [status(thm), theory('equality')], [c_543, c_4])).
% 4.89/1.96  tff(c_1092, plain, (![C_1295]: (~r2_hidden(k2_mcart_1('#skF_5'), C_1295) | r2_hidden('#skF_9', C_1295) | r2_hidden('#skF_8', C_1295))), inference(resolution, [status(thm)], [c_145, c_1072])).
% 4.89/1.96  tff(c_1143, plain, (r2_hidden('#skF_9', k1_tarski(k2_mcart_1('#skF_5'))) | r2_hidden('#skF_8', k1_tarski(k2_mcart_1('#skF_5')))), inference(resolution, [status(thm)], [c_28, c_1092])).
% 4.89/1.96  tff(c_1224, plain, (r2_hidden('#skF_8', k1_tarski(k2_mcart_1('#skF_5')))), inference(splitLeft, [status(thm)], [c_1143])).
% 4.89/1.96  tff(c_26, plain, (![C_13, A_9]: (C_13=A_9 | ~r2_hidden(C_13, k1_tarski(A_9)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.89/1.96  tff(c_1233, plain, (k2_mcart_1('#skF_5')='#skF_8'), inference(resolution, [status(thm)], [c_1224, c_26])).
% 4.89/1.96  tff(c_1291, plain, $false, inference(negUnitSimplification, [status(thm)], [c_77, c_1233])).
% 4.89/1.96  tff(c_1292, plain, (r2_hidden('#skF_9', k1_tarski(k2_mcart_1('#skF_5')))), inference(splitRight, [status(thm)], [c_1143])).
% 4.89/1.96  tff(c_1302, plain, (k2_mcart_1('#skF_5')='#skF_9'), inference(resolution, [status(thm)], [c_1292, c_26])).
% 4.89/1.96  tff(c_1360, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84, c_1302])).
% 4.89/1.96  tff(c_1362, plain, (k2_mcart_1('#skF_5')='#skF_9'), inference(splitRight, [status(thm)], [c_60])).
% 4.89/1.96  tff(c_58, plain, (k1_mcart_1('#skF_5')!='#skF_7' | k2_mcart_1('#skF_5')!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.89/1.96  tff(c_1369, plain, (k1_mcart_1('#skF_5')!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_1362, c_58])).
% 4.89/1.96  tff(c_1361, plain, (k1_mcart_1('#skF_5')!='#skF_6'), inference(splitRight, [status(thm)], [c_60])).
% 4.89/1.96  tff(c_1438, plain, (![A_1456, B_1457, C_1458]: (r2_hidden(k1_mcart_1(A_1456), B_1457) | ~r2_hidden(A_1456, k2_zfmisc_1(B_1457, C_1458)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.89/1.96  tff(c_1441, plain, (r2_hidden(k1_mcart_1('#skF_5'), k2_tarski('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_56, c_1438])).
% 4.89/1.96  tff(c_1817, plain, (![C_2362, A_2363, B_2364]: (k4_xboole_0(C_2362, k2_tarski(A_2363, B_2364))=C_2362 | r2_hidden(B_2364, C_2362) | r2_hidden(A_2363, C_2362))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.89/1.96  tff(c_2392, plain, (![D_2646, A_2647, B_2648, C_2649]: (~r2_hidden(D_2646, k2_tarski(A_2647, B_2648)) | ~r2_hidden(D_2646, C_2649) | r2_hidden(B_2648, C_2649) | r2_hidden(A_2647, C_2649))), inference(superposition, [status(thm), theory('equality')], [c_1817, c_4])).
% 4.89/1.96  tff(c_2494, plain, (![C_2733]: (~r2_hidden(k1_mcart_1('#skF_5'), C_2733) | r2_hidden('#skF_7', C_2733) | r2_hidden('#skF_6', C_2733))), inference(resolution, [status(thm)], [c_1441, c_2392])).
% 4.89/1.96  tff(c_2544, plain, (r2_hidden('#skF_7', k1_tarski(k1_mcart_1('#skF_5'))) | r2_hidden('#skF_6', k1_tarski(k1_mcart_1('#skF_5')))), inference(resolution, [status(thm)], [c_28, c_2494])).
% 4.89/1.96  tff(c_2545, plain, (r2_hidden('#skF_6', k1_tarski(k1_mcart_1('#skF_5')))), inference(splitLeft, [status(thm)], [c_2544])).
% 4.89/1.96  tff(c_2583, plain, (k1_mcart_1('#skF_5')='#skF_6'), inference(resolution, [status(thm)], [c_2545, c_26])).
% 4.89/1.96  tff(c_2640, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1361, c_2583])).
% 4.89/1.96  tff(c_2641, plain, (r2_hidden('#skF_7', k1_tarski(k1_mcart_1('#skF_5')))), inference(splitRight, [status(thm)], [c_2544])).
% 4.89/1.96  tff(c_2651, plain, (k1_mcart_1('#skF_5')='#skF_7'), inference(resolution, [status(thm)], [c_2641, c_26])).
% 4.89/1.96  tff(c_2708, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1369, c_2651])).
% 4.89/1.96  tff(c_2709, plain, (k1_mcart_1('#skF_5')!='#skF_7'), inference(splitRight, [status(thm)], [c_62])).
% 4.89/1.96  tff(c_2710, plain, (k2_mcart_1('#skF_5')='#skF_8'), inference(splitRight, [status(thm)], [c_62])).
% 4.89/1.96  tff(c_64, plain, (k1_mcart_1('#skF_5')!='#skF_6' | k2_mcart_1('#skF_5')!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.89/1.96  tff(c_2724, plain, (k1_mcart_1('#skF_5')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_2710, c_64])).
% 4.89/1.96  tff(c_2779, plain, (![A_2863, B_2864, C_2865]: (r2_hidden(k1_mcart_1(A_2863), B_2864) | ~r2_hidden(A_2863, k2_zfmisc_1(B_2864, C_2865)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.89/1.96  tff(c_2782, plain, (r2_hidden(k1_mcart_1('#skF_5'), k2_tarski('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_56, c_2779])).
% 4.89/1.96  tff(c_3224, plain, (![C_3803, A_3804, B_3805]: (k4_xboole_0(C_3803, k2_tarski(A_3804, B_3805))=C_3803 | r2_hidden(B_3805, C_3803) | r2_hidden(A_3804, C_3803))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.89/1.96  tff(c_3572, plain, (![D_4031, A_4032, B_4033, C_4034]: (~r2_hidden(D_4031, k2_tarski(A_4032, B_4033)) | ~r2_hidden(D_4031, C_4034) | r2_hidden(B_4033, C_4034) | r2_hidden(A_4032, C_4034))), inference(superposition, [status(thm), theory('equality')], [c_3224, c_4])).
% 4.89/1.96  tff(c_3589, plain, (![C_4061]: (~r2_hidden(k1_mcart_1('#skF_5'), C_4061) | r2_hidden('#skF_7', C_4061) | r2_hidden('#skF_6', C_4061))), inference(resolution, [status(thm)], [c_2782, c_3572])).
% 4.89/1.96  tff(c_3639, plain, (r2_hidden('#skF_7', k1_tarski(k1_mcart_1('#skF_5'))) | r2_hidden('#skF_6', k1_tarski(k1_mcart_1('#skF_5')))), inference(resolution, [status(thm)], [c_28, c_3589])).
% 4.89/1.96  tff(c_3764, plain, (r2_hidden('#skF_6', k1_tarski(k1_mcart_1('#skF_5')))), inference(splitLeft, [status(thm)], [c_3639])).
% 4.89/1.96  tff(c_3773, plain, (k1_mcart_1('#skF_5')='#skF_6'), inference(resolution, [status(thm)], [c_3764, c_26])).
% 4.89/1.96  tff(c_3830, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2724, c_3773])).
% 4.89/1.96  tff(c_3831, plain, (r2_hidden('#skF_7', k1_tarski(k1_mcart_1('#skF_5')))), inference(splitRight, [status(thm)], [c_3639])).
% 4.89/1.96  tff(c_3870, plain, (k1_mcart_1('#skF_5')='#skF_7'), inference(resolution, [status(thm)], [c_3831, c_26])).
% 4.89/1.96  tff(c_3927, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2709, c_3870])).
% 4.89/1.96  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.89/1.96  
% 4.89/1.96  Inference rules
% 4.89/1.96  ----------------------
% 4.89/1.96  #Ref     : 0
% 4.89/1.96  #Sup     : 579
% 4.89/1.96  #Fact    : 0
% 4.89/1.96  #Define  : 0
% 4.89/1.96  #Split   : 6
% 4.89/1.96  #Chain   : 0
% 4.89/1.96  #Close   : 0
% 4.89/1.96  
% 4.89/1.96  Ordering : KBO
% 4.89/1.96  
% 4.89/1.96  Simplification rules
% 4.89/1.96  ----------------------
% 4.89/1.96  #Subsume      : 16
% 4.89/1.96  #Demod        : 37
% 4.89/1.96  #Tautology    : 135
% 4.89/1.96  #SimpNegUnit  : 6
% 4.89/1.96  #BackRed      : 1
% 4.89/1.96  
% 4.89/1.96  #Partial instantiations: 2550
% 4.89/1.96  #Strategies tried      : 1
% 4.89/1.96  
% 4.89/1.96  Timing (in seconds)
% 4.89/1.96  ----------------------
% 4.89/1.97  Preprocessing        : 0.34
% 4.89/1.97  Parsing              : 0.18
% 4.89/1.97  CNF conversion       : 0.03
% 4.89/1.97  Main loop            : 0.82
% 4.89/1.97  Inferencing          : 0.40
% 4.89/1.97  Reduction            : 0.19
% 4.89/1.97  Demodulation         : 0.13
% 4.89/1.97  BG Simplification    : 0.04
% 4.89/1.97  Subsumption          : 0.13
% 4.89/1.97  Abstraction          : 0.05
% 4.89/1.97  MUC search           : 0.00
% 4.89/1.97  Cooper               : 0.00
% 4.89/1.97  Total                : 1.21
% 4.89/1.97  Index Insertion      : 0.00
% 4.89/1.97  Index Deletion       : 0.00
% 4.89/1.97  Index Matching       : 0.00
% 4.89/1.97  BG Taut test         : 0.00
%------------------------------------------------------------------------------
