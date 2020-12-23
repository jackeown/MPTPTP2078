%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:41 EST 2020

% Result     : Theorem 10.38s
% Output     : CNFRefutation 10.38s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 192 expanded)
%              Number of leaves         :   41 (  87 expanded)
%              Depth                    :    8
%              Number of atoms          :  166 ( 446 expanded)
%              Number of equality atoms :  132 ( 346 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k1_enumset1 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > k1_xboole_0 > #skF_5 > #skF_7 > #skF_3 > #skF_2 > #skF_6 > #skF_9 > #skF_8 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k7_mcart_1,type,(
    k7_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff(k5_mcart_1,type,(
    k5_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(k6_mcart_1,type,(
    k6_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_161,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( A != k1_xboole_0
          & B != k1_xboole_0
          & C != k1_xboole_0
          & ~ ! [D] :
                ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
               => ( D != k5_mcart_1(A,B,C,D)
                  & D != k6_mcart_1(A,B,C,D)
                  & D != k7_mcart_1(A,B,C,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_mcart_1)).

tff(f_53,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_29,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(f_27,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( k4_xboole_0(k2_tarski(A,B),C) = k1_xboole_0
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_zfmisc_1)).

tff(f_97,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k3_mcart_1(C,D,E) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_mcart_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_70,axiom,(
    ! [A,B,C] : k3_mcart_1(A,B,C) = k4_tarski(k4_tarski(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

tff(f_137,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_81,axiom,(
    ! [A] :
      ( ? [B,C] : A = k4_tarski(B,C)
     => ( A != k1_mcart_1(A)
        & A != k2_mcart_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).

tff(f_133,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & ~ ! [D] :
              ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
             => ( k5_mcart_1(A,B,C,D) = k1_mcart_1(k1_mcart_1(D))
                & k6_mcart_1(A,B,C,D) = k2_mcart_1(k1_mcart_1(D))
                & k7_mcart_1(A,B,C,D) = k2_mcart_1(D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_mcart_1)).

tff(f_113,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & ~ ! [D] :
              ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
             => D = k3_mcart_1(k5_mcart_1(A,B,C,D),k6_mcart_1(A,B,C,D),k7_mcart_1(A,B,C,D)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_mcart_1)).

tff(c_92,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_90,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_88,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_42,plain,(
    ! [A_15] : k2_tarski(A_15,A_15) = k1_tarski(A_15) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_4,plain,(
    ! [A_2] : k4_xboole_0(k1_xboole_0,A_2) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_166,plain,(
    ! [C_86,B_87] : ~ r2_hidden(C_86,k4_xboole_0(B_87,k1_tarski(C_86))) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_169,plain,(
    ! [C_86] : ~ r2_hidden(C_86,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_166])).

tff(c_2,plain,(
    ! [A_1] : k4_xboole_0(A_1,k1_xboole_0) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_17226,plain,(
    ! [B_85401,C_85402,A_85403] :
      ( r2_hidden(B_85401,C_85402)
      | k4_xboole_0(k2_tarski(A_85403,B_85401),C_85402) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_17233,plain,(
    ! [B_85401,A_85403] :
      ( r2_hidden(B_85401,k1_xboole_0)
      | k2_tarski(A_85403,B_85401) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_17226])).

tff(c_17235,plain,(
    ! [A_85404,B_85405] : k2_tarski(A_85404,B_85405) != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_169,c_17233])).

tff(c_17237,plain,(
    ! [A_15] : k1_tarski(A_15) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_17235])).

tff(c_160,plain,(
    ! [A_85] :
      ( r2_hidden('#skF_5'(A_85),A_85)
      | k1_xboole_0 = A_85 ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_30,plain,(
    ! [C_14,A_10] :
      ( C_14 = A_10
      | ~ r2_hidden(C_14,k1_tarski(A_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_165,plain,(
    ! [A_10] :
      ( '#skF_5'(k1_tarski(A_10)) = A_10
      | k1_tarski(A_10) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_160,c_30])).

tff(c_17247,plain,(
    ! [A_10] : '#skF_5'(k1_tarski(A_10)) = A_10 ),
    inference(negUnitSimplification,[status(thm)],[c_17237,c_165])).

tff(c_32,plain,(
    ! [C_14] : r2_hidden(C_14,k1_tarski(C_14)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_17830,plain,(
    ! [D_87566,A_87567,C_87568,E_87569] :
      ( ~ r2_hidden(D_87566,A_87567)
      | k3_mcart_1(C_87568,D_87566,E_87569) != '#skF_5'(A_87567)
      | k1_xboole_0 = A_87567 ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_17846,plain,(
    ! [C_87568,C_14,E_87569] :
      ( k3_mcart_1(C_87568,C_14,E_87569) != '#skF_5'(k1_tarski(C_14))
      | k1_tarski(C_14) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_32,c_17830])).

tff(c_17859,plain,(
    ! [C_87568,C_14,E_87569] :
      ( k3_mcart_1(C_87568,C_14,E_87569) != C_14
      | k1_tarski(C_14) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17247,c_17846])).

tff(c_17860,plain,(
    ! [C_87568,C_14,E_87569] : k3_mcart_1(C_87568,C_14,E_87569) != C_14 ),
    inference(negUnitSimplification,[status(thm)],[c_17237,c_17859])).

tff(c_86,plain,(
    m1_subset_1('#skF_9',k3_zfmisc_1('#skF_6','#skF_7','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_9531,plain,(
    ! [A_47793,B_47794,C_47795] : k4_tarski(k4_tarski(A_47793,B_47794),C_47795) = k3_mcart_1(A_47793,B_47794,C_47795) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_82,plain,(
    ! [A_59,B_60] : k2_mcart_1(k4_tarski(A_59,B_60)) = B_60 ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_62,plain,(
    ! [B_33,C_34] : k2_mcart_1(k4_tarski(B_33,C_34)) != k4_tarski(B_33,C_34) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_94,plain,(
    ! [B_33,C_34] : k4_tarski(B_33,C_34) != C_34 ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_62])).

tff(c_9549,plain,(
    ! [A_47793,B_47794,C_47795] : k3_mcart_1(A_47793,B_47794,C_47795) != C_47795 ),
    inference(superposition,[status(thm),theory(equality)],[c_9531,c_94])).

tff(c_211,plain,(
    ! [B_95,C_96,A_97] :
      ( r2_hidden(B_95,C_96)
      | k4_xboole_0(k2_tarski(A_97,B_95),C_96) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_218,plain,(
    ! [B_95,A_97] :
      ( r2_hidden(B_95,k1_xboole_0)
      | k2_tarski(A_97,B_95) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_211])).

tff(c_220,plain,(
    ! [A_98,B_99] : k2_tarski(A_98,B_99) != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_169,c_218])).

tff(c_222,plain,(
    ! [A_15] : k1_tarski(A_15) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_220])).

tff(c_224,plain,(
    ! [A_10] : '#skF_5'(k1_tarski(A_10)) = A_10 ),
    inference(negUnitSimplification,[status(thm)],[c_222,c_165])).

tff(c_713,plain,(
    ! [C_2093,A_2094,D_2095,E_2096] :
      ( ~ r2_hidden(C_2093,A_2094)
      | k3_mcart_1(C_2093,D_2095,E_2096) != '#skF_5'(A_2094)
      | k1_xboole_0 = A_2094 ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_727,plain,(
    ! [C_14,D_2095,E_2096] :
      ( k3_mcart_1(C_14,D_2095,E_2096) != '#skF_5'(k1_tarski(C_14))
      | k1_tarski(C_14) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_32,c_713])).

tff(c_739,plain,(
    ! [C_14,D_2095,E_2096] :
      ( k3_mcart_1(C_14,D_2095,E_2096) != C_14
      | k1_tarski(C_14) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_224,c_727])).

tff(c_740,plain,(
    ! [C_14,D_2095,E_2096] : k3_mcart_1(C_14,D_2095,E_2096) != C_14 ),
    inference(negUnitSimplification,[status(thm)],[c_222,c_739])).

tff(c_84,plain,
    ( k7_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9') = '#skF_9'
    | k6_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9') = '#skF_9'
    | k5_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9') = '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_177,plain,(
    k5_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9') = '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_84])).

tff(c_6410,plain,(
    ! [A_32060,B_32061,C_32062,D_32063] :
      ( k7_mcart_1(A_32060,B_32061,C_32062,D_32063) = k2_mcart_1(D_32063)
      | ~ m1_subset_1(D_32063,k3_zfmisc_1(A_32060,B_32061,C_32062))
      | k1_xboole_0 = C_32062
      | k1_xboole_0 = B_32061
      | k1_xboole_0 = A_32060 ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_6422,plain,
    ( k7_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9') = k2_mcart_1('#skF_9')
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_86,c_6410])).

tff(c_6425,plain,(
    k7_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9') = k2_mcart_1('#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_90,c_88,c_6422])).

tff(c_9260,plain,(
    ! [A_47497,B_47498,C_47499,D_47500] :
      ( k3_mcart_1(k5_mcart_1(A_47497,B_47498,C_47499,D_47500),k6_mcart_1(A_47497,B_47498,C_47499,D_47500),k7_mcart_1(A_47497,B_47498,C_47499,D_47500)) = D_47500
      | ~ m1_subset_1(D_47500,k3_zfmisc_1(A_47497,B_47498,C_47499))
      | k1_xboole_0 = C_47499
      | k1_xboole_0 = B_47498
      | k1_xboole_0 = A_47497 ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_9389,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9'),k6_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9'),k2_mcart_1('#skF_9')) = '#skF_9'
    | ~ m1_subset_1('#skF_9',k3_zfmisc_1('#skF_6','#skF_7','#skF_8'))
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_6425,c_9260])).

tff(c_9424,plain,
    ( k3_mcart_1('#skF_9',k6_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9'),k2_mcart_1('#skF_9')) = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_177,c_9389])).

tff(c_9426,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_90,c_88,c_740,c_9424])).

tff(c_9427,plain,
    ( k6_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9') = '#skF_9'
    | k7_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9') = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_9452,plain,(
    k7_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9') = '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_9427])).

tff(c_17034,plain,(
    ! [A_85118,B_85119,C_85120,D_85121] :
      ( k3_mcart_1(k5_mcart_1(A_85118,B_85119,C_85120,D_85121),k6_mcart_1(A_85118,B_85119,C_85120,D_85121),k7_mcart_1(A_85118,B_85119,C_85120,D_85121)) = D_85121
      | ~ m1_subset_1(D_85121,k3_zfmisc_1(A_85118,B_85119,C_85120))
      | k1_xboole_0 = C_85120
      | k1_xboole_0 = B_85119
      | k1_xboole_0 = A_85118 ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_17163,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9'),k6_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9'),'#skF_9') = '#skF_9'
    | ~ m1_subset_1('#skF_9',k3_zfmisc_1('#skF_6','#skF_7','#skF_8'))
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_9452,c_17034])).

tff(c_17171,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9'),k6_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9'),'#skF_9') = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_17163])).

tff(c_17173,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_90,c_88,c_9549,c_17171])).

tff(c_17174,plain,(
    k6_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9') = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_9427])).

tff(c_23117,plain,(
    ! [A_116488,B_116489,C_116490,D_116491] :
      ( k7_mcart_1(A_116488,B_116489,C_116490,D_116491) = k2_mcart_1(D_116491)
      | ~ m1_subset_1(D_116491,k3_zfmisc_1(A_116488,B_116489,C_116490))
      | k1_xboole_0 = C_116490
      | k1_xboole_0 = B_116489
      | k1_xboole_0 = A_116488 ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_23129,plain,
    ( k7_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9') = k2_mcart_1('#skF_9')
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_86,c_23117])).

tff(c_23132,plain,(
    k7_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9') = k2_mcart_1('#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_90,c_88,c_23129])).

tff(c_24838,plain,(
    ! [A_123821,B_123822,C_123823,D_123824] :
      ( k3_mcart_1(k5_mcart_1(A_123821,B_123822,C_123823,D_123824),k6_mcart_1(A_123821,B_123822,C_123823,D_123824),k7_mcart_1(A_123821,B_123822,C_123823,D_123824)) = D_123824
      | ~ m1_subset_1(D_123824,k3_zfmisc_1(A_123821,B_123822,C_123823))
      | k1_xboole_0 = C_123823
      | k1_xboole_0 = B_123822
      | k1_xboole_0 = A_123821 ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_24943,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9'),k6_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9'),k2_mcart_1('#skF_9')) = '#skF_9'
    | ~ m1_subset_1('#skF_9',k3_zfmisc_1('#skF_6','#skF_7','#skF_8'))
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_23132,c_24838])).

tff(c_24978,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9'),'#skF_9',k2_mcart_1('#skF_9')) = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_17174,c_24943])).

tff(c_24980,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_90,c_88,c_17860,c_24978])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n008.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:17:45 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.38/3.61  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.38/3.62  
% 10.38/3.62  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.38/3.62  %$ r2_hidden > m1_subset_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k1_enumset1 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > k1_xboole_0 > #skF_5 > #skF_7 > #skF_3 > #skF_2 > #skF_6 > #skF_9 > #skF_8 > #skF_1 > #skF_4
% 10.38/3.62  
% 10.38/3.62  %Foreground sorts:
% 10.38/3.62  
% 10.38/3.62  
% 10.38/3.62  %Background operators:
% 10.38/3.62  
% 10.38/3.62  
% 10.38/3.62  %Foreground operators:
% 10.38/3.62  tff('#skF_5', type, '#skF_5': $i > $i).
% 10.38/3.62  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.38/3.62  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.38/3.62  tff(k1_tarski, type, k1_tarski: $i > $i).
% 10.38/3.62  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 10.38/3.62  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 10.38/3.62  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.38/3.62  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 10.38/3.62  tff('#skF_7', type, '#skF_7': $i).
% 10.38/3.62  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 10.38/3.62  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 10.38/3.62  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 10.38/3.62  tff('#skF_6', type, '#skF_6': $i).
% 10.38/3.62  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 10.38/3.62  tff('#skF_9', type, '#skF_9': $i).
% 10.38/3.62  tff(k7_mcart_1, type, k7_mcart_1: ($i * $i * $i * $i) > $i).
% 10.38/3.62  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 10.38/3.62  tff('#skF_8', type, '#skF_8': $i).
% 10.38/3.62  tff(k5_mcart_1, type, k5_mcart_1: ($i * $i * $i * $i) > $i).
% 10.38/3.62  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.38/3.62  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 10.38/3.62  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 10.38/3.62  tff(k6_mcart_1, type, k6_mcart_1: ($i * $i * $i * $i) > $i).
% 10.38/3.62  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.38/3.62  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 10.38/3.62  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 10.38/3.62  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 10.38/3.62  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.38/3.62  
% 10.38/3.64  tff(f_161, negated_conjecture, ~(![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => ((~(D = k5_mcart_1(A, B, C, D)) & ~(D = k6_mcart_1(A, B, C, D))) & ~(D = k7_mcart_1(A, B, C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_mcart_1)).
% 10.38/3.64  tff(f_53, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 10.38/3.64  tff(f_29, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 10.38/3.64  tff(f_62, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 10.38/3.64  tff(f_27, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 10.38/3.64  tff(f_68, axiom, (![A, B, C]: ((k4_xboole_0(k2_tarski(A, B), C) = k1_xboole_0) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_zfmisc_1)).
% 10.38/3.64  tff(f_97, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k3_mcart_1(C, D, E)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_mcart_1)).
% 10.38/3.64  tff(f_51, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 10.38/3.64  tff(f_70, axiom, (![A, B, C]: (k3_mcart_1(A, B, C) = k4_tarski(k4_tarski(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_mcart_1)).
% 10.38/3.64  tff(f_137, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_mcart_1)).
% 10.38/3.64  tff(f_81, axiom, (![A]: ((?[B, C]: (A = k4_tarski(B, C))) => (~(A = k1_mcart_1(A)) & ~(A = k2_mcart_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_mcart_1)).
% 10.38/3.64  tff(f_133, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => (((k5_mcart_1(A, B, C, D) = k1_mcart_1(k1_mcart_1(D))) & (k6_mcart_1(A, B, C, D) = k2_mcart_1(k1_mcart_1(D)))) & (k7_mcart_1(A, B, C, D) = k2_mcart_1(D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_mcart_1)).
% 10.38/3.64  tff(f_113, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => (D = k3_mcart_1(k5_mcart_1(A, B, C, D), k6_mcart_1(A, B, C, D), k7_mcart_1(A, B, C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_mcart_1)).
% 10.38/3.64  tff(c_92, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_161])).
% 10.38/3.64  tff(c_90, plain, (k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_161])).
% 10.38/3.64  tff(c_88, plain, (k1_xboole_0!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_161])).
% 10.38/3.64  tff(c_42, plain, (![A_15]: (k2_tarski(A_15, A_15)=k1_tarski(A_15))), inference(cnfTransformation, [status(thm)], [f_53])).
% 10.38/3.64  tff(c_4, plain, (![A_2]: (k4_xboole_0(k1_xboole_0, A_2)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 10.38/3.64  tff(c_166, plain, (![C_86, B_87]: (~r2_hidden(C_86, k4_xboole_0(B_87, k1_tarski(C_86))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 10.38/3.64  tff(c_169, plain, (![C_86]: (~r2_hidden(C_86, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4, c_166])).
% 10.38/3.64  tff(c_2, plain, (![A_1]: (k4_xboole_0(A_1, k1_xboole_0)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 10.38/3.64  tff(c_17226, plain, (![B_85401, C_85402, A_85403]: (r2_hidden(B_85401, C_85402) | k4_xboole_0(k2_tarski(A_85403, B_85401), C_85402)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_68])).
% 10.38/3.64  tff(c_17233, plain, (![B_85401, A_85403]: (r2_hidden(B_85401, k1_xboole_0) | k2_tarski(A_85403, B_85401)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_17226])).
% 10.38/3.64  tff(c_17235, plain, (![A_85404, B_85405]: (k2_tarski(A_85404, B_85405)!=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_169, c_17233])).
% 10.38/3.64  tff(c_17237, plain, (![A_15]: (k1_tarski(A_15)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_42, c_17235])).
% 10.38/3.64  tff(c_160, plain, (![A_85]: (r2_hidden('#skF_5'(A_85), A_85) | k1_xboole_0=A_85)), inference(cnfTransformation, [status(thm)], [f_97])).
% 10.38/3.64  tff(c_30, plain, (![C_14, A_10]: (C_14=A_10 | ~r2_hidden(C_14, k1_tarski(A_10)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 10.38/3.64  tff(c_165, plain, (![A_10]: ('#skF_5'(k1_tarski(A_10))=A_10 | k1_tarski(A_10)=k1_xboole_0)), inference(resolution, [status(thm)], [c_160, c_30])).
% 10.38/3.64  tff(c_17247, plain, (![A_10]: ('#skF_5'(k1_tarski(A_10))=A_10)), inference(negUnitSimplification, [status(thm)], [c_17237, c_165])).
% 10.38/3.64  tff(c_32, plain, (![C_14]: (r2_hidden(C_14, k1_tarski(C_14)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 10.38/3.64  tff(c_17830, plain, (![D_87566, A_87567, C_87568, E_87569]: (~r2_hidden(D_87566, A_87567) | k3_mcart_1(C_87568, D_87566, E_87569)!='#skF_5'(A_87567) | k1_xboole_0=A_87567)), inference(cnfTransformation, [status(thm)], [f_97])).
% 10.38/3.64  tff(c_17846, plain, (![C_87568, C_14, E_87569]: (k3_mcart_1(C_87568, C_14, E_87569)!='#skF_5'(k1_tarski(C_14)) | k1_tarski(C_14)=k1_xboole_0)), inference(resolution, [status(thm)], [c_32, c_17830])).
% 10.38/3.64  tff(c_17859, plain, (![C_87568, C_14, E_87569]: (k3_mcart_1(C_87568, C_14, E_87569)!=C_14 | k1_tarski(C_14)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_17247, c_17846])).
% 10.38/3.64  tff(c_17860, plain, (![C_87568, C_14, E_87569]: (k3_mcart_1(C_87568, C_14, E_87569)!=C_14)), inference(negUnitSimplification, [status(thm)], [c_17237, c_17859])).
% 10.38/3.64  tff(c_86, plain, (m1_subset_1('#skF_9', k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_161])).
% 10.38/3.64  tff(c_9531, plain, (![A_47793, B_47794, C_47795]: (k4_tarski(k4_tarski(A_47793, B_47794), C_47795)=k3_mcart_1(A_47793, B_47794, C_47795))), inference(cnfTransformation, [status(thm)], [f_70])).
% 10.38/3.64  tff(c_82, plain, (![A_59, B_60]: (k2_mcart_1(k4_tarski(A_59, B_60))=B_60)), inference(cnfTransformation, [status(thm)], [f_137])).
% 10.38/3.64  tff(c_62, plain, (![B_33, C_34]: (k2_mcart_1(k4_tarski(B_33, C_34))!=k4_tarski(B_33, C_34))), inference(cnfTransformation, [status(thm)], [f_81])).
% 10.38/3.64  tff(c_94, plain, (![B_33, C_34]: (k4_tarski(B_33, C_34)!=C_34)), inference(demodulation, [status(thm), theory('equality')], [c_82, c_62])).
% 10.38/3.64  tff(c_9549, plain, (![A_47793, B_47794, C_47795]: (k3_mcart_1(A_47793, B_47794, C_47795)!=C_47795)), inference(superposition, [status(thm), theory('equality')], [c_9531, c_94])).
% 10.38/3.64  tff(c_211, plain, (![B_95, C_96, A_97]: (r2_hidden(B_95, C_96) | k4_xboole_0(k2_tarski(A_97, B_95), C_96)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_68])).
% 10.38/3.64  tff(c_218, plain, (![B_95, A_97]: (r2_hidden(B_95, k1_xboole_0) | k2_tarski(A_97, B_95)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_211])).
% 10.38/3.64  tff(c_220, plain, (![A_98, B_99]: (k2_tarski(A_98, B_99)!=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_169, c_218])).
% 10.38/3.64  tff(c_222, plain, (![A_15]: (k1_tarski(A_15)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_42, c_220])).
% 10.38/3.64  tff(c_224, plain, (![A_10]: ('#skF_5'(k1_tarski(A_10))=A_10)), inference(negUnitSimplification, [status(thm)], [c_222, c_165])).
% 10.38/3.64  tff(c_713, plain, (![C_2093, A_2094, D_2095, E_2096]: (~r2_hidden(C_2093, A_2094) | k3_mcart_1(C_2093, D_2095, E_2096)!='#skF_5'(A_2094) | k1_xboole_0=A_2094)), inference(cnfTransformation, [status(thm)], [f_97])).
% 10.38/3.64  tff(c_727, plain, (![C_14, D_2095, E_2096]: (k3_mcart_1(C_14, D_2095, E_2096)!='#skF_5'(k1_tarski(C_14)) | k1_tarski(C_14)=k1_xboole_0)), inference(resolution, [status(thm)], [c_32, c_713])).
% 10.38/3.64  tff(c_739, plain, (![C_14, D_2095, E_2096]: (k3_mcart_1(C_14, D_2095, E_2096)!=C_14 | k1_tarski(C_14)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_224, c_727])).
% 10.38/3.64  tff(c_740, plain, (![C_14, D_2095, E_2096]: (k3_mcart_1(C_14, D_2095, E_2096)!=C_14)), inference(negUnitSimplification, [status(thm)], [c_222, c_739])).
% 10.38/3.64  tff(c_84, plain, (k7_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9')='#skF_9' | k6_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9')='#skF_9' | k5_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9')='#skF_9'), inference(cnfTransformation, [status(thm)], [f_161])).
% 10.38/3.64  tff(c_177, plain, (k5_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9')='#skF_9'), inference(splitLeft, [status(thm)], [c_84])).
% 10.38/3.64  tff(c_6410, plain, (![A_32060, B_32061, C_32062, D_32063]: (k7_mcart_1(A_32060, B_32061, C_32062, D_32063)=k2_mcart_1(D_32063) | ~m1_subset_1(D_32063, k3_zfmisc_1(A_32060, B_32061, C_32062)) | k1_xboole_0=C_32062 | k1_xboole_0=B_32061 | k1_xboole_0=A_32060)), inference(cnfTransformation, [status(thm)], [f_133])).
% 10.38/3.64  tff(c_6422, plain, (k7_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9')=k2_mcart_1('#skF_9') | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_86, c_6410])).
% 10.38/3.64  tff(c_6425, plain, (k7_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9')=k2_mcart_1('#skF_9')), inference(negUnitSimplification, [status(thm)], [c_92, c_90, c_88, c_6422])).
% 10.38/3.64  tff(c_9260, plain, (![A_47497, B_47498, C_47499, D_47500]: (k3_mcart_1(k5_mcart_1(A_47497, B_47498, C_47499, D_47500), k6_mcart_1(A_47497, B_47498, C_47499, D_47500), k7_mcart_1(A_47497, B_47498, C_47499, D_47500))=D_47500 | ~m1_subset_1(D_47500, k3_zfmisc_1(A_47497, B_47498, C_47499)) | k1_xboole_0=C_47499 | k1_xboole_0=B_47498 | k1_xboole_0=A_47497)), inference(cnfTransformation, [status(thm)], [f_113])).
% 10.38/3.64  tff(c_9389, plain, (k3_mcart_1(k5_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'), k6_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'), k2_mcart_1('#skF_9'))='#skF_9' | ~m1_subset_1('#skF_9', k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8')) | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_6425, c_9260])).
% 10.38/3.64  tff(c_9424, plain, (k3_mcart_1('#skF_9', k6_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'), k2_mcart_1('#skF_9'))='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_86, c_177, c_9389])).
% 10.38/3.64  tff(c_9426, plain, $false, inference(negUnitSimplification, [status(thm)], [c_92, c_90, c_88, c_740, c_9424])).
% 10.38/3.64  tff(c_9427, plain, (k6_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9')='#skF_9' | k7_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9')='#skF_9'), inference(splitRight, [status(thm)], [c_84])).
% 10.38/3.64  tff(c_9452, plain, (k7_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9')='#skF_9'), inference(splitLeft, [status(thm)], [c_9427])).
% 10.38/3.64  tff(c_17034, plain, (![A_85118, B_85119, C_85120, D_85121]: (k3_mcart_1(k5_mcart_1(A_85118, B_85119, C_85120, D_85121), k6_mcart_1(A_85118, B_85119, C_85120, D_85121), k7_mcart_1(A_85118, B_85119, C_85120, D_85121))=D_85121 | ~m1_subset_1(D_85121, k3_zfmisc_1(A_85118, B_85119, C_85120)) | k1_xboole_0=C_85120 | k1_xboole_0=B_85119 | k1_xboole_0=A_85118)), inference(cnfTransformation, [status(thm)], [f_113])).
% 10.38/3.64  tff(c_17163, plain, (k3_mcart_1(k5_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'), k6_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'), '#skF_9')='#skF_9' | ~m1_subset_1('#skF_9', k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8')) | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_9452, c_17034])).
% 10.38/3.64  tff(c_17171, plain, (k3_mcart_1(k5_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'), k6_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'), '#skF_9')='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_86, c_17163])).
% 10.38/3.64  tff(c_17173, plain, $false, inference(negUnitSimplification, [status(thm)], [c_92, c_90, c_88, c_9549, c_17171])).
% 10.38/3.64  tff(c_17174, plain, (k6_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9')='#skF_9'), inference(splitRight, [status(thm)], [c_9427])).
% 10.38/3.64  tff(c_23117, plain, (![A_116488, B_116489, C_116490, D_116491]: (k7_mcart_1(A_116488, B_116489, C_116490, D_116491)=k2_mcart_1(D_116491) | ~m1_subset_1(D_116491, k3_zfmisc_1(A_116488, B_116489, C_116490)) | k1_xboole_0=C_116490 | k1_xboole_0=B_116489 | k1_xboole_0=A_116488)), inference(cnfTransformation, [status(thm)], [f_133])).
% 10.38/3.64  tff(c_23129, plain, (k7_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9')=k2_mcart_1('#skF_9') | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_86, c_23117])).
% 10.38/3.64  tff(c_23132, plain, (k7_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9')=k2_mcart_1('#skF_9')), inference(negUnitSimplification, [status(thm)], [c_92, c_90, c_88, c_23129])).
% 10.38/3.64  tff(c_24838, plain, (![A_123821, B_123822, C_123823, D_123824]: (k3_mcart_1(k5_mcart_1(A_123821, B_123822, C_123823, D_123824), k6_mcart_1(A_123821, B_123822, C_123823, D_123824), k7_mcart_1(A_123821, B_123822, C_123823, D_123824))=D_123824 | ~m1_subset_1(D_123824, k3_zfmisc_1(A_123821, B_123822, C_123823)) | k1_xboole_0=C_123823 | k1_xboole_0=B_123822 | k1_xboole_0=A_123821)), inference(cnfTransformation, [status(thm)], [f_113])).
% 10.38/3.64  tff(c_24943, plain, (k3_mcart_1(k5_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'), k6_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'), k2_mcart_1('#skF_9'))='#skF_9' | ~m1_subset_1('#skF_9', k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8')) | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_23132, c_24838])).
% 10.38/3.64  tff(c_24978, plain, (k3_mcart_1(k5_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'), '#skF_9', k2_mcart_1('#skF_9'))='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_86, c_17174, c_24943])).
% 10.38/3.64  tff(c_24980, plain, $false, inference(negUnitSimplification, [status(thm)], [c_92, c_90, c_88, c_17860, c_24978])).
% 10.38/3.64  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.38/3.64  
% 10.38/3.64  Inference rules
% 10.38/3.64  ----------------------
% 10.38/3.64  #Ref     : 40
% 10.38/3.64  #Sup     : 2820
% 10.38/3.64  #Fact    : 6
% 10.38/3.64  #Define  : 0
% 10.38/3.64  #Split   : 19
% 10.38/3.64  #Chain   : 0
% 10.38/3.64  #Close   : 0
% 10.38/3.64  
% 10.38/3.64  Ordering : KBO
% 10.38/3.64  
% 10.38/3.64  Simplification rules
% 10.38/3.64  ----------------------
% 10.38/3.64  #Subsume      : 636
% 10.38/3.64  #Demod        : 488
% 10.38/3.64  #Tautology    : 663
% 10.38/3.64  #SimpNegUnit  : 648
% 10.38/3.64  #BackRed      : 44
% 10.38/3.64  
% 10.38/3.64  #Partial instantiations: 39075
% 10.38/3.64  #Strategies tried      : 1
% 10.38/3.64  
% 10.38/3.64  Timing (in seconds)
% 10.38/3.64  ----------------------
% 10.38/3.64  Preprocessing        : 0.35
% 10.38/3.64  Parsing              : 0.18
% 10.38/3.64  CNF conversion       : 0.03
% 10.38/3.64  Main loop            : 2.52
% 10.38/3.64  Inferencing          : 1.32
% 10.38/3.64  Reduction            : 0.57
% 10.38/3.64  Demodulation         : 0.36
% 10.38/3.64  BG Simplification    : 0.08
% 10.38/3.64  Subsumption          : 0.41
% 10.38/3.64  Abstraction          : 0.11
% 10.38/3.64  MUC search           : 0.00
% 10.38/3.64  Cooper               : 0.00
% 10.38/3.64  Total                : 2.91
% 10.38/3.64  Index Insertion      : 0.00
% 10.38/3.64  Index Deletion       : 0.00
% 10.38/3.64  Index Matching       : 0.00
% 10.38/3.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------
