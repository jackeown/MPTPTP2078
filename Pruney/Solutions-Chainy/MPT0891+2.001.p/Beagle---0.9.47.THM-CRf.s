%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:40 EST 2020

% Result     : Theorem 7.94s
% Output     : CNFRefutation 8.34s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 159 expanded)
%              Number of leaves         :   41 (  78 expanded)
%              Depth                    :    6
%              Number of atoms          :  151 ( 386 expanded)
%              Number of equality atoms :  126 ( 318 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_xboole_0 > #nlpp > k2_mcart_1 > k1_zfmisc_1 > k1_tarski > k1_mcart_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_11 > #skF_3 > #skF_10 > #skF_6 > #skF_2 > #skF_1 > #skF_9 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_7',type,(
    '#skF_7': $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k7_mcart_1,type,(
    k7_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff(k5_mcart_1,type,(
    k5_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_mcart_1,type,(
    k6_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_184,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( A != k1_xboole_0
          & B != k1_xboole_0
          & C != k1_xboole_0
          & ~ ! [D] :
                ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
               => ( D != k5_mcart_1(A,B,C,D)
                  & D != k6_mcart_1(A,B,C,D)
                  & D != k7_mcart_1(A,B,C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_mcart_1)).

tff(f_33,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_63,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_120,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k3_mcart_1(C,D,E) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_mcart_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_83,axiom,(
    ! [A,B,C] : k3_mcart_1(A,B,C) = k4_tarski(k4_tarski(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

tff(f_160,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_104,axiom,(
    ! [A] :
      ( ? [B,C] : A = k4_tarski(B,C)
     => ( A != k1_mcart_1(A)
        & A != k2_mcart_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_mcart_1)).

tff(f_156,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & ~ ! [D] :
              ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
             => ( k5_mcart_1(A,B,C,D) = k1_mcart_1(k1_mcart_1(D))
                & k6_mcart_1(A,B,C,D) = k2_mcart_1(k1_mcart_1(D))
                & k7_mcart_1(A,B,C,D) = k2_mcart_1(D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_mcart_1)).

tff(f_136,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & ~ ! [D] :
              ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
             => D = k3_mcart_1(k5_mcart_1(A,B,C,D),k6_mcart_1(A,B,C,D),k7_mcart_1(A,B,C,D)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_mcart_1)).

tff(c_86,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_84,plain,(
    k1_xboole_0 != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_82,plain,(
    k1_xboole_0 != '#skF_10' ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_8,plain,(
    ! [A_1] : k2_xboole_0(A_1,k1_xboole_0) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_5338,plain,(
    ! [A_29696,B_29697] : k2_xboole_0(k1_tarski(A_29696),B_29697) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_5342,plain,(
    ! [A_29696] : k1_tarski(A_29696) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_5338])).

tff(c_10296,plain,(
    ! [A_56346] :
      ( r2_hidden('#skF_7'(A_56346),A_56346)
      | k1_xboole_0 = A_56346 ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_14,plain,(
    ! [C_7,A_3] :
      ( C_7 = A_3
      | ~ r2_hidden(C_7,k1_tarski(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_10300,plain,(
    ! [A_3] :
      ( '#skF_7'(k1_tarski(A_3)) = A_3
      | k1_tarski(A_3) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10296,c_14])).

tff(c_10303,plain,(
    ! [A_3] : '#skF_7'(k1_tarski(A_3)) = A_3 ),
    inference(negUnitSimplification,[status(thm)],[c_5342,c_10300])).

tff(c_16,plain,(
    ! [C_7] : r2_hidden(C_7,k1_tarski(C_7)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_11301,plain,(
    ! [D_58082,A_58083,C_58084,E_58085] :
      ( ~ r2_hidden(D_58082,A_58083)
      | k3_mcart_1(C_58084,D_58082,E_58085) != '#skF_7'(A_58083)
      | k1_xboole_0 = A_58083 ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_11305,plain,(
    ! [C_58084,C_7,E_58085] :
      ( k3_mcart_1(C_58084,C_7,E_58085) != '#skF_7'(k1_tarski(C_7))
      | k1_tarski(C_7) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_16,c_11301])).

tff(c_11308,plain,(
    ! [C_58084,C_7,E_58085] :
      ( k3_mcart_1(C_58084,C_7,E_58085) != C_7
      | k1_tarski(C_7) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10303,c_11305])).

tff(c_11309,plain,(
    ! [C_58084,C_7,E_58085] : k3_mcart_1(C_58084,C_7,E_58085) != C_7 ),
    inference(negUnitSimplification,[status(thm)],[c_5342,c_11308])).

tff(c_80,plain,(
    m1_subset_1('#skF_11',k3_zfmisc_1('#skF_8','#skF_9','#skF_10')) ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_5411,plain,(
    ! [A_29710,B_29711,C_29712] : k4_tarski(k4_tarski(A_29710,B_29711),C_29712) = k3_mcart_1(A_29710,B_29711,C_29712) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_76,plain,(
    ! [A_64,B_65] : k2_mcart_1(k4_tarski(A_64,B_65)) = B_65 ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_56,plain,(
    ! [B_38,C_39] : k2_mcart_1(k4_tarski(B_38,C_39)) != k4_tarski(B_38,C_39) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_88,plain,(
    ! [B_38,C_39] : k4_tarski(B_38,C_39) != C_39 ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_56])).

tff(c_5433,plain,(
    ! [A_29710,B_29711,C_29712] : k3_mcart_1(A_29710,B_29711,C_29712) != C_29712 ),
    inference(superposition,[status(thm),theory(equality)],[c_5411,c_88])).

tff(c_151,plain,(
    ! [A_86,B_87] : k2_xboole_0(k1_tarski(A_86),B_87) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_155,plain,(
    ! [A_86] : k1_tarski(A_86) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_151])).

tff(c_170,plain,(
    ! [A_92] :
      ( r2_hidden('#skF_7'(A_92),A_92)
      | k1_xboole_0 = A_92 ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_174,plain,(
    ! [A_3] :
      ( '#skF_7'(k1_tarski(A_3)) = A_3
      | k1_tarski(A_3) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_170,c_14])).

tff(c_177,plain,(
    ! [A_3] : '#skF_7'(k1_tarski(A_3)) = A_3 ),
    inference(negUnitSimplification,[status(thm)],[c_155,c_174])).

tff(c_1169,plain,(
    ! [C_1813,A_1814,D_1815,E_1816] :
      ( ~ r2_hidden(C_1813,A_1814)
      | k3_mcart_1(C_1813,D_1815,E_1816) != '#skF_7'(A_1814)
      | k1_xboole_0 = A_1814 ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_1173,plain,(
    ! [C_7,D_1815,E_1816] :
      ( k3_mcart_1(C_7,D_1815,E_1816) != '#skF_7'(k1_tarski(C_7))
      | k1_tarski(C_7) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_16,c_1169])).

tff(c_1176,plain,(
    ! [C_7,D_1815,E_1816] :
      ( k3_mcart_1(C_7,D_1815,E_1816) != C_7
      | k1_tarski(C_7) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_177,c_1173])).

tff(c_1177,plain,(
    ! [C_7,D_1815,E_1816] : k3_mcart_1(C_7,D_1815,E_1816) != C_7 ),
    inference(negUnitSimplification,[status(thm)],[c_155,c_1176])).

tff(c_78,plain,
    ( k7_mcart_1('#skF_8','#skF_9','#skF_10','#skF_11') = '#skF_11'
    | k6_mcart_1('#skF_8','#skF_9','#skF_10','#skF_11') = '#skF_11'
    | k5_mcart_1('#skF_8','#skF_9','#skF_10','#skF_11') = '#skF_11' ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_111,plain,(
    k5_mcart_1('#skF_8','#skF_9','#skF_10','#skF_11') = '#skF_11' ),
    inference(splitLeft,[status(thm)],[c_78])).

tff(c_4874,plain,(
    ! [A_25334,B_25335,C_25336,D_25337] :
      ( k7_mcart_1(A_25334,B_25335,C_25336,D_25337) = k2_mcart_1(D_25337)
      | ~ m1_subset_1(D_25337,k3_zfmisc_1(A_25334,B_25335,C_25336))
      | k1_xboole_0 = C_25336
      | k1_xboole_0 = B_25335
      | k1_xboole_0 = A_25334 ) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_4898,plain,
    ( k7_mcart_1('#skF_8','#skF_9','#skF_10','#skF_11') = k2_mcart_1('#skF_11')
    | k1_xboole_0 = '#skF_10'
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_80,c_4874])).

tff(c_4904,plain,(
    k7_mcart_1('#skF_8','#skF_9','#skF_10','#skF_11') = k2_mcart_1('#skF_11') ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_84,c_82,c_4898])).

tff(c_5203,plain,(
    ! [A_29397,B_29398,C_29399,D_29400] :
      ( k3_mcart_1(k5_mcart_1(A_29397,B_29398,C_29399,D_29400),k6_mcart_1(A_29397,B_29398,C_29399,D_29400),k7_mcart_1(A_29397,B_29398,C_29399,D_29400)) = D_29400
      | ~ m1_subset_1(D_29400,k3_zfmisc_1(A_29397,B_29398,C_29399))
      | k1_xboole_0 = C_29399
      | k1_xboole_0 = B_29398
      | k1_xboole_0 = A_29397 ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_5261,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_8','#skF_9','#skF_10','#skF_11'),k6_mcart_1('#skF_8','#skF_9','#skF_10','#skF_11'),k2_mcart_1('#skF_11')) = '#skF_11'
    | ~ m1_subset_1('#skF_11',k3_zfmisc_1('#skF_8','#skF_9','#skF_10'))
    | k1_xboole_0 = '#skF_10'
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_4904,c_5203])).

tff(c_5304,plain,
    ( k3_mcart_1('#skF_11',k6_mcart_1('#skF_8','#skF_9','#skF_10','#skF_11'),k2_mcart_1('#skF_11')) = '#skF_11'
    | k1_xboole_0 = '#skF_10'
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_111,c_5261])).

tff(c_5306,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_84,c_82,c_1177,c_5304])).

tff(c_5307,plain,
    ( k6_mcart_1('#skF_8','#skF_9','#skF_10','#skF_11') = '#skF_11'
    | k7_mcart_1('#skF_8','#skF_9','#skF_10','#skF_11') = '#skF_11' ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_5363,plain,(
    k7_mcart_1('#skF_8','#skF_9','#skF_10','#skF_11') = '#skF_11' ),
    inference(splitLeft,[status(thm)],[c_5307])).

tff(c_10211,plain,(
    ! [A_56054,B_56055,C_56056,D_56057] :
      ( k3_mcart_1(k5_mcart_1(A_56054,B_56055,C_56056,D_56057),k6_mcart_1(A_56054,B_56055,C_56056,D_56057),k7_mcart_1(A_56054,B_56055,C_56056,D_56057)) = D_56057
      | ~ m1_subset_1(D_56057,k3_zfmisc_1(A_56054,B_56055,C_56056))
      | k1_xboole_0 = C_56056
      | k1_xboole_0 = B_56055
      | k1_xboole_0 = A_56054 ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_10287,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_8','#skF_9','#skF_10','#skF_11'),k6_mcart_1('#skF_8','#skF_9','#skF_10','#skF_11'),'#skF_11') = '#skF_11'
    | ~ m1_subset_1('#skF_11',k3_zfmisc_1('#skF_8','#skF_9','#skF_10'))
    | k1_xboole_0 = '#skF_10'
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_5363,c_10211])).

tff(c_10291,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_8','#skF_9','#skF_10','#skF_11'),k6_mcart_1('#skF_8','#skF_9','#skF_10','#skF_11'),'#skF_11') = '#skF_11'
    | k1_xboole_0 = '#skF_10'
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_10287])).

tff(c_10293,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_84,c_82,c_5433,c_10291])).

tff(c_10294,plain,(
    k6_mcart_1('#skF_8','#skF_9','#skF_10','#skF_11') = '#skF_11' ),
    inference(splitRight,[status(thm)],[c_5307])).

tff(c_14607,plain,(
    ! [A_78233,B_78234,C_78235,D_78236] :
      ( k7_mcart_1(A_78233,B_78234,C_78235,D_78236) = k2_mcart_1(D_78236)
      | ~ m1_subset_1(D_78236,k3_zfmisc_1(A_78233,B_78234,C_78235))
      | k1_xboole_0 = C_78235
      | k1_xboole_0 = B_78234
      | k1_xboole_0 = A_78233 ) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_14630,plain,
    ( k7_mcart_1('#skF_8','#skF_9','#skF_10','#skF_11') = k2_mcart_1('#skF_11')
    | k1_xboole_0 = '#skF_10'
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_80,c_14607])).

tff(c_14636,plain,(
    k7_mcart_1('#skF_8','#skF_9','#skF_10','#skF_11') = k2_mcart_1('#skF_11') ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_84,c_82,c_14630])).

tff(c_15342,plain,(
    ! [A_85566,B_85567,C_85568,D_85569] :
      ( k3_mcart_1(k5_mcart_1(A_85566,B_85567,C_85568,D_85569),k6_mcart_1(A_85566,B_85567,C_85568,D_85569),k7_mcart_1(A_85566,B_85567,C_85568,D_85569)) = D_85569
      | ~ m1_subset_1(D_85569,k3_zfmisc_1(A_85566,B_85567,C_85568))
      | k1_xboole_0 = C_85568
      | k1_xboole_0 = B_85567
      | k1_xboole_0 = A_85566 ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_15401,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_8','#skF_9','#skF_10','#skF_11'),k6_mcart_1('#skF_8','#skF_9','#skF_10','#skF_11'),k2_mcart_1('#skF_11')) = '#skF_11'
    | ~ m1_subset_1('#skF_11',k3_zfmisc_1('#skF_8','#skF_9','#skF_10'))
    | k1_xboole_0 = '#skF_10'
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_14636,c_15342])).

tff(c_15440,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_8','#skF_9','#skF_10','#skF_11'),'#skF_11',k2_mcart_1('#skF_11')) = '#skF_11'
    | k1_xboole_0 = '#skF_10'
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_10294,c_15401])).

tff(c_15442,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_84,c_82,c_11309,c_15440])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.32  % Computer   : n021.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 12:38:34 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.94/2.81  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.94/2.81  
% 7.94/2.81  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.94/2.82  %$ r2_hidden > r1_xboole_0 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_xboole_0 > #nlpp > k2_mcart_1 > k1_zfmisc_1 > k1_tarski > k1_mcart_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_11 > #skF_3 > #skF_10 > #skF_6 > #skF_2 > #skF_1 > #skF_9 > #skF_8 > #skF_4
% 7.94/2.82  
% 7.94/2.82  %Foreground sorts:
% 7.94/2.82  
% 7.94/2.82  
% 7.94/2.82  %Background operators:
% 7.94/2.82  
% 7.94/2.82  
% 7.94/2.82  %Foreground operators:
% 7.94/2.82  tff('#skF_7', type, '#skF_7': $i > $i).
% 7.94/2.82  tff('#skF_5', type, '#skF_5': $i > $i).
% 7.94/2.82  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.94/2.82  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.94/2.82  tff('#skF_11', type, '#skF_11': $i).
% 7.94/2.82  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.94/2.82  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 7.94/2.82  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.94/2.82  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 7.94/2.82  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 7.94/2.82  tff('#skF_10', type, '#skF_10': $i).
% 7.94/2.82  tff('#skF_6', type, '#skF_6': $i).
% 7.94/2.82  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 7.94/2.82  tff('#skF_2', type, '#skF_2': $i).
% 7.94/2.82  tff('#skF_1', type, '#skF_1': $i).
% 7.94/2.82  tff('#skF_9', type, '#skF_9': $i).
% 7.94/2.82  tff(k7_mcart_1, type, k7_mcart_1: ($i * $i * $i * $i) > $i).
% 7.94/2.82  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 7.94/2.82  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.94/2.82  tff('#skF_8', type, '#skF_8': $i).
% 7.94/2.82  tff(k5_mcart_1, type, k5_mcart_1: ($i * $i * $i * $i) > $i).
% 7.94/2.82  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.94/2.82  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 7.94/2.82  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.94/2.82  tff(k6_mcart_1, type, k6_mcart_1: ($i * $i * $i * $i) > $i).
% 7.94/2.82  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.94/2.82  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 7.94/2.82  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.94/2.82  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.94/2.82  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 7.94/2.82  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.94/2.82  
% 8.34/2.83  tff(f_184, negated_conjecture, ~(![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => ((~(D = k5_mcart_1(A, B, C, D)) & ~(D = k6_mcart_1(A, B, C, D))) & ~(D = k7_mcart_1(A, B, C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_mcart_1)).
% 8.34/2.83  tff(f_33, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 8.34/2.83  tff(f_63, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 8.34/2.83  tff(f_120, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k3_mcart_1(C, D, E)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_mcart_1)).
% 8.34/2.83  tff(f_52, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 8.34/2.83  tff(f_83, axiom, (![A, B, C]: (k3_mcart_1(A, B, C) = k4_tarski(k4_tarski(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_mcart_1)).
% 8.34/2.83  tff(f_160, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 8.34/2.83  tff(f_104, axiom, (![A]: ((?[B, C]: (A = k4_tarski(B, C))) => (~(A = k1_mcart_1(A)) & ~(A = k2_mcart_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_mcart_1)).
% 8.34/2.83  tff(f_156, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => (((k5_mcart_1(A, B, C, D) = k1_mcart_1(k1_mcart_1(D))) & (k6_mcart_1(A, B, C, D) = k2_mcart_1(k1_mcart_1(D)))) & (k7_mcart_1(A, B, C, D) = k2_mcart_1(D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_mcart_1)).
% 8.34/2.83  tff(f_136, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => (D = k3_mcart_1(k5_mcart_1(A, B, C, D), k6_mcart_1(A, B, C, D), k7_mcart_1(A, B, C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_mcart_1)).
% 8.34/2.83  tff(c_86, plain, (k1_xboole_0!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_184])).
% 8.34/2.83  tff(c_84, plain, (k1_xboole_0!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_184])).
% 8.34/2.83  tff(c_82, plain, (k1_xboole_0!='#skF_10'), inference(cnfTransformation, [status(thm)], [f_184])).
% 8.34/2.83  tff(c_8, plain, (![A_1]: (k2_xboole_0(A_1, k1_xboole_0)=A_1)), inference(cnfTransformation, [status(thm)], [f_33])).
% 8.34/2.83  tff(c_5338, plain, (![A_29696, B_29697]: (k2_xboole_0(k1_tarski(A_29696), B_29697)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_63])).
% 8.34/2.83  tff(c_5342, plain, (![A_29696]: (k1_tarski(A_29696)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_8, c_5338])).
% 8.34/2.83  tff(c_10296, plain, (![A_56346]: (r2_hidden('#skF_7'(A_56346), A_56346) | k1_xboole_0=A_56346)), inference(cnfTransformation, [status(thm)], [f_120])).
% 8.34/2.83  tff(c_14, plain, (![C_7, A_3]: (C_7=A_3 | ~r2_hidden(C_7, k1_tarski(A_3)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 8.34/2.83  tff(c_10300, plain, (![A_3]: ('#skF_7'(k1_tarski(A_3))=A_3 | k1_tarski(A_3)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10296, c_14])).
% 8.34/2.83  tff(c_10303, plain, (![A_3]: ('#skF_7'(k1_tarski(A_3))=A_3)), inference(negUnitSimplification, [status(thm)], [c_5342, c_10300])).
% 8.34/2.83  tff(c_16, plain, (![C_7]: (r2_hidden(C_7, k1_tarski(C_7)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 8.34/2.83  tff(c_11301, plain, (![D_58082, A_58083, C_58084, E_58085]: (~r2_hidden(D_58082, A_58083) | k3_mcart_1(C_58084, D_58082, E_58085)!='#skF_7'(A_58083) | k1_xboole_0=A_58083)), inference(cnfTransformation, [status(thm)], [f_120])).
% 8.34/2.83  tff(c_11305, plain, (![C_58084, C_7, E_58085]: (k3_mcart_1(C_58084, C_7, E_58085)!='#skF_7'(k1_tarski(C_7)) | k1_tarski(C_7)=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_11301])).
% 8.34/2.83  tff(c_11308, plain, (![C_58084, C_7, E_58085]: (k3_mcart_1(C_58084, C_7, E_58085)!=C_7 | k1_tarski(C_7)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10303, c_11305])).
% 8.34/2.83  tff(c_11309, plain, (![C_58084, C_7, E_58085]: (k3_mcart_1(C_58084, C_7, E_58085)!=C_7)), inference(negUnitSimplification, [status(thm)], [c_5342, c_11308])).
% 8.34/2.83  tff(c_80, plain, (m1_subset_1('#skF_11', k3_zfmisc_1('#skF_8', '#skF_9', '#skF_10'))), inference(cnfTransformation, [status(thm)], [f_184])).
% 8.34/2.83  tff(c_5411, plain, (![A_29710, B_29711, C_29712]: (k4_tarski(k4_tarski(A_29710, B_29711), C_29712)=k3_mcart_1(A_29710, B_29711, C_29712))), inference(cnfTransformation, [status(thm)], [f_83])).
% 8.34/2.83  tff(c_76, plain, (![A_64, B_65]: (k2_mcart_1(k4_tarski(A_64, B_65))=B_65)), inference(cnfTransformation, [status(thm)], [f_160])).
% 8.34/2.83  tff(c_56, plain, (![B_38, C_39]: (k2_mcart_1(k4_tarski(B_38, C_39))!=k4_tarski(B_38, C_39))), inference(cnfTransformation, [status(thm)], [f_104])).
% 8.34/2.83  tff(c_88, plain, (![B_38, C_39]: (k4_tarski(B_38, C_39)!=C_39)), inference(demodulation, [status(thm), theory('equality')], [c_76, c_56])).
% 8.34/2.83  tff(c_5433, plain, (![A_29710, B_29711, C_29712]: (k3_mcart_1(A_29710, B_29711, C_29712)!=C_29712)), inference(superposition, [status(thm), theory('equality')], [c_5411, c_88])).
% 8.34/2.83  tff(c_151, plain, (![A_86, B_87]: (k2_xboole_0(k1_tarski(A_86), B_87)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_63])).
% 8.34/2.83  tff(c_155, plain, (![A_86]: (k1_tarski(A_86)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_8, c_151])).
% 8.34/2.83  tff(c_170, plain, (![A_92]: (r2_hidden('#skF_7'(A_92), A_92) | k1_xboole_0=A_92)), inference(cnfTransformation, [status(thm)], [f_120])).
% 8.34/2.83  tff(c_174, plain, (![A_3]: ('#skF_7'(k1_tarski(A_3))=A_3 | k1_tarski(A_3)=k1_xboole_0)), inference(resolution, [status(thm)], [c_170, c_14])).
% 8.34/2.83  tff(c_177, plain, (![A_3]: ('#skF_7'(k1_tarski(A_3))=A_3)), inference(negUnitSimplification, [status(thm)], [c_155, c_174])).
% 8.34/2.83  tff(c_1169, plain, (![C_1813, A_1814, D_1815, E_1816]: (~r2_hidden(C_1813, A_1814) | k3_mcart_1(C_1813, D_1815, E_1816)!='#skF_7'(A_1814) | k1_xboole_0=A_1814)), inference(cnfTransformation, [status(thm)], [f_120])).
% 8.34/2.83  tff(c_1173, plain, (![C_7, D_1815, E_1816]: (k3_mcart_1(C_7, D_1815, E_1816)!='#skF_7'(k1_tarski(C_7)) | k1_tarski(C_7)=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_1169])).
% 8.34/2.83  tff(c_1176, plain, (![C_7, D_1815, E_1816]: (k3_mcart_1(C_7, D_1815, E_1816)!=C_7 | k1_tarski(C_7)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_177, c_1173])).
% 8.34/2.83  tff(c_1177, plain, (![C_7, D_1815, E_1816]: (k3_mcart_1(C_7, D_1815, E_1816)!=C_7)), inference(negUnitSimplification, [status(thm)], [c_155, c_1176])).
% 8.34/2.83  tff(c_78, plain, (k7_mcart_1('#skF_8', '#skF_9', '#skF_10', '#skF_11')='#skF_11' | k6_mcart_1('#skF_8', '#skF_9', '#skF_10', '#skF_11')='#skF_11' | k5_mcart_1('#skF_8', '#skF_9', '#skF_10', '#skF_11')='#skF_11'), inference(cnfTransformation, [status(thm)], [f_184])).
% 8.34/2.83  tff(c_111, plain, (k5_mcart_1('#skF_8', '#skF_9', '#skF_10', '#skF_11')='#skF_11'), inference(splitLeft, [status(thm)], [c_78])).
% 8.34/2.83  tff(c_4874, plain, (![A_25334, B_25335, C_25336, D_25337]: (k7_mcart_1(A_25334, B_25335, C_25336, D_25337)=k2_mcart_1(D_25337) | ~m1_subset_1(D_25337, k3_zfmisc_1(A_25334, B_25335, C_25336)) | k1_xboole_0=C_25336 | k1_xboole_0=B_25335 | k1_xboole_0=A_25334)), inference(cnfTransformation, [status(thm)], [f_156])).
% 8.34/2.83  tff(c_4898, plain, (k7_mcart_1('#skF_8', '#skF_9', '#skF_10', '#skF_11')=k2_mcart_1('#skF_11') | k1_xboole_0='#skF_10' | k1_xboole_0='#skF_9' | k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_80, c_4874])).
% 8.34/2.83  tff(c_4904, plain, (k7_mcart_1('#skF_8', '#skF_9', '#skF_10', '#skF_11')=k2_mcart_1('#skF_11')), inference(negUnitSimplification, [status(thm)], [c_86, c_84, c_82, c_4898])).
% 8.34/2.83  tff(c_5203, plain, (![A_29397, B_29398, C_29399, D_29400]: (k3_mcart_1(k5_mcart_1(A_29397, B_29398, C_29399, D_29400), k6_mcart_1(A_29397, B_29398, C_29399, D_29400), k7_mcart_1(A_29397, B_29398, C_29399, D_29400))=D_29400 | ~m1_subset_1(D_29400, k3_zfmisc_1(A_29397, B_29398, C_29399)) | k1_xboole_0=C_29399 | k1_xboole_0=B_29398 | k1_xboole_0=A_29397)), inference(cnfTransformation, [status(thm)], [f_136])).
% 8.34/2.83  tff(c_5261, plain, (k3_mcart_1(k5_mcart_1('#skF_8', '#skF_9', '#skF_10', '#skF_11'), k6_mcart_1('#skF_8', '#skF_9', '#skF_10', '#skF_11'), k2_mcart_1('#skF_11'))='#skF_11' | ~m1_subset_1('#skF_11', k3_zfmisc_1('#skF_8', '#skF_9', '#skF_10')) | k1_xboole_0='#skF_10' | k1_xboole_0='#skF_9' | k1_xboole_0='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_4904, c_5203])).
% 8.34/2.83  tff(c_5304, plain, (k3_mcart_1('#skF_11', k6_mcart_1('#skF_8', '#skF_9', '#skF_10', '#skF_11'), k2_mcart_1('#skF_11'))='#skF_11' | k1_xboole_0='#skF_10' | k1_xboole_0='#skF_9' | k1_xboole_0='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_111, c_5261])).
% 8.34/2.83  tff(c_5306, plain, $false, inference(negUnitSimplification, [status(thm)], [c_86, c_84, c_82, c_1177, c_5304])).
% 8.34/2.83  tff(c_5307, plain, (k6_mcart_1('#skF_8', '#skF_9', '#skF_10', '#skF_11')='#skF_11' | k7_mcart_1('#skF_8', '#skF_9', '#skF_10', '#skF_11')='#skF_11'), inference(splitRight, [status(thm)], [c_78])).
% 8.34/2.83  tff(c_5363, plain, (k7_mcart_1('#skF_8', '#skF_9', '#skF_10', '#skF_11')='#skF_11'), inference(splitLeft, [status(thm)], [c_5307])).
% 8.34/2.83  tff(c_10211, plain, (![A_56054, B_56055, C_56056, D_56057]: (k3_mcart_1(k5_mcart_1(A_56054, B_56055, C_56056, D_56057), k6_mcart_1(A_56054, B_56055, C_56056, D_56057), k7_mcart_1(A_56054, B_56055, C_56056, D_56057))=D_56057 | ~m1_subset_1(D_56057, k3_zfmisc_1(A_56054, B_56055, C_56056)) | k1_xboole_0=C_56056 | k1_xboole_0=B_56055 | k1_xboole_0=A_56054)), inference(cnfTransformation, [status(thm)], [f_136])).
% 8.34/2.83  tff(c_10287, plain, (k3_mcart_1(k5_mcart_1('#skF_8', '#skF_9', '#skF_10', '#skF_11'), k6_mcart_1('#skF_8', '#skF_9', '#skF_10', '#skF_11'), '#skF_11')='#skF_11' | ~m1_subset_1('#skF_11', k3_zfmisc_1('#skF_8', '#skF_9', '#skF_10')) | k1_xboole_0='#skF_10' | k1_xboole_0='#skF_9' | k1_xboole_0='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_5363, c_10211])).
% 8.34/2.83  tff(c_10291, plain, (k3_mcart_1(k5_mcart_1('#skF_8', '#skF_9', '#skF_10', '#skF_11'), k6_mcart_1('#skF_8', '#skF_9', '#skF_10', '#skF_11'), '#skF_11')='#skF_11' | k1_xboole_0='#skF_10' | k1_xboole_0='#skF_9' | k1_xboole_0='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_10287])).
% 8.34/2.83  tff(c_10293, plain, $false, inference(negUnitSimplification, [status(thm)], [c_86, c_84, c_82, c_5433, c_10291])).
% 8.34/2.83  tff(c_10294, plain, (k6_mcart_1('#skF_8', '#skF_9', '#skF_10', '#skF_11')='#skF_11'), inference(splitRight, [status(thm)], [c_5307])).
% 8.34/2.83  tff(c_14607, plain, (![A_78233, B_78234, C_78235, D_78236]: (k7_mcart_1(A_78233, B_78234, C_78235, D_78236)=k2_mcart_1(D_78236) | ~m1_subset_1(D_78236, k3_zfmisc_1(A_78233, B_78234, C_78235)) | k1_xboole_0=C_78235 | k1_xboole_0=B_78234 | k1_xboole_0=A_78233)), inference(cnfTransformation, [status(thm)], [f_156])).
% 8.34/2.83  tff(c_14630, plain, (k7_mcart_1('#skF_8', '#skF_9', '#skF_10', '#skF_11')=k2_mcart_1('#skF_11') | k1_xboole_0='#skF_10' | k1_xboole_0='#skF_9' | k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_80, c_14607])).
% 8.34/2.83  tff(c_14636, plain, (k7_mcart_1('#skF_8', '#skF_9', '#skF_10', '#skF_11')=k2_mcart_1('#skF_11')), inference(negUnitSimplification, [status(thm)], [c_86, c_84, c_82, c_14630])).
% 8.34/2.83  tff(c_15342, plain, (![A_85566, B_85567, C_85568, D_85569]: (k3_mcart_1(k5_mcart_1(A_85566, B_85567, C_85568, D_85569), k6_mcart_1(A_85566, B_85567, C_85568, D_85569), k7_mcart_1(A_85566, B_85567, C_85568, D_85569))=D_85569 | ~m1_subset_1(D_85569, k3_zfmisc_1(A_85566, B_85567, C_85568)) | k1_xboole_0=C_85568 | k1_xboole_0=B_85567 | k1_xboole_0=A_85566)), inference(cnfTransformation, [status(thm)], [f_136])).
% 8.34/2.83  tff(c_15401, plain, (k3_mcart_1(k5_mcart_1('#skF_8', '#skF_9', '#skF_10', '#skF_11'), k6_mcart_1('#skF_8', '#skF_9', '#skF_10', '#skF_11'), k2_mcart_1('#skF_11'))='#skF_11' | ~m1_subset_1('#skF_11', k3_zfmisc_1('#skF_8', '#skF_9', '#skF_10')) | k1_xboole_0='#skF_10' | k1_xboole_0='#skF_9' | k1_xboole_0='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_14636, c_15342])).
% 8.34/2.83  tff(c_15440, plain, (k3_mcart_1(k5_mcart_1('#skF_8', '#skF_9', '#skF_10', '#skF_11'), '#skF_11', k2_mcart_1('#skF_11'))='#skF_11' | k1_xboole_0='#skF_10' | k1_xboole_0='#skF_9' | k1_xboole_0='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_10294, c_15401])).
% 8.34/2.83  tff(c_15442, plain, $false, inference(negUnitSimplification, [status(thm)], [c_86, c_84, c_82, c_11309, c_15440])).
% 8.34/2.83  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.34/2.83  
% 8.34/2.83  Inference rules
% 8.34/2.83  ----------------------
% 8.34/2.83  #Ref     : 0
% 8.34/2.83  #Sup     : 1794
% 8.34/2.83  #Fact    : 0
% 8.34/2.83  #Define  : 0
% 8.34/2.83  #Split   : 18
% 8.34/2.83  #Chain   : 0
% 8.34/2.83  #Close   : 0
% 8.34/2.83  
% 8.34/2.83  Ordering : KBO
% 8.34/2.83  
% 8.34/2.83  Simplification rules
% 8.34/2.83  ----------------------
% 8.34/2.83  #Subsume      : 504
% 8.34/2.83  #Demod        : 136
% 8.34/2.83  #Tautology    : 309
% 8.34/2.83  #SimpNegUnit  : 243
% 8.34/2.83  #BackRed      : 1
% 8.34/2.83  
% 8.34/2.83  #Partial instantiations: 38537
% 8.34/2.83  #Strategies tried      : 1
% 8.34/2.83  
% 8.34/2.83  Timing (in seconds)
% 8.34/2.83  ----------------------
% 8.34/2.83  Preprocessing        : 0.38
% 8.34/2.84  Parsing              : 0.19
% 8.34/2.84  CNF conversion       : 0.03
% 8.34/2.84  Main loop            : 1.63
% 8.34/2.84  Inferencing          : 0.93
% 8.34/2.84  Reduction            : 0.37
% 8.34/2.84  Demodulation         : 0.24
% 8.34/2.84  BG Simplification    : 0.06
% 8.34/2.84  Subsumption          : 0.19
% 8.34/2.84  Abstraction          : 0.06
% 8.34/2.84  MUC search           : 0.00
% 8.34/2.84  Cooper               : 0.00
% 8.34/2.84  Total                : 2.05
% 8.34/2.84  Index Insertion      : 0.00
% 8.34/2.84  Index Deletion       : 0.00
% 8.34/2.84  Index Matching       : 0.00
% 8.34/2.84  BG Taut test         : 0.00
%------------------------------------------------------------------------------
