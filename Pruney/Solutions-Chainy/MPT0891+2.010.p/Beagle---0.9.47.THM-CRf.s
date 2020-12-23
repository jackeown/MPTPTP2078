%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:41 EST 2020

% Result     : Theorem 6.79s
% Output     : CNFRefutation 6.98s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 240 expanded)
%              Number of leaves         :   43 ( 103 expanded)
%              Depth                    :    9
%              Number of atoms          :  208 ( 548 expanded)
%              Number of equality atoms :  148 ( 386 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k1_enumset1 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > k1_xboole_0 > #skF_5 > #skF_1 > #skF_7 > #skF_6 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_5',type,(
    '#skF_5': $i > $i )).

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

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k7_mcart_1,type,(
    k7_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_164,negated_conjecture,(
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

tff(f_56,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_39,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(f_37,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( k4_xboole_0(k2_tarski(A,B),C) = k1_xboole_0
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_zfmisc_1)).

tff(f_100,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k3_mcart_1(C,D,E) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_mcart_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_58,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_54,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_73,axiom,(
    ! [A,B,C] : k3_mcart_1(A,B,C) = k4_tarski(k4_tarski(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

tff(f_140,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_84,axiom,(
    ! [A] :
      ( ? [B,C] : A = k4_tarski(B,C)
     => ( A != k1_mcart_1(A)
        & A != k2_mcart_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_mcart_1)).

tff(f_136,axiom,(
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

tff(f_116,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & ~ ! [D] :
              ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
             => D = k3_mcart_1(k5_mcart_1(A,B,C,D),k6_mcart_1(A,B,C,D),k7_mcart_1(A,B,C,D)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_mcart_1)).

tff(c_98,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_96,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_94,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_48,plain,(
    ! [A_16] : k2_tarski(A_16,A_16) = k1_tarski(A_16) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_22,plain,(
    ! [A_8] : k4_xboole_0(k1_xboole_0,A_8) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_159,plain,(
    ! [C_81,B_82] : ~ r2_hidden(C_81,k4_xboole_0(B_82,k1_tarski(C_81))) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_162,plain,(
    ! [C_81] : ~ r2_hidden(C_81,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_159])).

tff(c_20,plain,(
    ! [A_7] : k4_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2925,plain,(
    ! [B_415,C_416,A_417] :
      ( r2_hidden(B_415,C_416)
      | k4_xboole_0(k2_tarski(A_417,B_415),C_416) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_2932,plain,(
    ! [B_415,A_417] :
      ( r2_hidden(B_415,k1_xboole_0)
      | k2_tarski(A_417,B_415) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_2925])).

tff(c_2934,plain,(
    ! [A_418,B_419] : k2_tarski(A_418,B_419) != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_162,c_2932])).

tff(c_2936,plain,(
    ! [A_16] : k1_tarski(A_16) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_2934])).

tff(c_72,plain,(
    ! [A_36] :
      ( r2_hidden('#skF_5'(A_36),A_36)
      | k1_xboole_0 = A_36 ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_2900,plain,(
    ! [D_409,A_410,B_411] :
      ( r2_hidden(D_409,A_410)
      | ~ r2_hidden(D_409,k4_xboole_0(A_410,B_411)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_5407,plain,(
    ! [A_709,B_710] :
      ( r2_hidden('#skF_5'(k4_xboole_0(A_709,B_710)),A_709)
      | k4_xboole_0(A_709,B_710) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_72,c_2900])).

tff(c_2913,plain,(
    ! [D_412,B_413,A_414] :
      ( ~ r2_hidden(D_412,B_413)
      | ~ r2_hidden(D_412,k4_xboole_0(A_414,B_413)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2924,plain,(
    ! [A_414,B_413] :
      ( ~ r2_hidden('#skF_5'(k4_xboole_0(A_414,B_413)),B_413)
      | k4_xboole_0(A_414,B_413) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_72,c_2913])).

tff(c_5430,plain,(
    ! [A_709] : k4_xboole_0(A_709,A_709) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_5407,c_2924])).

tff(c_5574,plain,(
    ! [A_733,B_734,C_735] :
      ( r2_hidden(A_733,k4_xboole_0(B_734,k1_tarski(C_735)))
      | C_735 = A_733
      | ~ r2_hidden(A_733,B_734) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_5594,plain,(
    ! [A_733,C_735] :
      ( r2_hidden(A_733,k1_xboole_0)
      | C_735 = A_733
      | ~ r2_hidden(A_733,k1_tarski(C_735)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5430,c_5574])).

tff(c_5607,plain,(
    ! [C_736,A_737] :
      ( C_736 = A_737
      | ~ r2_hidden(A_737,k1_tarski(C_736)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_162,c_5594])).

tff(c_5618,plain,(
    ! [C_736] :
      ( '#skF_5'(k1_tarski(C_736)) = C_736
      | k1_tarski(C_736) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_72,c_5607])).

tff(c_5624,plain,(
    ! [C_736] : '#skF_5'(k1_tarski(C_736)) = C_736 ),
    inference(negUnitSimplification,[status(thm)],[c_2936,c_5618])).

tff(c_171,plain,(
    ! [A_87,B_88] : k1_enumset1(A_87,A_87,B_88) = k2_tarski(A_87,B_88) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_28,plain,(
    ! [E_15,A_9,C_11] : r2_hidden(E_15,k1_enumset1(A_9,E_15,C_11)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_189,plain,(
    ! [A_89,B_90] : r2_hidden(A_89,k2_tarski(A_89,B_90)) ),
    inference(superposition,[status(thm),theory(equality)],[c_171,c_28])).

tff(c_192,plain,(
    ! [A_16] : r2_hidden(A_16,k1_tarski(A_16)) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_189])).

tff(c_5530,plain,(
    ! [D_715,A_716,C_717,E_718] :
      ( ~ r2_hidden(D_715,A_716)
      | k3_mcart_1(C_717,D_715,E_718) != '#skF_5'(A_716)
      | k1_xboole_0 = A_716 ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_5538,plain,(
    ! [C_717,A_16,E_718] :
      ( k3_mcart_1(C_717,A_16,E_718) != '#skF_5'(k1_tarski(A_16))
      | k1_tarski(A_16) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_192,c_5530])).

tff(c_5556,plain,(
    ! [C_717,A_16,E_718] : k3_mcart_1(C_717,A_16,E_718) != '#skF_5'(k1_tarski(A_16)) ),
    inference(negUnitSimplification,[status(thm)],[c_2936,c_5538])).

tff(c_5625,plain,(
    ! [C_717,A_16,E_718] : k3_mcart_1(C_717,A_16,E_718) != A_16 ),
    inference(demodulation,[status(thm),theory(equality)],[c_5624,c_5556])).

tff(c_92,plain,(
    m1_subset_1('#skF_9',k3_zfmisc_1('#skF_6','#skF_7','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_2938,plain,(
    ! [A_421,B_422,C_423] : k4_tarski(k4_tarski(A_421,B_422),C_423) = k3_mcart_1(A_421,B_422,C_423) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_88,plain,(
    ! [A_60,B_61] : k2_mcart_1(k4_tarski(A_60,B_61)) = B_61 ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_68,plain,(
    ! [B_34,C_35] : k2_mcart_1(k4_tarski(B_34,C_35)) != k4_tarski(B_34,C_35) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_100,plain,(
    ! [B_34,C_35] : k4_tarski(B_34,C_35) != C_35 ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_68])).

tff(c_2956,plain,(
    ! [A_421,B_422,C_423] : k3_mcart_1(A_421,B_422,C_423) != C_423 ),
    inference(superposition,[status(thm),theory(equality)],[c_2938,c_100])).

tff(c_267,plain,(
    ! [A_109,C_110,B_111] :
      ( r2_hidden(A_109,C_110)
      | k4_xboole_0(k2_tarski(A_109,B_111),C_110) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_274,plain,(
    ! [A_109,B_111] :
      ( r2_hidden(A_109,k1_xboole_0)
      | k2_tarski(A_109,B_111) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_267])).

tff(c_276,plain,(
    ! [A_112,B_113] : k2_tarski(A_112,B_113) != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_162,c_274])).

tff(c_278,plain,(
    ! [A_16] : k1_tarski(A_16) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_276])).

tff(c_217,plain,(
    ! [D_97,A_98,B_99] :
      ( r2_hidden(D_97,A_98)
      | ~ r2_hidden(D_97,k4_xboole_0(A_98,B_99)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_228,plain,(
    ! [A_98,B_99] :
      ( r2_hidden('#skF_5'(k4_xboole_0(A_98,B_99)),A_98)
      | k4_xboole_0(A_98,B_99) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_72,c_217])).

tff(c_205,plain,(
    ! [D_94,B_95,A_96] :
      ( ~ r2_hidden(D_94,B_95)
      | ~ r2_hidden(D_94,k4_xboole_0(A_96,B_95)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_346,plain,(
    ! [A_131,B_132] :
      ( ~ r2_hidden('#skF_5'(k4_xboole_0(A_131,B_132)),B_132)
      | k4_xboole_0(A_131,B_132) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_72,c_205])).

tff(c_357,plain,(
    ! [A_98] : k4_xboole_0(A_98,A_98) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_228,c_346])).

tff(c_501,plain,(
    ! [A_167,B_168,C_169] :
      ( r2_hidden(A_167,k4_xboole_0(B_168,k1_tarski(C_169)))
      | C_169 = A_167
      | ~ r2_hidden(A_167,B_168) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_523,plain,(
    ! [A_167,C_169] :
      ( r2_hidden(A_167,k1_xboole_0)
      | C_169 = A_167
      | ~ r2_hidden(A_167,k1_tarski(C_169)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_357,c_501])).

tff(c_537,plain,(
    ! [C_170,A_171] :
      ( C_170 = A_171
      | ~ r2_hidden(A_171,k1_tarski(C_170)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_162,c_523])).

tff(c_548,plain,(
    ! [C_170] :
      ( '#skF_5'(k1_tarski(C_170)) = C_170
      | k1_tarski(C_170) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_72,c_537])).

tff(c_554,plain,(
    ! [C_170] : '#skF_5'(k1_tarski(C_170)) = C_170 ),
    inference(negUnitSimplification,[status(thm)],[c_278,c_548])).

tff(c_461,plain,(
    ! [C_152,A_153,D_154,E_155] :
      ( ~ r2_hidden(C_152,A_153)
      | k3_mcart_1(C_152,D_154,E_155) != '#skF_5'(A_153)
      | k1_xboole_0 = A_153 ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_467,plain,(
    ! [A_16,D_154,E_155] :
      ( k3_mcart_1(A_16,D_154,E_155) != '#skF_5'(k1_tarski(A_16))
      | k1_tarski(A_16) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_192,c_461])).

tff(c_484,plain,(
    ! [A_16,D_154,E_155] : k3_mcart_1(A_16,D_154,E_155) != '#skF_5'(k1_tarski(A_16)) ),
    inference(negUnitSimplification,[status(thm)],[c_278,c_467])).

tff(c_555,plain,(
    ! [A_16,D_154,E_155] : k3_mcart_1(A_16,D_154,E_155) != A_16 ),
    inference(demodulation,[status(thm),theory(equality)],[c_554,c_484])).

tff(c_90,plain,
    ( k7_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9') = '#skF_9'
    | k6_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9') = '#skF_9'
    | k5_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9') = '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_193,plain,(
    k5_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9') = '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_90])).

tff(c_1690,plain,(
    ! [A_319,B_320,C_321,D_322] :
      ( k7_mcart_1(A_319,B_320,C_321,D_322) = k2_mcart_1(D_322)
      | ~ m1_subset_1(D_322,k3_zfmisc_1(A_319,B_320,C_321))
      | k1_xboole_0 = C_321
      | k1_xboole_0 = B_320
      | k1_xboole_0 = A_319 ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_1696,plain,
    ( k7_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9') = k2_mcart_1('#skF_9')
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_92,c_1690])).

tff(c_1699,plain,(
    k7_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9') = k2_mcart_1('#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_96,c_94,c_1696])).

tff(c_2799,plain,(
    ! [A_402,B_403,C_404,D_405] :
      ( k3_mcart_1(k5_mcart_1(A_402,B_403,C_404,D_405),k6_mcart_1(A_402,B_403,C_404,D_405),k7_mcart_1(A_402,B_403,C_404,D_405)) = D_405
      | ~ m1_subset_1(D_405,k3_zfmisc_1(A_402,B_403,C_404))
      | k1_xboole_0 = C_404
      | k1_xboole_0 = B_403
      | k1_xboole_0 = A_402 ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_2877,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9'),k6_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9'),k2_mcart_1('#skF_9')) = '#skF_9'
    | ~ m1_subset_1('#skF_9',k3_zfmisc_1('#skF_6','#skF_7','#skF_8'))
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_1699,c_2799])).

tff(c_2888,plain,
    ( k3_mcart_1('#skF_9',k6_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9'),k2_mcart_1('#skF_9')) = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_193,c_2877])).

tff(c_2890,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_96,c_94,c_555,c_2888])).

tff(c_2891,plain,
    ( k6_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9') = '#skF_9'
    | k7_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9') = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_90])).

tff(c_2976,plain,(
    k7_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9') = '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_2891])).

tff(c_5273,plain,(
    ! [A_692,B_693,C_694,D_695] :
      ( k3_mcart_1(k5_mcart_1(A_692,B_693,C_694,D_695),k6_mcart_1(A_692,B_693,C_694,D_695),k7_mcart_1(A_692,B_693,C_694,D_695)) = D_695
      | ~ m1_subset_1(D_695,k3_zfmisc_1(A_692,B_693,C_694))
      | k1_xboole_0 = C_694
      | k1_xboole_0 = B_693
      | k1_xboole_0 = A_692 ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_5342,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9'),k6_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9'),'#skF_9') = '#skF_9'
    | ~ m1_subset_1('#skF_9',k3_zfmisc_1('#skF_6','#skF_7','#skF_8'))
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_2976,c_5273])).

tff(c_5350,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9'),k6_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9'),'#skF_9') = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_5342])).

tff(c_5352,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_96,c_94,c_2956,c_5350])).

tff(c_5353,plain,(
    k6_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9') = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_2891])).

tff(c_6805,plain,(
    ! [A_898,B_899,C_900,D_901] :
      ( k7_mcart_1(A_898,B_899,C_900,D_901) = k2_mcart_1(D_901)
      | ~ m1_subset_1(D_901,k3_zfmisc_1(A_898,B_899,C_900))
      | k1_xboole_0 = C_900
      | k1_xboole_0 = B_899
      | k1_xboole_0 = A_898 ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_6811,plain,
    ( k7_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9') = k2_mcart_1('#skF_9')
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_92,c_6805])).

tff(c_6814,plain,(
    k7_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9') = k2_mcart_1('#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_96,c_94,c_6811])).

tff(c_7898,plain,(
    ! [A_995,B_996,C_997,D_998] :
      ( k3_mcart_1(k5_mcart_1(A_995,B_996,C_997,D_998),k6_mcart_1(A_995,B_996,C_997,D_998),k7_mcart_1(A_995,B_996,C_997,D_998)) = D_998
      | ~ m1_subset_1(D_998,k3_zfmisc_1(A_995,B_996,C_997))
      | k1_xboole_0 = C_997
      | k1_xboole_0 = B_996
      | k1_xboole_0 = A_995 ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_7982,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9'),k6_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9'),k2_mcart_1('#skF_9')) = '#skF_9'
    | ~ m1_subset_1('#skF_9',k3_zfmisc_1('#skF_6','#skF_7','#skF_8'))
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_6814,c_7898])).

tff(c_7993,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9'),'#skF_9',k2_mcart_1('#skF_9')) = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_5353,c_7982])).

tff(c_7995,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_96,c_94,c_5625,c_7993])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:26:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.79/2.40  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.90/2.41  
% 6.90/2.41  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.90/2.41  %$ r2_hidden > m1_subset_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k1_enumset1 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > k1_xboole_0 > #skF_5 > #skF_1 > #skF_7 > #skF_6 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_3
% 6.90/2.41  
% 6.90/2.41  %Foreground sorts:
% 6.90/2.41  
% 6.90/2.41  
% 6.90/2.41  %Background operators:
% 6.90/2.41  
% 6.90/2.41  
% 6.90/2.41  %Foreground operators:
% 6.90/2.41  tff('#skF_5', type, '#skF_5': $i > $i).
% 6.90/2.41  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 6.90/2.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.90/2.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.90/2.41  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.90/2.41  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.90/2.41  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 6.90/2.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.90/2.41  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 6.90/2.41  tff('#skF_7', type, '#skF_7': $i).
% 6.90/2.41  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.90/2.41  tff('#skF_6', type, '#skF_6': $i).
% 6.90/2.41  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.90/2.41  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 6.90/2.41  tff('#skF_9', type, '#skF_9': $i).
% 6.90/2.41  tff(k7_mcart_1, type, k7_mcart_1: ($i * $i * $i * $i) > $i).
% 6.90/2.41  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 6.90/2.41  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 6.90/2.41  tff('#skF_8', type, '#skF_8': $i).
% 6.90/2.41  tff(k5_mcart_1, type, k5_mcart_1: ($i * $i * $i * $i) > $i).
% 6.90/2.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.90/2.41  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 6.90/2.41  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.90/2.41  tff(k6_mcart_1, type, k6_mcart_1: ($i * $i * $i * $i) > $i).
% 6.90/2.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.90/2.41  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 6.90/2.41  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 6.90/2.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.90/2.41  
% 6.98/2.43  tff(f_164, negated_conjecture, ~(![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => ((~(D = k5_mcart_1(A, B, C, D)) & ~(D = k6_mcart_1(A, B, C, D))) & ~(D = k7_mcart_1(A, B, C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_mcart_1)).
% 6.98/2.43  tff(f_56, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 6.98/2.43  tff(f_39, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 6.98/2.43  tff(f_65, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 6.98/2.43  tff(f_37, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 6.98/2.43  tff(f_71, axiom, (![A, B, C]: ((k4_xboole_0(k2_tarski(A, B), C) = k1_xboole_0) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_zfmisc_1)).
% 6.98/2.43  tff(f_100, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k3_mcart_1(C, D, E)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_mcart_1)).
% 6.98/2.43  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 6.98/2.43  tff(f_58, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 6.98/2.43  tff(f_54, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 6.98/2.43  tff(f_73, axiom, (![A, B, C]: (k3_mcart_1(A, B, C) = k4_tarski(k4_tarski(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_mcart_1)).
% 6.98/2.43  tff(f_140, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 6.98/2.43  tff(f_84, axiom, (![A]: ((?[B, C]: (A = k4_tarski(B, C))) => (~(A = k1_mcart_1(A)) & ~(A = k2_mcart_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_mcart_1)).
% 6.98/2.43  tff(f_136, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => (((k5_mcart_1(A, B, C, D) = k1_mcart_1(k1_mcart_1(D))) & (k6_mcart_1(A, B, C, D) = k2_mcart_1(k1_mcart_1(D)))) & (k7_mcart_1(A, B, C, D) = k2_mcart_1(D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_mcart_1)).
% 6.98/2.43  tff(f_116, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => (D = k3_mcart_1(k5_mcart_1(A, B, C, D), k6_mcart_1(A, B, C, D), k7_mcart_1(A, B, C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_mcart_1)).
% 6.98/2.43  tff(c_98, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_164])).
% 6.98/2.43  tff(c_96, plain, (k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_164])).
% 6.98/2.43  tff(c_94, plain, (k1_xboole_0!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_164])).
% 6.98/2.43  tff(c_48, plain, (![A_16]: (k2_tarski(A_16, A_16)=k1_tarski(A_16))), inference(cnfTransformation, [status(thm)], [f_56])).
% 6.98/2.43  tff(c_22, plain, (![A_8]: (k4_xboole_0(k1_xboole_0, A_8)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.98/2.43  tff(c_159, plain, (![C_81, B_82]: (~r2_hidden(C_81, k4_xboole_0(B_82, k1_tarski(C_81))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.98/2.43  tff(c_162, plain, (![C_81]: (~r2_hidden(C_81, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_22, c_159])).
% 6.98/2.43  tff(c_20, plain, (![A_7]: (k4_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.98/2.43  tff(c_2925, plain, (![B_415, C_416, A_417]: (r2_hidden(B_415, C_416) | k4_xboole_0(k2_tarski(A_417, B_415), C_416)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_71])).
% 6.98/2.43  tff(c_2932, plain, (![B_415, A_417]: (r2_hidden(B_415, k1_xboole_0) | k2_tarski(A_417, B_415)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_20, c_2925])).
% 6.98/2.43  tff(c_2934, plain, (![A_418, B_419]: (k2_tarski(A_418, B_419)!=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_162, c_2932])).
% 6.98/2.43  tff(c_2936, plain, (![A_16]: (k1_tarski(A_16)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_48, c_2934])).
% 6.98/2.43  tff(c_72, plain, (![A_36]: (r2_hidden('#skF_5'(A_36), A_36) | k1_xboole_0=A_36)), inference(cnfTransformation, [status(thm)], [f_100])).
% 6.98/2.43  tff(c_2900, plain, (![D_409, A_410, B_411]: (r2_hidden(D_409, A_410) | ~r2_hidden(D_409, k4_xboole_0(A_410, B_411)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.98/2.43  tff(c_5407, plain, (![A_709, B_710]: (r2_hidden('#skF_5'(k4_xboole_0(A_709, B_710)), A_709) | k4_xboole_0(A_709, B_710)=k1_xboole_0)), inference(resolution, [status(thm)], [c_72, c_2900])).
% 6.98/2.43  tff(c_2913, plain, (![D_412, B_413, A_414]: (~r2_hidden(D_412, B_413) | ~r2_hidden(D_412, k4_xboole_0(A_414, B_413)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.98/2.43  tff(c_2924, plain, (![A_414, B_413]: (~r2_hidden('#skF_5'(k4_xboole_0(A_414, B_413)), B_413) | k4_xboole_0(A_414, B_413)=k1_xboole_0)), inference(resolution, [status(thm)], [c_72, c_2913])).
% 6.98/2.43  tff(c_5430, plain, (![A_709]: (k4_xboole_0(A_709, A_709)=k1_xboole_0)), inference(resolution, [status(thm)], [c_5407, c_2924])).
% 6.98/2.43  tff(c_5574, plain, (![A_733, B_734, C_735]: (r2_hidden(A_733, k4_xboole_0(B_734, k1_tarski(C_735))) | C_735=A_733 | ~r2_hidden(A_733, B_734))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.98/2.43  tff(c_5594, plain, (![A_733, C_735]: (r2_hidden(A_733, k1_xboole_0) | C_735=A_733 | ~r2_hidden(A_733, k1_tarski(C_735)))), inference(superposition, [status(thm), theory('equality')], [c_5430, c_5574])).
% 6.98/2.43  tff(c_5607, plain, (![C_736, A_737]: (C_736=A_737 | ~r2_hidden(A_737, k1_tarski(C_736)))), inference(negUnitSimplification, [status(thm)], [c_162, c_5594])).
% 6.98/2.43  tff(c_5618, plain, (![C_736]: ('#skF_5'(k1_tarski(C_736))=C_736 | k1_tarski(C_736)=k1_xboole_0)), inference(resolution, [status(thm)], [c_72, c_5607])).
% 6.98/2.43  tff(c_5624, plain, (![C_736]: ('#skF_5'(k1_tarski(C_736))=C_736)), inference(negUnitSimplification, [status(thm)], [c_2936, c_5618])).
% 6.98/2.43  tff(c_171, plain, (![A_87, B_88]: (k1_enumset1(A_87, A_87, B_88)=k2_tarski(A_87, B_88))), inference(cnfTransformation, [status(thm)], [f_58])).
% 6.98/2.43  tff(c_28, plain, (![E_15, A_9, C_11]: (r2_hidden(E_15, k1_enumset1(A_9, E_15, C_11)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 6.98/2.43  tff(c_189, plain, (![A_89, B_90]: (r2_hidden(A_89, k2_tarski(A_89, B_90)))), inference(superposition, [status(thm), theory('equality')], [c_171, c_28])).
% 6.98/2.43  tff(c_192, plain, (![A_16]: (r2_hidden(A_16, k1_tarski(A_16)))), inference(superposition, [status(thm), theory('equality')], [c_48, c_189])).
% 6.98/2.43  tff(c_5530, plain, (![D_715, A_716, C_717, E_718]: (~r2_hidden(D_715, A_716) | k3_mcart_1(C_717, D_715, E_718)!='#skF_5'(A_716) | k1_xboole_0=A_716)), inference(cnfTransformation, [status(thm)], [f_100])).
% 6.98/2.43  tff(c_5538, plain, (![C_717, A_16, E_718]: (k3_mcart_1(C_717, A_16, E_718)!='#skF_5'(k1_tarski(A_16)) | k1_tarski(A_16)=k1_xboole_0)), inference(resolution, [status(thm)], [c_192, c_5530])).
% 6.98/2.43  tff(c_5556, plain, (![C_717, A_16, E_718]: (k3_mcart_1(C_717, A_16, E_718)!='#skF_5'(k1_tarski(A_16)))), inference(negUnitSimplification, [status(thm)], [c_2936, c_5538])).
% 6.98/2.43  tff(c_5625, plain, (![C_717, A_16, E_718]: (k3_mcart_1(C_717, A_16, E_718)!=A_16)), inference(demodulation, [status(thm), theory('equality')], [c_5624, c_5556])).
% 6.98/2.43  tff(c_92, plain, (m1_subset_1('#skF_9', k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_164])).
% 6.98/2.43  tff(c_2938, plain, (![A_421, B_422, C_423]: (k4_tarski(k4_tarski(A_421, B_422), C_423)=k3_mcart_1(A_421, B_422, C_423))), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.98/2.43  tff(c_88, plain, (![A_60, B_61]: (k2_mcart_1(k4_tarski(A_60, B_61))=B_61)), inference(cnfTransformation, [status(thm)], [f_140])).
% 6.98/2.43  tff(c_68, plain, (![B_34, C_35]: (k2_mcart_1(k4_tarski(B_34, C_35))!=k4_tarski(B_34, C_35))), inference(cnfTransformation, [status(thm)], [f_84])).
% 6.98/2.43  tff(c_100, plain, (![B_34, C_35]: (k4_tarski(B_34, C_35)!=C_35)), inference(demodulation, [status(thm), theory('equality')], [c_88, c_68])).
% 6.98/2.43  tff(c_2956, plain, (![A_421, B_422, C_423]: (k3_mcart_1(A_421, B_422, C_423)!=C_423)), inference(superposition, [status(thm), theory('equality')], [c_2938, c_100])).
% 6.98/2.43  tff(c_267, plain, (![A_109, C_110, B_111]: (r2_hidden(A_109, C_110) | k4_xboole_0(k2_tarski(A_109, B_111), C_110)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_71])).
% 6.98/2.43  tff(c_274, plain, (![A_109, B_111]: (r2_hidden(A_109, k1_xboole_0) | k2_tarski(A_109, B_111)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_20, c_267])).
% 6.98/2.43  tff(c_276, plain, (![A_112, B_113]: (k2_tarski(A_112, B_113)!=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_162, c_274])).
% 6.98/2.43  tff(c_278, plain, (![A_16]: (k1_tarski(A_16)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_48, c_276])).
% 6.98/2.43  tff(c_217, plain, (![D_97, A_98, B_99]: (r2_hidden(D_97, A_98) | ~r2_hidden(D_97, k4_xboole_0(A_98, B_99)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.98/2.43  tff(c_228, plain, (![A_98, B_99]: (r2_hidden('#skF_5'(k4_xboole_0(A_98, B_99)), A_98) | k4_xboole_0(A_98, B_99)=k1_xboole_0)), inference(resolution, [status(thm)], [c_72, c_217])).
% 6.98/2.43  tff(c_205, plain, (![D_94, B_95, A_96]: (~r2_hidden(D_94, B_95) | ~r2_hidden(D_94, k4_xboole_0(A_96, B_95)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.98/2.43  tff(c_346, plain, (![A_131, B_132]: (~r2_hidden('#skF_5'(k4_xboole_0(A_131, B_132)), B_132) | k4_xboole_0(A_131, B_132)=k1_xboole_0)), inference(resolution, [status(thm)], [c_72, c_205])).
% 6.98/2.43  tff(c_357, plain, (![A_98]: (k4_xboole_0(A_98, A_98)=k1_xboole_0)), inference(resolution, [status(thm)], [c_228, c_346])).
% 6.98/2.43  tff(c_501, plain, (![A_167, B_168, C_169]: (r2_hidden(A_167, k4_xboole_0(B_168, k1_tarski(C_169))) | C_169=A_167 | ~r2_hidden(A_167, B_168))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.98/2.43  tff(c_523, plain, (![A_167, C_169]: (r2_hidden(A_167, k1_xboole_0) | C_169=A_167 | ~r2_hidden(A_167, k1_tarski(C_169)))), inference(superposition, [status(thm), theory('equality')], [c_357, c_501])).
% 6.98/2.43  tff(c_537, plain, (![C_170, A_171]: (C_170=A_171 | ~r2_hidden(A_171, k1_tarski(C_170)))), inference(negUnitSimplification, [status(thm)], [c_162, c_523])).
% 6.98/2.43  tff(c_548, plain, (![C_170]: ('#skF_5'(k1_tarski(C_170))=C_170 | k1_tarski(C_170)=k1_xboole_0)), inference(resolution, [status(thm)], [c_72, c_537])).
% 6.98/2.43  tff(c_554, plain, (![C_170]: ('#skF_5'(k1_tarski(C_170))=C_170)), inference(negUnitSimplification, [status(thm)], [c_278, c_548])).
% 6.98/2.43  tff(c_461, plain, (![C_152, A_153, D_154, E_155]: (~r2_hidden(C_152, A_153) | k3_mcart_1(C_152, D_154, E_155)!='#skF_5'(A_153) | k1_xboole_0=A_153)), inference(cnfTransformation, [status(thm)], [f_100])).
% 6.98/2.43  tff(c_467, plain, (![A_16, D_154, E_155]: (k3_mcart_1(A_16, D_154, E_155)!='#skF_5'(k1_tarski(A_16)) | k1_tarski(A_16)=k1_xboole_0)), inference(resolution, [status(thm)], [c_192, c_461])).
% 6.98/2.43  tff(c_484, plain, (![A_16, D_154, E_155]: (k3_mcart_1(A_16, D_154, E_155)!='#skF_5'(k1_tarski(A_16)))), inference(negUnitSimplification, [status(thm)], [c_278, c_467])).
% 6.98/2.43  tff(c_555, plain, (![A_16, D_154, E_155]: (k3_mcart_1(A_16, D_154, E_155)!=A_16)), inference(demodulation, [status(thm), theory('equality')], [c_554, c_484])).
% 6.98/2.43  tff(c_90, plain, (k7_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9')='#skF_9' | k6_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9')='#skF_9' | k5_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9')='#skF_9'), inference(cnfTransformation, [status(thm)], [f_164])).
% 6.98/2.43  tff(c_193, plain, (k5_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9')='#skF_9'), inference(splitLeft, [status(thm)], [c_90])).
% 6.98/2.43  tff(c_1690, plain, (![A_319, B_320, C_321, D_322]: (k7_mcart_1(A_319, B_320, C_321, D_322)=k2_mcart_1(D_322) | ~m1_subset_1(D_322, k3_zfmisc_1(A_319, B_320, C_321)) | k1_xboole_0=C_321 | k1_xboole_0=B_320 | k1_xboole_0=A_319)), inference(cnfTransformation, [status(thm)], [f_136])).
% 6.98/2.43  tff(c_1696, plain, (k7_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9')=k2_mcart_1('#skF_9') | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_92, c_1690])).
% 6.98/2.43  tff(c_1699, plain, (k7_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9')=k2_mcart_1('#skF_9')), inference(negUnitSimplification, [status(thm)], [c_98, c_96, c_94, c_1696])).
% 6.98/2.43  tff(c_2799, plain, (![A_402, B_403, C_404, D_405]: (k3_mcart_1(k5_mcart_1(A_402, B_403, C_404, D_405), k6_mcart_1(A_402, B_403, C_404, D_405), k7_mcart_1(A_402, B_403, C_404, D_405))=D_405 | ~m1_subset_1(D_405, k3_zfmisc_1(A_402, B_403, C_404)) | k1_xboole_0=C_404 | k1_xboole_0=B_403 | k1_xboole_0=A_402)), inference(cnfTransformation, [status(thm)], [f_116])).
% 6.98/2.43  tff(c_2877, plain, (k3_mcart_1(k5_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'), k6_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'), k2_mcart_1('#skF_9'))='#skF_9' | ~m1_subset_1('#skF_9', k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8')) | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_1699, c_2799])).
% 6.98/2.43  tff(c_2888, plain, (k3_mcart_1('#skF_9', k6_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'), k2_mcart_1('#skF_9'))='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_92, c_193, c_2877])).
% 6.98/2.43  tff(c_2890, plain, $false, inference(negUnitSimplification, [status(thm)], [c_98, c_96, c_94, c_555, c_2888])).
% 6.98/2.43  tff(c_2891, plain, (k6_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9')='#skF_9' | k7_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9')='#skF_9'), inference(splitRight, [status(thm)], [c_90])).
% 6.98/2.43  tff(c_2976, plain, (k7_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9')='#skF_9'), inference(splitLeft, [status(thm)], [c_2891])).
% 6.98/2.43  tff(c_5273, plain, (![A_692, B_693, C_694, D_695]: (k3_mcart_1(k5_mcart_1(A_692, B_693, C_694, D_695), k6_mcart_1(A_692, B_693, C_694, D_695), k7_mcart_1(A_692, B_693, C_694, D_695))=D_695 | ~m1_subset_1(D_695, k3_zfmisc_1(A_692, B_693, C_694)) | k1_xboole_0=C_694 | k1_xboole_0=B_693 | k1_xboole_0=A_692)), inference(cnfTransformation, [status(thm)], [f_116])).
% 6.98/2.43  tff(c_5342, plain, (k3_mcart_1(k5_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'), k6_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'), '#skF_9')='#skF_9' | ~m1_subset_1('#skF_9', k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8')) | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_2976, c_5273])).
% 6.98/2.43  tff(c_5350, plain, (k3_mcart_1(k5_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'), k6_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'), '#skF_9')='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_92, c_5342])).
% 6.98/2.43  tff(c_5352, plain, $false, inference(negUnitSimplification, [status(thm)], [c_98, c_96, c_94, c_2956, c_5350])).
% 6.98/2.43  tff(c_5353, plain, (k6_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9')='#skF_9'), inference(splitRight, [status(thm)], [c_2891])).
% 6.98/2.43  tff(c_6805, plain, (![A_898, B_899, C_900, D_901]: (k7_mcart_1(A_898, B_899, C_900, D_901)=k2_mcart_1(D_901) | ~m1_subset_1(D_901, k3_zfmisc_1(A_898, B_899, C_900)) | k1_xboole_0=C_900 | k1_xboole_0=B_899 | k1_xboole_0=A_898)), inference(cnfTransformation, [status(thm)], [f_136])).
% 6.98/2.43  tff(c_6811, plain, (k7_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9')=k2_mcart_1('#skF_9') | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_92, c_6805])).
% 6.98/2.43  tff(c_6814, plain, (k7_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9')=k2_mcart_1('#skF_9')), inference(negUnitSimplification, [status(thm)], [c_98, c_96, c_94, c_6811])).
% 6.98/2.43  tff(c_7898, plain, (![A_995, B_996, C_997, D_998]: (k3_mcart_1(k5_mcart_1(A_995, B_996, C_997, D_998), k6_mcart_1(A_995, B_996, C_997, D_998), k7_mcart_1(A_995, B_996, C_997, D_998))=D_998 | ~m1_subset_1(D_998, k3_zfmisc_1(A_995, B_996, C_997)) | k1_xboole_0=C_997 | k1_xboole_0=B_996 | k1_xboole_0=A_995)), inference(cnfTransformation, [status(thm)], [f_116])).
% 6.98/2.43  tff(c_7982, plain, (k3_mcart_1(k5_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'), k6_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'), k2_mcart_1('#skF_9'))='#skF_9' | ~m1_subset_1('#skF_9', k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8')) | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_6814, c_7898])).
% 6.98/2.43  tff(c_7993, plain, (k3_mcart_1(k5_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'), '#skF_9', k2_mcart_1('#skF_9'))='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_92, c_5353, c_7982])).
% 6.98/2.43  tff(c_7995, plain, $false, inference(negUnitSimplification, [status(thm)], [c_98, c_96, c_94, c_5625, c_7993])).
% 6.98/2.43  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.98/2.43  
% 6.98/2.43  Inference rules
% 6.98/2.43  ----------------------
% 6.98/2.43  #Ref     : 18
% 6.98/2.43  #Sup     : 1709
% 6.98/2.43  #Fact    : 12
% 6.98/2.43  #Define  : 0
% 6.98/2.43  #Split   : 2
% 6.98/2.43  #Chain   : 0
% 6.98/2.43  #Close   : 0
% 6.98/2.43  
% 6.98/2.43  Ordering : KBO
% 6.98/2.43  
% 6.98/2.43  Simplification rules
% 6.98/2.43  ----------------------
% 6.98/2.43  #Subsume      : 429
% 6.98/2.43  #Demod        : 570
% 6.98/2.43  #Tautology    : 512
% 6.98/2.43  #SimpNegUnit  : 287
% 6.98/2.43  #BackRed      : 5
% 6.98/2.43  
% 6.98/2.43  #Partial instantiations: 0
% 6.98/2.43  #Strategies tried      : 1
% 6.98/2.43  
% 6.98/2.43  Timing (in seconds)
% 6.98/2.43  ----------------------
% 6.98/2.43  Preprocessing        : 0.35
% 6.98/2.43  Parsing              : 0.17
% 6.98/2.43  CNF conversion       : 0.03
% 6.98/2.43  Main loop            : 1.25
% 6.98/2.43  Inferencing          : 0.42
% 6.98/2.43  Reduction            : 0.40
% 6.98/2.43  Demodulation         : 0.26
% 6.98/2.43  BG Simplification    : 0.06
% 6.98/2.43  Subsumption          : 0.27
% 6.98/2.43  Abstraction          : 0.08
% 6.98/2.43  MUC search           : 0.00
% 6.98/2.43  Cooper               : 0.00
% 6.98/2.43  Total                : 1.64
% 6.98/2.43  Index Insertion      : 0.00
% 6.98/2.43  Index Deletion       : 0.00
% 6.98/2.43  Index Matching       : 0.00
% 6.98/2.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
