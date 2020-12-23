%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0918+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:04 EST 2020

% Result     : Theorem 2.70s
% Output     : CNFRefutation 2.70s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 145 expanded)
%              Number of leaves         :   45 (  76 expanded)
%              Depth                    :    6
%              Number of atoms          :  205 ( 557 expanded)
%              Number of equality atoms :  155 ( 473 expanded)
%              Maximal formula depth    :   22 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > k9_mcart_1 > k8_mcart_1 > k11_mcart_1 > k10_mcart_1 > k4_zfmisc_1 > k4_mcart_1 > #nlpp > k1_xboole_0 > #skF_10 > #skF_15 > #skF_9 > #skF_20 > #skF_18 > #skF_2 > #skF_17 > #skF_1 > #skF_25 > #skF_14 > #skF_13 > #skF_19 > #skF_11 > #skF_8 > #skF_12 > #skF_7 > #skF_21 > #skF_3 > #skF_5 > #skF_22 > #skF_24 > #skF_23 > #skF_16 > #skF_6 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_10',type,(
    '#skF_10': ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_15',type,(
    '#skF_15': ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_20',type,(
    '#skF_20': $i )).

tff('#skF_18',type,(
    '#skF_18': $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_17',type,(
    '#skF_17': $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k10_mcart_1,type,(
    k10_mcart_1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_25',type,(
    '#skF_25': $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_14',type,(
    '#skF_14': ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_13',type,(
    '#skF_13': ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k4_zfmisc_1,type,(
    k4_zfmisc_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_19',type,(
    '#skF_19': $i )).

tff('#skF_11',type,(
    '#skF_11': ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k11_mcart_1,type,(
    k11_mcart_1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_12',type,(
    '#skF_12': ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_21',type,(
    '#skF_21': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k8_mcart_1,type,(
    k8_mcart_1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_22',type,(
    '#skF_22': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_24',type,(
    '#skF_24': $i )).

tff('#skF_23',type,(
    '#skF_23': $i )).

tff('#skF_16',type,(
    '#skF_16': ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k9_mcart_1,type,(
    k9_mcart_1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k4_mcart_1,type,(
    k4_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_176,negated_conjecture,(
    ~ ! [A,B,C,D,E] :
        ( m1_subset_1(E,k4_zfmisc_1(A,B,C,D))
       => ~ ( A != k1_xboole_0
            & B != k1_xboole_0
            & C != k1_xboole_0
            & D != k1_xboole_0
            & ? [F,G,H,I] :
                ( E = k4_mcart_1(F,G,H,I)
                & ~ ( k8_mcart_1(A,B,C,D,E) = F
                    & k9_mcart_1(A,B,C,D,E) = G
                    & k10_mcart_1(A,B,C,D,E) = H
                    & k11_mcart_1(A,B,C,D,E) = I ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_mcart_1)).

tff(f_144,axiom,(
    ! [A,B,C,D,E] :
      ( m1_subset_1(E,k4_zfmisc_1(A,B,C,D))
     => m1_subset_1(k8_mcart_1(A,B,C,D,E),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_mcart_1)).

tff(f_105,axiom,(
    ! [A,B,C,D] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & D != k1_xboole_0
        & ~ ! [E] :
              ( m1_subset_1(E,k4_zfmisc_1(A,B,C,D))
             => ! [F] :
                  ( m1_subset_1(F,A)
                 => ( F = k8_mcart_1(A,B,C,D,E)
                  <=> ! [G,H,I,J] :
                        ( E = k4_mcart_1(G,H,I,J)
                       => F = G ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_mcart_1)).

tff(f_140,axiom,(
    ! [A,B,C,D,E] :
      ( m1_subset_1(E,k4_zfmisc_1(A,B,C,D))
     => m1_subset_1(k11_mcart_1(A,B,C,D,E),D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k11_mcart_1)).

tff(f_78,axiom,(
    ! [A,B,C,D] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & D != k1_xboole_0
        & ~ ! [E] :
              ( m1_subset_1(E,k4_zfmisc_1(A,B,C,D))
             => ! [F] :
                  ( m1_subset_1(F,D)
                 => ( F = k11_mcart_1(A,B,C,D,E)
                  <=> ! [G,H,I,J] :
                        ( E = k4_mcart_1(G,H,I,J)
                       => F = J ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_mcart_1)).

tff(f_148,axiom,(
    ! [A,B,C,D,E] :
      ( m1_subset_1(E,k4_zfmisc_1(A,B,C,D))
     => m1_subset_1(k9_mcart_1(A,B,C,D,E),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_mcart_1)).

tff(f_132,axiom,(
    ! [A,B,C,D] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & D != k1_xboole_0
        & ~ ! [E] :
              ( m1_subset_1(E,k4_zfmisc_1(A,B,C,D))
             => ! [F] :
                  ( m1_subset_1(F,B)
                 => ( F = k9_mcart_1(A,B,C,D,E)
                  <=> ! [G,H,I,J] :
                        ( E = k4_mcart_1(G,H,I,J)
                       => F = H ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_mcart_1)).

tff(f_136,axiom,(
    ! [A,B,C,D,E] :
      ( m1_subset_1(E,k4_zfmisc_1(A,B,C,D))
     => m1_subset_1(k10_mcart_1(A,B,C,D,E),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k10_mcart_1)).

tff(f_51,axiom,(
    ! [A,B,C,D] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & D != k1_xboole_0
        & ~ ! [E] :
              ( m1_subset_1(E,k4_zfmisc_1(A,B,C,D))
             => ! [F] :
                  ( m1_subset_1(F,C)
                 => ( F = k10_mcart_1(A,B,C,D,E)
                  <=> ! [G,H,I,J] :
                        ( E = k4_mcart_1(G,H,I,J)
                       => F = I ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_mcart_1)).

tff(c_44,plain,(
    k1_xboole_0 != '#skF_17' ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_42,plain,(
    k1_xboole_0 != '#skF_18' ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_40,plain,(
    k1_xboole_0 != '#skF_19' ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_38,plain,(
    k1_xboole_0 != '#skF_20' ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_34,plain,
    ( k11_mcart_1('#skF_17','#skF_18','#skF_19','#skF_20','#skF_21') != '#skF_25'
    | k10_mcart_1('#skF_17','#skF_18','#skF_19','#skF_20','#skF_21') != '#skF_24'
    | k9_mcart_1('#skF_17','#skF_18','#skF_19','#skF_20','#skF_21') != '#skF_23'
    | k8_mcart_1('#skF_17','#skF_18','#skF_19','#skF_20','#skF_21') != '#skF_22' ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_54,plain,(
    k8_mcart_1('#skF_17','#skF_18','#skF_19','#skF_20','#skF_21') != '#skF_22' ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_46,plain,(
    m1_subset_1('#skF_21',k4_zfmisc_1('#skF_17','#skF_18','#skF_19','#skF_20')) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_36,plain,(
    k4_mcart_1('#skF_22','#skF_23','#skF_24','#skF_25') = '#skF_21' ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_30,plain,(
    ! [B_292,C_293,A_291,D_294,E_295] :
      ( m1_subset_1(k8_mcart_1(A_291,B_292,C_293,D_294,E_295),A_291)
      | ~ m1_subset_1(E_295,k4_zfmisc_1(A_291,B_292,C_293,D_294)) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_153,plain,(
    ! [C_412,J_409,A_415,B_413,I_414,G_416,D_411,H_410] :
      ( k8_mcart_1(A_415,B_413,C_412,D_411,k4_mcart_1(G_416,H_410,I_414,J_409)) = G_416
      | ~ m1_subset_1(k8_mcart_1(A_415,B_413,C_412,D_411,k4_mcart_1(G_416,H_410,I_414,J_409)),A_415)
      | ~ m1_subset_1(k4_mcart_1(G_416,H_410,I_414,J_409),k4_zfmisc_1(A_415,B_413,C_412,D_411))
      | k1_xboole_0 = D_411
      | k1_xboole_0 = C_412
      | k1_xboole_0 = B_413
      | k1_xboole_0 = A_415 ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_193,plain,(
    ! [G_430,D_424,I_429,J_427,C_428,A_425,B_423,H_426] :
      ( k8_mcart_1(A_425,B_423,C_428,D_424,k4_mcart_1(G_430,H_426,I_429,J_427)) = G_430
      | k1_xboole_0 = D_424
      | k1_xboole_0 = C_428
      | k1_xboole_0 = B_423
      | k1_xboole_0 = A_425
      | ~ m1_subset_1(k4_mcart_1(G_430,H_426,I_429,J_427),k4_zfmisc_1(A_425,B_423,C_428,D_424)) ) ),
    inference(resolution,[status(thm)],[c_30,c_153])).

tff(c_199,plain,(
    ! [A_425,B_423,C_428,D_424] :
      ( k8_mcart_1(A_425,B_423,C_428,D_424,k4_mcart_1('#skF_22','#skF_23','#skF_24','#skF_25')) = '#skF_22'
      | k1_xboole_0 = D_424
      | k1_xboole_0 = C_428
      | k1_xboole_0 = B_423
      | k1_xboole_0 = A_425
      | ~ m1_subset_1('#skF_21',k4_zfmisc_1(A_425,B_423,C_428,D_424)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_193])).

tff(c_201,plain,(
    ! [A_431,B_432,C_433,D_434] :
      ( k8_mcart_1(A_431,B_432,C_433,D_434,'#skF_21') = '#skF_22'
      | k1_xboole_0 = D_434
      | k1_xboole_0 = C_433
      | k1_xboole_0 = B_432
      | k1_xboole_0 = A_431
      | ~ m1_subset_1('#skF_21',k4_zfmisc_1(A_431,B_432,C_433,D_434)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_199])).

tff(c_204,plain,
    ( k8_mcart_1('#skF_17','#skF_18','#skF_19','#skF_20','#skF_21') = '#skF_22'
    | k1_xboole_0 = '#skF_20'
    | k1_xboole_0 = '#skF_19'
    | k1_xboole_0 = '#skF_18'
    | k1_xboole_0 = '#skF_17' ),
    inference(resolution,[status(thm)],[c_46,c_201])).

tff(c_208,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_42,c_40,c_38,c_54,c_204])).

tff(c_209,plain,
    ( k9_mcart_1('#skF_17','#skF_18','#skF_19','#skF_20','#skF_21') != '#skF_23'
    | k10_mcart_1('#skF_17','#skF_18','#skF_19','#skF_20','#skF_21') != '#skF_24'
    | k11_mcart_1('#skF_17','#skF_18','#skF_19','#skF_20','#skF_21') != '#skF_25' ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_220,plain,(
    k11_mcart_1('#skF_17','#skF_18','#skF_19','#skF_20','#skF_21') != '#skF_25' ),
    inference(splitLeft,[status(thm)],[c_209])).

tff(c_28,plain,(
    ! [C_288,E_290,D_289,B_287,A_286] :
      ( m1_subset_1(k11_mcart_1(A_286,B_287,C_288,D_289,E_290),D_289)
      | ~ m1_subset_1(E_290,k4_zfmisc_1(A_286,B_287,C_288,D_289)) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_257,plain,(
    ! [G_484,B_486,I_488,J_491,H_489,D_487,A_485,C_490] :
      ( k11_mcart_1(A_485,B_486,C_490,D_487,k4_mcart_1(G_484,H_489,I_488,J_491)) = J_491
      | ~ m1_subset_1(k11_mcart_1(A_485,B_486,C_490,D_487,k4_mcart_1(G_484,H_489,I_488,J_491)),D_487)
      | ~ m1_subset_1(k4_mcart_1(G_484,H_489,I_488,J_491),k4_zfmisc_1(A_485,B_486,C_490,D_487))
      | k1_xboole_0 = D_487
      | k1_xboole_0 = C_490
      | k1_xboole_0 = B_486
      | k1_xboole_0 = A_485 ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_267,plain,(
    ! [J_497,G_493,H_494,D_498,A_499,B_495,I_492,C_496] :
      ( k11_mcart_1(A_499,B_495,C_496,D_498,k4_mcart_1(G_493,H_494,I_492,J_497)) = J_497
      | k1_xboole_0 = D_498
      | k1_xboole_0 = C_496
      | k1_xboole_0 = B_495
      | k1_xboole_0 = A_499
      | ~ m1_subset_1(k4_mcart_1(G_493,H_494,I_492,J_497),k4_zfmisc_1(A_499,B_495,C_496,D_498)) ) ),
    inference(resolution,[status(thm)],[c_28,c_257])).

tff(c_270,plain,(
    ! [A_499,B_495,C_496,D_498] :
      ( k11_mcart_1(A_499,B_495,C_496,D_498,k4_mcart_1('#skF_22','#skF_23','#skF_24','#skF_25')) = '#skF_25'
      | k1_xboole_0 = D_498
      | k1_xboole_0 = C_496
      | k1_xboole_0 = B_495
      | k1_xboole_0 = A_499
      | ~ m1_subset_1('#skF_21',k4_zfmisc_1(A_499,B_495,C_496,D_498)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_267])).

tff(c_282,plain,(
    ! [A_508,B_509,C_510,D_511] :
      ( k11_mcart_1(A_508,B_509,C_510,D_511,'#skF_21') = '#skF_25'
      | k1_xboole_0 = D_511
      | k1_xboole_0 = C_510
      | k1_xboole_0 = B_509
      | k1_xboole_0 = A_508
      | ~ m1_subset_1('#skF_21',k4_zfmisc_1(A_508,B_509,C_510,D_511)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_270])).

tff(c_285,plain,
    ( k11_mcart_1('#skF_17','#skF_18','#skF_19','#skF_20','#skF_21') = '#skF_25'
    | k1_xboole_0 = '#skF_20'
    | k1_xboole_0 = '#skF_19'
    | k1_xboole_0 = '#skF_18'
    | k1_xboole_0 = '#skF_17' ),
    inference(resolution,[status(thm)],[c_46,c_282])).

tff(c_289,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_42,c_40,c_38,c_220,c_285])).

tff(c_290,plain,
    ( k10_mcart_1('#skF_17','#skF_18','#skF_19','#skF_20','#skF_21') != '#skF_24'
    | k9_mcart_1('#skF_17','#skF_18','#skF_19','#skF_20','#skF_21') != '#skF_23' ),
    inference(splitRight,[status(thm)],[c_209])).

tff(c_296,plain,(
    k9_mcart_1('#skF_17','#skF_18','#skF_19','#skF_20','#skF_21') != '#skF_23' ),
    inference(splitLeft,[status(thm)],[c_290])).

tff(c_32,plain,(
    ! [A_296,B_297,D_299,E_300,C_298] :
      ( m1_subset_1(k9_mcart_1(A_296,B_297,C_298,D_299,E_300),B_297)
      | ~ m1_subset_1(E_300,k4_zfmisc_1(A_296,B_297,C_298,D_299)) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_307,plain,(
    ! [J_541,H_542,B_547,A_546,C_548,D_545,G_544,I_543] :
      ( k9_mcart_1(A_546,B_547,C_548,D_545,k4_mcart_1(G_544,H_542,I_543,J_541)) = H_542
      | ~ m1_subset_1(k9_mcart_1(A_546,B_547,C_548,D_545,k4_mcart_1(G_544,H_542,I_543,J_541)),B_547)
      | ~ m1_subset_1(k4_mcart_1(G_544,H_542,I_543,J_541),k4_zfmisc_1(A_546,B_547,C_548,D_545))
      | k1_xboole_0 = D_545
      | k1_xboole_0 = C_548
      | k1_xboole_0 = B_547
      | k1_xboole_0 = A_546 ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_317,plain,(
    ! [H_552,J_554,B_549,G_553,C_555,I_551,D_556,A_550] :
      ( k9_mcart_1(A_550,B_549,C_555,D_556,k4_mcart_1(G_553,H_552,I_551,J_554)) = H_552
      | k1_xboole_0 = D_556
      | k1_xboole_0 = C_555
      | k1_xboole_0 = B_549
      | k1_xboole_0 = A_550
      | ~ m1_subset_1(k4_mcart_1(G_553,H_552,I_551,J_554),k4_zfmisc_1(A_550,B_549,C_555,D_556)) ) ),
    inference(resolution,[status(thm)],[c_32,c_307])).

tff(c_320,plain,(
    ! [A_550,B_549,C_555,D_556] :
      ( k9_mcart_1(A_550,B_549,C_555,D_556,k4_mcart_1('#skF_22','#skF_23','#skF_24','#skF_25')) = '#skF_23'
      | k1_xboole_0 = D_556
      | k1_xboole_0 = C_555
      | k1_xboole_0 = B_549
      | k1_xboole_0 = A_550
      | ~ m1_subset_1('#skF_21',k4_zfmisc_1(A_550,B_549,C_555,D_556)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_317])).

tff(c_322,plain,(
    ! [A_557,B_558,C_559,D_560] :
      ( k9_mcart_1(A_557,B_558,C_559,D_560,'#skF_21') = '#skF_23'
      | k1_xboole_0 = D_560
      | k1_xboole_0 = C_559
      | k1_xboole_0 = B_558
      | k1_xboole_0 = A_557
      | ~ m1_subset_1('#skF_21',k4_zfmisc_1(A_557,B_558,C_559,D_560)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_320])).

tff(c_325,plain,
    ( k9_mcart_1('#skF_17','#skF_18','#skF_19','#skF_20','#skF_21') = '#skF_23'
    | k1_xboole_0 = '#skF_20'
    | k1_xboole_0 = '#skF_19'
    | k1_xboole_0 = '#skF_18'
    | k1_xboole_0 = '#skF_17' ),
    inference(resolution,[status(thm)],[c_46,c_322])).

tff(c_329,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_42,c_40,c_38,c_296,c_325])).

tff(c_330,plain,(
    k10_mcart_1('#skF_17','#skF_18','#skF_19','#skF_20','#skF_21') != '#skF_24' ),
    inference(splitRight,[status(thm)],[c_290])).

tff(c_26,plain,(
    ! [E_285,D_284,C_283,A_281,B_282] :
      ( m1_subset_1(k10_mcart_1(A_281,B_282,C_283,D_284,E_285),C_283)
      | ~ m1_subset_1(E_285,k4_zfmisc_1(A_281,B_282,C_283,D_284)) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_351,plain,(
    ! [I_590,G_592,J_593,D_594,B_595,A_597,C_596,H_591] :
      ( k10_mcart_1(A_597,B_595,C_596,D_594,k4_mcart_1(G_592,H_591,I_590,J_593)) = I_590
      | ~ m1_subset_1(k10_mcart_1(A_597,B_595,C_596,D_594,k4_mcart_1(G_592,H_591,I_590,J_593)),C_596)
      | ~ m1_subset_1(k4_mcart_1(G_592,H_591,I_590,J_593),k4_zfmisc_1(A_597,B_595,C_596,D_594))
      | k1_xboole_0 = D_594
      | k1_xboole_0 = C_596
      | k1_xboole_0 = B_595
      | k1_xboole_0 = A_597 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_361,plain,(
    ! [H_599,J_602,B_600,A_598,D_604,G_603,I_601,C_605] :
      ( k10_mcart_1(A_598,B_600,C_605,D_604,k4_mcart_1(G_603,H_599,I_601,J_602)) = I_601
      | k1_xboole_0 = D_604
      | k1_xboole_0 = C_605
      | k1_xboole_0 = B_600
      | k1_xboole_0 = A_598
      | ~ m1_subset_1(k4_mcart_1(G_603,H_599,I_601,J_602),k4_zfmisc_1(A_598,B_600,C_605,D_604)) ) ),
    inference(resolution,[status(thm)],[c_26,c_351])).

tff(c_364,plain,(
    ! [A_598,B_600,C_605,D_604] :
      ( k10_mcart_1(A_598,B_600,C_605,D_604,k4_mcart_1('#skF_22','#skF_23','#skF_24','#skF_25')) = '#skF_24'
      | k1_xboole_0 = D_604
      | k1_xboole_0 = C_605
      | k1_xboole_0 = B_600
      | k1_xboole_0 = A_598
      | ~ m1_subset_1('#skF_21',k4_zfmisc_1(A_598,B_600,C_605,D_604)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_361])).

tff(c_366,plain,(
    ! [A_606,B_607,C_608,D_609] :
      ( k10_mcart_1(A_606,B_607,C_608,D_609,'#skF_21') = '#skF_24'
      | k1_xboole_0 = D_609
      | k1_xboole_0 = C_608
      | k1_xboole_0 = B_607
      | k1_xboole_0 = A_606
      | ~ m1_subset_1('#skF_21',k4_zfmisc_1(A_606,B_607,C_608,D_609)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_364])).

tff(c_369,plain,
    ( k10_mcart_1('#skF_17','#skF_18','#skF_19','#skF_20','#skF_21') = '#skF_24'
    | k1_xboole_0 = '#skF_20'
    | k1_xboole_0 = '#skF_19'
    | k1_xboole_0 = '#skF_18'
    | k1_xboole_0 = '#skF_17' ),
    inference(resolution,[status(thm)],[c_46,c_366])).

tff(c_373,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_42,c_40,c_38,c_330,c_369])).

%------------------------------------------------------------------------------
