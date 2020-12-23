%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:52 EST 2020

% Result     : Theorem 2.95s
% Output     : CNFRefutation 2.95s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 147 expanded)
%              Number of leaves         :   45 (  77 expanded)
%              Depth                    :    6
%              Number of atoms          :  207 ( 570 expanded)
%              Number of equality atoms :  155 ( 483 expanded)
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

tff(f_178,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ~ ( A != k1_xboole_0
          & B != k1_xboole_0
          & C != k1_xboole_0
          & D != k1_xboole_0
          & ? [E] :
              ( m1_subset_1(E,k4_zfmisc_1(A,B,C,D))
              & ? [F,G,H,I] :
                  ( E = k4_mcart_1(F,G,H,I)
                  & ~ ( k8_mcart_1(A,B,C,D,E) = F
                      & k9_mcart_1(A,B,C,D,E) = G
                      & k10_mcart_1(A,B,C,D,E) = H
                      & k11_mcart_1(A,B,C,D,E) = I ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_mcart_1)).

tff(f_145,axiom,(
    ! [A,B,C,D,E] :
      ( m1_subset_1(E,k4_zfmisc_1(A,B,C,D))
     => m1_subset_1(k8_mcart_1(A,B,C,D,E),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_mcart_1)).

tff(f_106,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_mcart_1)).

tff(f_141,axiom,(
    ! [A,B,C,D,E] :
      ( m1_subset_1(E,k4_zfmisc_1(A,B,C,D))
     => m1_subset_1(k11_mcart_1(A,B,C,D,E),D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k11_mcart_1)).

tff(f_79,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_mcart_1)).

tff(f_149,axiom,(
    ! [A,B,C,D,E] :
      ( m1_subset_1(E,k4_zfmisc_1(A,B,C,D))
     => m1_subset_1(k9_mcart_1(A,B,C,D,E),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_mcart_1)).

tff(f_133,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_mcart_1)).

tff(f_137,axiom,(
    ! [A,B,C,D,E] :
      ( m1_subset_1(E,k4_zfmisc_1(A,B,C,D))
     => m1_subset_1(k10_mcart_1(A,B,C,D,E),C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k10_mcart_1)).

tff(f_52,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_mcart_1)).

tff(c_46,plain,(
    k1_xboole_0 != '#skF_17' ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_44,plain,(
    k1_xboole_0 != '#skF_18' ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_42,plain,(
    k1_xboole_0 != '#skF_19' ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_40,plain,(
    k1_xboole_0 != '#skF_20' ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_34,plain,
    ( k11_mcart_1('#skF_17','#skF_18','#skF_19','#skF_20','#skF_21') != '#skF_25'
    | k10_mcart_1('#skF_17','#skF_18','#skF_19','#skF_20','#skF_21') != '#skF_24'
    | k9_mcart_1('#skF_17','#skF_18','#skF_19','#skF_20','#skF_21') != '#skF_23'
    | k8_mcart_1('#skF_17','#skF_18','#skF_19','#skF_20','#skF_21') != '#skF_22' ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_54,plain,(
    k8_mcart_1('#skF_17','#skF_18','#skF_19','#skF_20','#skF_21') != '#skF_22' ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_38,plain,(
    m1_subset_1('#skF_21',k4_zfmisc_1('#skF_17','#skF_18','#skF_19','#skF_20')) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_36,plain,(
    k4_mcart_1('#skF_22','#skF_23','#skF_24','#skF_25') = '#skF_21' ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_30,plain,(
    ! [B_292,C_293,A_291,D_294,E_295] :
      ( m1_subset_1(k8_mcart_1(A_291,B_292,C_293,D_294,E_295),A_291)
      | ~ m1_subset_1(E_295,k4_zfmisc_1(A_291,B_292,C_293,D_294)) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_91,plain,(
    ! [H_379,C_381,I_383,G_385,J_378,A_384,B_382,D_380] :
      ( k8_mcart_1(A_384,B_382,C_381,D_380,k4_mcart_1(G_385,H_379,I_383,J_378)) = G_385
      | ~ m1_subset_1(k8_mcart_1(A_384,B_382,C_381,D_380,k4_mcart_1(G_385,H_379,I_383,J_378)),A_384)
      | ~ m1_subset_1(k4_mcart_1(G_385,H_379,I_383,J_378),k4_zfmisc_1(A_384,B_382,C_381,D_380))
      | k1_xboole_0 = D_380
      | k1_xboole_0 = C_381
      | k1_xboole_0 = B_382
      | k1_xboole_0 = A_384 ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_101,plain,(
    ! [D_387,B_386,I_393,H_389,G_391,A_388,C_392,J_390] :
      ( k8_mcart_1(A_388,B_386,C_392,D_387,k4_mcart_1(G_391,H_389,I_393,J_390)) = G_391
      | k1_xboole_0 = D_387
      | k1_xboole_0 = C_392
      | k1_xboole_0 = B_386
      | k1_xboole_0 = A_388
      | ~ m1_subset_1(k4_mcart_1(G_391,H_389,I_393,J_390),k4_zfmisc_1(A_388,B_386,C_392,D_387)) ) ),
    inference(resolution,[status(thm)],[c_30,c_91])).

tff(c_104,plain,(
    ! [A_388,B_386,C_392,D_387] :
      ( k8_mcart_1(A_388,B_386,C_392,D_387,k4_mcart_1('#skF_22','#skF_23','#skF_24','#skF_25')) = '#skF_22'
      | k1_xboole_0 = D_387
      | k1_xboole_0 = C_392
      | k1_xboole_0 = B_386
      | k1_xboole_0 = A_388
      | ~ m1_subset_1('#skF_21',k4_zfmisc_1(A_388,B_386,C_392,D_387)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_101])).

tff(c_106,plain,(
    ! [A_394,B_395,C_396,D_397] :
      ( k8_mcart_1(A_394,B_395,C_396,D_397,'#skF_21') = '#skF_22'
      | k1_xboole_0 = D_397
      | k1_xboole_0 = C_396
      | k1_xboole_0 = B_395
      | k1_xboole_0 = A_394
      | ~ m1_subset_1('#skF_21',k4_zfmisc_1(A_394,B_395,C_396,D_397)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_104])).

tff(c_109,plain,
    ( k8_mcart_1('#skF_17','#skF_18','#skF_19','#skF_20','#skF_21') = '#skF_22'
    | k1_xboole_0 = '#skF_20'
    | k1_xboole_0 = '#skF_19'
    | k1_xboole_0 = '#skF_18'
    | k1_xboole_0 = '#skF_17' ),
    inference(resolution,[status(thm)],[c_38,c_106])).

tff(c_113,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_44,c_42,c_40,c_54,c_109])).

tff(c_114,plain,
    ( k9_mcart_1('#skF_17','#skF_18','#skF_19','#skF_20','#skF_21') != '#skF_23'
    | k10_mcart_1('#skF_17','#skF_18','#skF_19','#skF_20','#skF_21') != '#skF_24'
    | k11_mcart_1('#skF_17','#skF_18','#skF_19','#skF_20','#skF_21') != '#skF_25' ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_126,plain,(
    k11_mcart_1('#skF_17','#skF_18','#skF_19','#skF_20','#skF_21') != '#skF_25' ),
    inference(splitLeft,[status(thm)],[c_114])).

tff(c_28,plain,(
    ! [C_288,E_290,D_289,B_287,A_286] :
      ( m1_subset_1(k11_mcart_1(A_286,B_287,C_288,D_289,E_290),D_289)
      | ~ m1_subset_1(E_290,k4_zfmisc_1(A_286,B_287,C_288,D_289)) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_141,plain,(
    ! [H_440,J_442,I_439,C_441,A_436,G_435,B_437,D_438] :
      ( k11_mcart_1(A_436,B_437,C_441,D_438,k4_mcart_1(G_435,H_440,I_439,J_442)) = J_442
      | ~ m1_subset_1(k11_mcart_1(A_436,B_437,C_441,D_438,k4_mcart_1(G_435,H_440,I_439,J_442)),D_438)
      | ~ m1_subset_1(k4_mcart_1(G_435,H_440,I_439,J_442),k4_zfmisc_1(A_436,B_437,C_441,D_438))
      | k1_xboole_0 = D_438
      | k1_xboole_0 = C_441
      | k1_xboole_0 = B_437
      | k1_xboole_0 = A_436 ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_148,plain,(
    ! [A_436,B_437,C_441,D_438] :
      ( k11_mcart_1(A_436,B_437,C_441,D_438,k4_mcart_1('#skF_22','#skF_23','#skF_24','#skF_25')) = '#skF_25'
      | ~ m1_subset_1(k11_mcart_1(A_436,B_437,C_441,D_438,'#skF_21'),D_438)
      | ~ m1_subset_1(k4_mcart_1('#skF_22','#skF_23','#skF_24','#skF_25'),k4_zfmisc_1(A_436,B_437,C_441,D_438))
      | k1_xboole_0 = D_438
      | k1_xboole_0 = C_441
      | k1_xboole_0 = B_437
      | k1_xboole_0 = A_436 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_141])).

tff(c_172,plain,(
    ! [A_455,B_456,C_457,D_458] :
      ( k11_mcart_1(A_455,B_456,C_457,D_458,'#skF_21') = '#skF_25'
      | ~ m1_subset_1(k11_mcart_1(A_455,B_456,C_457,D_458,'#skF_21'),D_458)
      | ~ m1_subset_1('#skF_21',k4_zfmisc_1(A_455,B_456,C_457,D_458))
      | k1_xboole_0 = D_458
      | k1_xboole_0 = C_457
      | k1_xboole_0 = B_456
      | k1_xboole_0 = A_455 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_36,c_148])).

tff(c_178,plain,(
    ! [A_459,B_460,C_461,D_462] :
      ( k11_mcart_1(A_459,B_460,C_461,D_462,'#skF_21') = '#skF_25'
      | k1_xboole_0 = D_462
      | k1_xboole_0 = C_461
      | k1_xboole_0 = B_460
      | k1_xboole_0 = A_459
      | ~ m1_subset_1('#skF_21',k4_zfmisc_1(A_459,B_460,C_461,D_462)) ) ),
    inference(resolution,[status(thm)],[c_28,c_172])).

tff(c_181,plain,
    ( k11_mcart_1('#skF_17','#skF_18','#skF_19','#skF_20','#skF_21') = '#skF_25'
    | k1_xboole_0 = '#skF_20'
    | k1_xboole_0 = '#skF_19'
    | k1_xboole_0 = '#skF_18'
    | k1_xboole_0 = '#skF_17' ),
    inference(resolution,[status(thm)],[c_38,c_178])).

tff(c_185,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_44,c_42,c_40,c_126,c_181])).

tff(c_186,plain,
    ( k10_mcart_1('#skF_17','#skF_18','#skF_19','#skF_20','#skF_21') != '#skF_24'
    | k9_mcart_1('#skF_17','#skF_18','#skF_19','#skF_20','#skF_21') != '#skF_23' ),
    inference(splitRight,[status(thm)],[c_114])).

tff(c_197,plain,(
    k9_mcart_1('#skF_17','#skF_18','#skF_19','#skF_20','#skF_21') != '#skF_23' ),
    inference(splitLeft,[status(thm)],[c_186])).

tff(c_32,plain,(
    ! [A_296,B_297,D_299,E_300,C_298] :
      ( m1_subset_1(k9_mcart_1(A_296,B_297,C_298,D_299,E_300),B_297)
      | ~ m1_subset_1(E_300,k4_zfmisc_1(A_296,B_297,C_298,D_299)) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_224,plain,(
    ! [D_511,I_509,H_508,C_514,G_510,J_507,B_513,A_512] :
      ( k9_mcart_1(A_512,B_513,C_514,D_511,k4_mcart_1(G_510,H_508,I_509,J_507)) = H_508
      | ~ m1_subset_1(k9_mcart_1(A_512,B_513,C_514,D_511,k4_mcart_1(G_510,H_508,I_509,J_507)),B_513)
      | ~ m1_subset_1(k4_mcart_1(G_510,H_508,I_509,J_507),k4_zfmisc_1(A_512,B_513,C_514,D_511))
      | k1_xboole_0 = D_511
      | k1_xboole_0 = C_514
      | k1_xboole_0 = B_513
      | k1_xboole_0 = A_512 ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_234,plain,(
    ! [C_518,D_522,B_515,I_519,H_520,A_516,J_521,G_517] :
      ( k9_mcart_1(A_516,B_515,C_518,D_522,k4_mcart_1(G_517,H_520,I_519,J_521)) = H_520
      | k1_xboole_0 = D_522
      | k1_xboole_0 = C_518
      | k1_xboole_0 = B_515
      | k1_xboole_0 = A_516
      | ~ m1_subset_1(k4_mcart_1(G_517,H_520,I_519,J_521),k4_zfmisc_1(A_516,B_515,C_518,D_522)) ) ),
    inference(resolution,[status(thm)],[c_32,c_224])).

tff(c_237,plain,(
    ! [A_516,B_515,C_518,D_522] :
      ( k9_mcart_1(A_516,B_515,C_518,D_522,k4_mcart_1('#skF_22','#skF_23','#skF_24','#skF_25')) = '#skF_23'
      | k1_xboole_0 = D_522
      | k1_xboole_0 = C_518
      | k1_xboole_0 = B_515
      | k1_xboole_0 = A_516
      | ~ m1_subset_1('#skF_21',k4_zfmisc_1(A_516,B_515,C_518,D_522)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_234])).

tff(c_239,plain,(
    ! [A_523,B_524,C_525,D_526] :
      ( k9_mcart_1(A_523,B_524,C_525,D_526,'#skF_21') = '#skF_23'
      | k1_xboole_0 = D_526
      | k1_xboole_0 = C_525
      | k1_xboole_0 = B_524
      | k1_xboole_0 = A_523
      | ~ m1_subset_1('#skF_21',k4_zfmisc_1(A_523,B_524,C_525,D_526)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_237])).

tff(c_242,plain,
    ( k9_mcart_1('#skF_17','#skF_18','#skF_19','#skF_20','#skF_21') = '#skF_23'
    | k1_xboole_0 = '#skF_20'
    | k1_xboole_0 = '#skF_19'
    | k1_xboole_0 = '#skF_18'
    | k1_xboole_0 = '#skF_17' ),
    inference(resolution,[status(thm)],[c_38,c_239])).

tff(c_246,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_44,c_42,c_40,c_197,c_242])).

tff(c_247,plain,(
    k10_mcart_1('#skF_17','#skF_18','#skF_19','#skF_20','#skF_21') != '#skF_24' ),
    inference(splitRight,[status(thm)],[c_186])).

tff(c_26,plain,(
    ! [E_285,D_284,C_283,A_281,B_282] :
      ( m1_subset_1(k10_mcart_1(A_281,B_282,C_283,D_284,E_285),C_283)
      | ~ m1_subset_1(E_285,k4_zfmisc_1(A_281,B_282,C_283,D_284)) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_284,plain,(
    ! [B_576,D_575,I_571,H_572,A_578,C_577,J_574,G_573] :
      ( k10_mcart_1(A_578,B_576,C_577,D_575,k4_mcart_1(G_573,H_572,I_571,J_574)) = I_571
      | ~ m1_subset_1(k10_mcart_1(A_578,B_576,C_577,D_575,k4_mcart_1(G_573,H_572,I_571,J_574)),C_577)
      | ~ m1_subset_1(k4_mcart_1(G_573,H_572,I_571,J_574),k4_zfmisc_1(A_578,B_576,C_577,D_575))
      | k1_xboole_0 = D_575
      | k1_xboole_0 = C_577
      | k1_xboole_0 = B_576
      | k1_xboole_0 = A_578 ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_294,plain,(
    ! [J_582,G_581,H_584,D_583,I_585,C_586,A_579,B_580] :
      ( k10_mcart_1(A_579,B_580,C_586,D_583,k4_mcart_1(G_581,H_584,I_585,J_582)) = I_585
      | k1_xboole_0 = D_583
      | k1_xboole_0 = C_586
      | k1_xboole_0 = B_580
      | k1_xboole_0 = A_579
      | ~ m1_subset_1(k4_mcart_1(G_581,H_584,I_585,J_582),k4_zfmisc_1(A_579,B_580,C_586,D_583)) ) ),
    inference(resolution,[status(thm)],[c_26,c_284])).

tff(c_297,plain,(
    ! [A_579,B_580,C_586,D_583] :
      ( k10_mcart_1(A_579,B_580,C_586,D_583,k4_mcart_1('#skF_22','#skF_23','#skF_24','#skF_25')) = '#skF_24'
      | k1_xboole_0 = D_583
      | k1_xboole_0 = C_586
      | k1_xboole_0 = B_580
      | k1_xboole_0 = A_579
      | ~ m1_subset_1('#skF_21',k4_zfmisc_1(A_579,B_580,C_586,D_583)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_294])).

tff(c_299,plain,(
    ! [A_587,B_588,C_589,D_590] :
      ( k10_mcart_1(A_587,B_588,C_589,D_590,'#skF_21') = '#skF_24'
      | k1_xboole_0 = D_590
      | k1_xboole_0 = C_589
      | k1_xboole_0 = B_588
      | k1_xboole_0 = A_587
      | ~ m1_subset_1('#skF_21',k4_zfmisc_1(A_587,B_588,C_589,D_590)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_297])).

tff(c_302,plain,
    ( k10_mcart_1('#skF_17','#skF_18','#skF_19','#skF_20','#skF_21') = '#skF_24'
    | k1_xboole_0 = '#skF_20'
    | k1_xboole_0 = '#skF_19'
    | k1_xboole_0 = '#skF_18'
    | k1_xboole_0 = '#skF_17' ),
    inference(resolution,[status(thm)],[c_38,c_299])).

tff(c_306,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_44,c_42,c_40,c_247,c_302])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:25:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.95/1.39  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.95/1.40  
% 2.95/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.95/1.40  %$ m1_subset_1 > k9_mcart_1 > k8_mcart_1 > k11_mcart_1 > k10_mcart_1 > k4_zfmisc_1 > k4_mcart_1 > #nlpp > k1_xboole_0 > #skF_10 > #skF_15 > #skF_9 > #skF_20 > #skF_18 > #skF_2 > #skF_17 > #skF_1 > #skF_25 > #skF_14 > #skF_13 > #skF_19 > #skF_11 > #skF_8 > #skF_12 > #skF_7 > #skF_21 > #skF_3 > #skF_5 > #skF_22 > #skF_24 > #skF_23 > #skF_16 > #skF_6 > #skF_4
% 2.95/1.40  
% 2.95/1.40  %Foreground sorts:
% 2.95/1.40  
% 2.95/1.40  
% 2.95/1.40  %Background operators:
% 2.95/1.40  
% 2.95/1.40  
% 2.95/1.40  %Foreground operators:
% 2.95/1.40  tff('#skF_10', type, '#skF_10': ($i * $i * $i * $i * $i * $i) > $i).
% 2.95/1.40  tff('#skF_15', type, '#skF_15': ($i * $i * $i * $i * $i * $i) > $i).
% 2.95/1.40  tff('#skF_9', type, '#skF_9': ($i * $i * $i * $i * $i * $i) > $i).
% 2.95/1.40  tff('#skF_20', type, '#skF_20': $i).
% 2.95/1.40  tff('#skF_18', type, '#skF_18': $i).
% 2.95/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.95/1.40  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i * $i) > $i).
% 2.95/1.40  tff('#skF_17', type, '#skF_17': $i).
% 2.95/1.40  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i * $i) > $i).
% 2.95/1.40  tff(k10_mcart_1, type, k10_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 2.95/1.40  tff('#skF_25', type, '#skF_25': $i).
% 2.95/1.40  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.95/1.40  tff('#skF_14', type, '#skF_14': ($i * $i * $i * $i * $i * $i) > $i).
% 2.95/1.40  tff('#skF_13', type, '#skF_13': ($i * $i * $i * $i * $i * $i) > $i).
% 2.95/1.40  tff(k4_zfmisc_1, type, k4_zfmisc_1: ($i * $i * $i * $i) > $i).
% 2.95/1.40  tff('#skF_19', type, '#skF_19': $i).
% 2.95/1.40  tff('#skF_11', type, '#skF_11': ($i * $i * $i * $i * $i * $i) > $i).
% 2.95/1.40  tff(k11_mcart_1, type, k11_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 2.95/1.40  tff('#skF_8', type, '#skF_8': ($i * $i * $i * $i * $i * $i) > $i).
% 2.95/1.40  tff('#skF_12', type, '#skF_12': ($i * $i * $i * $i * $i * $i) > $i).
% 2.95/1.40  tff('#skF_7', type, '#skF_7': ($i * $i * $i * $i * $i * $i) > $i).
% 2.95/1.40  tff('#skF_21', type, '#skF_21': $i).
% 2.95/1.40  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i * $i * $i) > $i).
% 2.95/1.40  tff(k8_mcart_1, type, k8_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 2.95/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.95/1.40  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i * $i * $i) > $i).
% 2.95/1.40  tff('#skF_22', type, '#skF_22': $i).
% 2.95/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.95/1.40  tff('#skF_24', type, '#skF_24': $i).
% 2.95/1.40  tff('#skF_23', type, '#skF_23': $i).
% 2.95/1.40  tff('#skF_16', type, '#skF_16': ($i * $i * $i * $i * $i * $i) > $i).
% 2.95/1.40  tff(k9_mcart_1, type, k9_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 2.95/1.40  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i * $i * $i) > $i).
% 2.95/1.40  tff(k4_mcart_1, type, k4_mcart_1: ($i * $i * $i * $i) > $i).
% 2.95/1.40  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i * $i * $i) > $i).
% 2.95/1.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.95/1.40  
% 2.95/1.42  tff(f_178, negated_conjecture, ~(![A, B, C, D]: ~((((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(D = k1_xboole_0)) & (?[E]: (m1_subset_1(E, k4_zfmisc_1(A, B, C, D)) & (?[F, G, H, I]: ((E = k4_mcart_1(F, G, H, I)) & ~((((k8_mcart_1(A, B, C, D, E) = F) & (k9_mcart_1(A, B, C, D, E) = G)) & (k10_mcart_1(A, B, C, D, E) = H)) & (k11_mcart_1(A, B, C, D, E) = I)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_mcart_1)).
% 2.95/1.42  tff(f_145, axiom, (![A, B, C, D, E]: (m1_subset_1(E, k4_zfmisc_1(A, B, C, D)) => m1_subset_1(k8_mcart_1(A, B, C, D, E), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_mcart_1)).
% 2.95/1.42  tff(f_106, axiom, (![A, B, C, D]: ~((((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(D = k1_xboole_0)) & ~(![E]: (m1_subset_1(E, k4_zfmisc_1(A, B, C, D)) => (![F]: (m1_subset_1(F, A) => ((F = k8_mcart_1(A, B, C, D, E)) <=> (![G, H, I, J]: ((E = k4_mcart_1(G, H, I, J)) => (F = G)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_mcart_1)).
% 2.95/1.42  tff(f_141, axiom, (![A, B, C, D, E]: (m1_subset_1(E, k4_zfmisc_1(A, B, C, D)) => m1_subset_1(k11_mcart_1(A, B, C, D, E), D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k11_mcart_1)).
% 2.95/1.42  tff(f_79, axiom, (![A, B, C, D]: ~((((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(D = k1_xboole_0)) & ~(![E]: (m1_subset_1(E, k4_zfmisc_1(A, B, C, D)) => (![F]: (m1_subset_1(F, D) => ((F = k11_mcart_1(A, B, C, D, E)) <=> (![G, H, I, J]: ((E = k4_mcart_1(G, H, I, J)) => (F = J)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d11_mcart_1)).
% 2.95/1.42  tff(f_149, axiom, (![A, B, C, D, E]: (m1_subset_1(E, k4_zfmisc_1(A, B, C, D)) => m1_subset_1(k9_mcart_1(A, B, C, D, E), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k9_mcart_1)).
% 2.95/1.42  tff(f_133, axiom, (![A, B, C, D]: ~((((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(D = k1_xboole_0)) & ~(![E]: (m1_subset_1(E, k4_zfmisc_1(A, B, C, D)) => (![F]: (m1_subset_1(F, B) => ((F = k9_mcart_1(A, B, C, D, E)) <=> (![G, H, I, J]: ((E = k4_mcart_1(G, H, I, J)) => (F = H)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_mcart_1)).
% 2.95/1.42  tff(f_137, axiom, (![A, B, C, D, E]: (m1_subset_1(E, k4_zfmisc_1(A, B, C, D)) => m1_subset_1(k10_mcart_1(A, B, C, D, E), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k10_mcart_1)).
% 2.95/1.42  tff(f_52, axiom, (![A, B, C, D]: ~((((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(D = k1_xboole_0)) & ~(![E]: (m1_subset_1(E, k4_zfmisc_1(A, B, C, D)) => (![F]: (m1_subset_1(F, C) => ((F = k10_mcart_1(A, B, C, D, E)) <=> (![G, H, I, J]: ((E = k4_mcart_1(G, H, I, J)) => (F = I)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_mcart_1)).
% 2.95/1.42  tff(c_46, plain, (k1_xboole_0!='#skF_17'), inference(cnfTransformation, [status(thm)], [f_178])).
% 2.95/1.42  tff(c_44, plain, (k1_xboole_0!='#skF_18'), inference(cnfTransformation, [status(thm)], [f_178])).
% 2.95/1.42  tff(c_42, plain, (k1_xboole_0!='#skF_19'), inference(cnfTransformation, [status(thm)], [f_178])).
% 2.95/1.42  tff(c_40, plain, (k1_xboole_0!='#skF_20'), inference(cnfTransformation, [status(thm)], [f_178])).
% 2.95/1.42  tff(c_34, plain, (k11_mcart_1('#skF_17', '#skF_18', '#skF_19', '#skF_20', '#skF_21')!='#skF_25' | k10_mcart_1('#skF_17', '#skF_18', '#skF_19', '#skF_20', '#skF_21')!='#skF_24' | k9_mcart_1('#skF_17', '#skF_18', '#skF_19', '#skF_20', '#skF_21')!='#skF_23' | k8_mcart_1('#skF_17', '#skF_18', '#skF_19', '#skF_20', '#skF_21')!='#skF_22'), inference(cnfTransformation, [status(thm)], [f_178])).
% 2.95/1.42  tff(c_54, plain, (k8_mcart_1('#skF_17', '#skF_18', '#skF_19', '#skF_20', '#skF_21')!='#skF_22'), inference(splitLeft, [status(thm)], [c_34])).
% 2.95/1.42  tff(c_38, plain, (m1_subset_1('#skF_21', k4_zfmisc_1('#skF_17', '#skF_18', '#skF_19', '#skF_20'))), inference(cnfTransformation, [status(thm)], [f_178])).
% 2.95/1.42  tff(c_36, plain, (k4_mcart_1('#skF_22', '#skF_23', '#skF_24', '#skF_25')='#skF_21'), inference(cnfTransformation, [status(thm)], [f_178])).
% 2.95/1.42  tff(c_30, plain, (![B_292, C_293, A_291, D_294, E_295]: (m1_subset_1(k8_mcart_1(A_291, B_292, C_293, D_294, E_295), A_291) | ~m1_subset_1(E_295, k4_zfmisc_1(A_291, B_292, C_293, D_294)))), inference(cnfTransformation, [status(thm)], [f_145])).
% 2.95/1.42  tff(c_91, plain, (![H_379, C_381, I_383, G_385, J_378, A_384, B_382, D_380]: (k8_mcart_1(A_384, B_382, C_381, D_380, k4_mcart_1(G_385, H_379, I_383, J_378))=G_385 | ~m1_subset_1(k8_mcart_1(A_384, B_382, C_381, D_380, k4_mcart_1(G_385, H_379, I_383, J_378)), A_384) | ~m1_subset_1(k4_mcart_1(G_385, H_379, I_383, J_378), k4_zfmisc_1(A_384, B_382, C_381, D_380)) | k1_xboole_0=D_380 | k1_xboole_0=C_381 | k1_xboole_0=B_382 | k1_xboole_0=A_384)), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.95/1.42  tff(c_101, plain, (![D_387, B_386, I_393, H_389, G_391, A_388, C_392, J_390]: (k8_mcart_1(A_388, B_386, C_392, D_387, k4_mcart_1(G_391, H_389, I_393, J_390))=G_391 | k1_xboole_0=D_387 | k1_xboole_0=C_392 | k1_xboole_0=B_386 | k1_xboole_0=A_388 | ~m1_subset_1(k4_mcart_1(G_391, H_389, I_393, J_390), k4_zfmisc_1(A_388, B_386, C_392, D_387)))), inference(resolution, [status(thm)], [c_30, c_91])).
% 2.95/1.42  tff(c_104, plain, (![A_388, B_386, C_392, D_387]: (k8_mcart_1(A_388, B_386, C_392, D_387, k4_mcart_1('#skF_22', '#skF_23', '#skF_24', '#skF_25'))='#skF_22' | k1_xboole_0=D_387 | k1_xboole_0=C_392 | k1_xboole_0=B_386 | k1_xboole_0=A_388 | ~m1_subset_1('#skF_21', k4_zfmisc_1(A_388, B_386, C_392, D_387)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_101])).
% 2.95/1.42  tff(c_106, plain, (![A_394, B_395, C_396, D_397]: (k8_mcart_1(A_394, B_395, C_396, D_397, '#skF_21')='#skF_22' | k1_xboole_0=D_397 | k1_xboole_0=C_396 | k1_xboole_0=B_395 | k1_xboole_0=A_394 | ~m1_subset_1('#skF_21', k4_zfmisc_1(A_394, B_395, C_396, D_397)))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_104])).
% 2.95/1.42  tff(c_109, plain, (k8_mcart_1('#skF_17', '#skF_18', '#skF_19', '#skF_20', '#skF_21')='#skF_22' | k1_xboole_0='#skF_20' | k1_xboole_0='#skF_19' | k1_xboole_0='#skF_18' | k1_xboole_0='#skF_17'), inference(resolution, [status(thm)], [c_38, c_106])).
% 2.95/1.42  tff(c_113, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_44, c_42, c_40, c_54, c_109])).
% 2.95/1.42  tff(c_114, plain, (k9_mcart_1('#skF_17', '#skF_18', '#skF_19', '#skF_20', '#skF_21')!='#skF_23' | k10_mcart_1('#skF_17', '#skF_18', '#skF_19', '#skF_20', '#skF_21')!='#skF_24' | k11_mcart_1('#skF_17', '#skF_18', '#skF_19', '#skF_20', '#skF_21')!='#skF_25'), inference(splitRight, [status(thm)], [c_34])).
% 2.95/1.42  tff(c_126, plain, (k11_mcart_1('#skF_17', '#skF_18', '#skF_19', '#skF_20', '#skF_21')!='#skF_25'), inference(splitLeft, [status(thm)], [c_114])).
% 2.95/1.42  tff(c_28, plain, (![C_288, E_290, D_289, B_287, A_286]: (m1_subset_1(k11_mcart_1(A_286, B_287, C_288, D_289, E_290), D_289) | ~m1_subset_1(E_290, k4_zfmisc_1(A_286, B_287, C_288, D_289)))), inference(cnfTransformation, [status(thm)], [f_141])).
% 2.95/1.42  tff(c_141, plain, (![H_440, J_442, I_439, C_441, A_436, G_435, B_437, D_438]: (k11_mcart_1(A_436, B_437, C_441, D_438, k4_mcart_1(G_435, H_440, I_439, J_442))=J_442 | ~m1_subset_1(k11_mcart_1(A_436, B_437, C_441, D_438, k4_mcart_1(G_435, H_440, I_439, J_442)), D_438) | ~m1_subset_1(k4_mcart_1(G_435, H_440, I_439, J_442), k4_zfmisc_1(A_436, B_437, C_441, D_438)) | k1_xboole_0=D_438 | k1_xboole_0=C_441 | k1_xboole_0=B_437 | k1_xboole_0=A_436)), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.95/1.42  tff(c_148, plain, (![A_436, B_437, C_441, D_438]: (k11_mcart_1(A_436, B_437, C_441, D_438, k4_mcart_1('#skF_22', '#skF_23', '#skF_24', '#skF_25'))='#skF_25' | ~m1_subset_1(k11_mcart_1(A_436, B_437, C_441, D_438, '#skF_21'), D_438) | ~m1_subset_1(k4_mcart_1('#skF_22', '#skF_23', '#skF_24', '#skF_25'), k4_zfmisc_1(A_436, B_437, C_441, D_438)) | k1_xboole_0=D_438 | k1_xboole_0=C_441 | k1_xboole_0=B_437 | k1_xboole_0=A_436)), inference(superposition, [status(thm), theory('equality')], [c_36, c_141])).
% 2.95/1.42  tff(c_172, plain, (![A_455, B_456, C_457, D_458]: (k11_mcart_1(A_455, B_456, C_457, D_458, '#skF_21')='#skF_25' | ~m1_subset_1(k11_mcart_1(A_455, B_456, C_457, D_458, '#skF_21'), D_458) | ~m1_subset_1('#skF_21', k4_zfmisc_1(A_455, B_456, C_457, D_458)) | k1_xboole_0=D_458 | k1_xboole_0=C_457 | k1_xboole_0=B_456 | k1_xboole_0=A_455)), inference(demodulation, [status(thm), theory('equality')], [c_36, c_36, c_148])).
% 2.95/1.42  tff(c_178, plain, (![A_459, B_460, C_461, D_462]: (k11_mcart_1(A_459, B_460, C_461, D_462, '#skF_21')='#skF_25' | k1_xboole_0=D_462 | k1_xboole_0=C_461 | k1_xboole_0=B_460 | k1_xboole_0=A_459 | ~m1_subset_1('#skF_21', k4_zfmisc_1(A_459, B_460, C_461, D_462)))), inference(resolution, [status(thm)], [c_28, c_172])).
% 2.95/1.42  tff(c_181, plain, (k11_mcart_1('#skF_17', '#skF_18', '#skF_19', '#skF_20', '#skF_21')='#skF_25' | k1_xboole_0='#skF_20' | k1_xboole_0='#skF_19' | k1_xboole_0='#skF_18' | k1_xboole_0='#skF_17'), inference(resolution, [status(thm)], [c_38, c_178])).
% 2.95/1.42  tff(c_185, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_44, c_42, c_40, c_126, c_181])).
% 2.95/1.42  tff(c_186, plain, (k10_mcart_1('#skF_17', '#skF_18', '#skF_19', '#skF_20', '#skF_21')!='#skF_24' | k9_mcart_1('#skF_17', '#skF_18', '#skF_19', '#skF_20', '#skF_21')!='#skF_23'), inference(splitRight, [status(thm)], [c_114])).
% 2.95/1.42  tff(c_197, plain, (k9_mcart_1('#skF_17', '#skF_18', '#skF_19', '#skF_20', '#skF_21')!='#skF_23'), inference(splitLeft, [status(thm)], [c_186])).
% 2.95/1.42  tff(c_32, plain, (![A_296, B_297, D_299, E_300, C_298]: (m1_subset_1(k9_mcart_1(A_296, B_297, C_298, D_299, E_300), B_297) | ~m1_subset_1(E_300, k4_zfmisc_1(A_296, B_297, C_298, D_299)))), inference(cnfTransformation, [status(thm)], [f_149])).
% 2.95/1.42  tff(c_224, plain, (![D_511, I_509, H_508, C_514, G_510, J_507, B_513, A_512]: (k9_mcart_1(A_512, B_513, C_514, D_511, k4_mcart_1(G_510, H_508, I_509, J_507))=H_508 | ~m1_subset_1(k9_mcart_1(A_512, B_513, C_514, D_511, k4_mcart_1(G_510, H_508, I_509, J_507)), B_513) | ~m1_subset_1(k4_mcart_1(G_510, H_508, I_509, J_507), k4_zfmisc_1(A_512, B_513, C_514, D_511)) | k1_xboole_0=D_511 | k1_xboole_0=C_514 | k1_xboole_0=B_513 | k1_xboole_0=A_512)), inference(cnfTransformation, [status(thm)], [f_133])).
% 2.95/1.42  tff(c_234, plain, (![C_518, D_522, B_515, I_519, H_520, A_516, J_521, G_517]: (k9_mcart_1(A_516, B_515, C_518, D_522, k4_mcart_1(G_517, H_520, I_519, J_521))=H_520 | k1_xboole_0=D_522 | k1_xboole_0=C_518 | k1_xboole_0=B_515 | k1_xboole_0=A_516 | ~m1_subset_1(k4_mcart_1(G_517, H_520, I_519, J_521), k4_zfmisc_1(A_516, B_515, C_518, D_522)))), inference(resolution, [status(thm)], [c_32, c_224])).
% 2.95/1.42  tff(c_237, plain, (![A_516, B_515, C_518, D_522]: (k9_mcart_1(A_516, B_515, C_518, D_522, k4_mcart_1('#skF_22', '#skF_23', '#skF_24', '#skF_25'))='#skF_23' | k1_xboole_0=D_522 | k1_xboole_0=C_518 | k1_xboole_0=B_515 | k1_xboole_0=A_516 | ~m1_subset_1('#skF_21', k4_zfmisc_1(A_516, B_515, C_518, D_522)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_234])).
% 2.95/1.42  tff(c_239, plain, (![A_523, B_524, C_525, D_526]: (k9_mcart_1(A_523, B_524, C_525, D_526, '#skF_21')='#skF_23' | k1_xboole_0=D_526 | k1_xboole_0=C_525 | k1_xboole_0=B_524 | k1_xboole_0=A_523 | ~m1_subset_1('#skF_21', k4_zfmisc_1(A_523, B_524, C_525, D_526)))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_237])).
% 2.95/1.42  tff(c_242, plain, (k9_mcart_1('#skF_17', '#skF_18', '#skF_19', '#skF_20', '#skF_21')='#skF_23' | k1_xboole_0='#skF_20' | k1_xboole_0='#skF_19' | k1_xboole_0='#skF_18' | k1_xboole_0='#skF_17'), inference(resolution, [status(thm)], [c_38, c_239])).
% 2.95/1.42  tff(c_246, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_44, c_42, c_40, c_197, c_242])).
% 2.95/1.42  tff(c_247, plain, (k10_mcart_1('#skF_17', '#skF_18', '#skF_19', '#skF_20', '#skF_21')!='#skF_24'), inference(splitRight, [status(thm)], [c_186])).
% 2.95/1.42  tff(c_26, plain, (![E_285, D_284, C_283, A_281, B_282]: (m1_subset_1(k10_mcart_1(A_281, B_282, C_283, D_284, E_285), C_283) | ~m1_subset_1(E_285, k4_zfmisc_1(A_281, B_282, C_283, D_284)))), inference(cnfTransformation, [status(thm)], [f_137])).
% 2.95/1.42  tff(c_284, plain, (![B_576, D_575, I_571, H_572, A_578, C_577, J_574, G_573]: (k10_mcart_1(A_578, B_576, C_577, D_575, k4_mcart_1(G_573, H_572, I_571, J_574))=I_571 | ~m1_subset_1(k10_mcart_1(A_578, B_576, C_577, D_575, k4_mcart_1(G_573, H_572, I_571, J_574)), C_577) | ~m1_subset_1(k4_mcart_1(G_573, H_572, I_571, J_574), k4_zfmisc_1(A_578, B_576, C_577, D_575)) | k1_xboole_0=D_575 | k1_xboole_0=C_577 | k1_xboole_0=B_576 | k1_xboole_0=A_578)), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.95/1.42  tff(c_294, plain, (![J_582, G_581, H_584, D_583, I_585, C_586, A_579, B_580]: (k10_mcart_1(A_579, B_580, C_586, D_583, k4_mcart_1(G_581, H_584, I_585, J_582))=I_585 | k1_xboole_0=D_583 | k1_xboole_0=C_586 | k1_xboole_0=B_580 | k1_xboole_0=A_579 | ~m1_subset_1(k4_mcart_1(G_581, H_584, I_585, J_582), k4_zfmisc_1(A_579, B_580, C_586, D_583)))), inference(resolution, [status(thm)], [c_26, c_284])).
% 2.95/1.42  tff(c_297, plain, (![A_579, B_580, C_586, D_583]: (k10_mcart_1(A_579, B_580, C_586, D_583, k4_mcart_1('#skF_22', '#skF_23', '#skF_24', '#skF_25'))='#skF_24' | k1_xboole_0=D_583 | k1_xboole_0=C_586 | k1_xboole_0=B_580 | k1_xboole_0=A_579 | ~m1_subset_1('#skF_21', k4_zfmisc_1(A_579, B_580, C_586, D_583)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_294])).
% 2.95/1.42  tff(c_299, plain, (![A_587, B_588, C_589, D_590]: (k10_mcart_1(A_587, B_588, C_589, D_590, '#skF_21')='#skF_24' | k1_xboole_0=D_590 | k1_xboole_0=C_589 | k1_xboole_0=B_588 | k1_xboole_0=A_587 | ~m1_subset_1('#skF_21', k4_zfmisc_1(A_587, B_588, C_589, D_590)))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_297])).
% 2.95/1.42  tff(c_302, plain, (k10_mcart_1('#skF_17', '#skF_18', '#skF_19', '#skF_20', '#skF_21')='#skF_24' | k1_xboole_0='#skF_20' | k1_xboole_0='#skF_19' | k1_xboole_0='#skF_18' | k1_xboole_0='#skF_17'), inference(resolution, [status(thm)], [c_38, c_299])).
% 2.95/1.42  tff(c_306, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_44, c_42, c_40, c_247, c_302])).
% 2.95/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.95/1.42  
% 2.95/1.42  Inference rules
% 2.95/1.42  ----------------------
% 2.95/1.42  #Ref     : 0
% 2.95/1.42  #Sup     : 49
% 2.95/1.42  #Fact    : 0
% 2.95/1.42  #Define  : 0
% 2.95/1.42  #Split   : 3
% 2.95/1.42  #Chain   : 0
% 2.95/1.42  #Close   : 0
% 2.95/1.42  
% 2.95/1.42  Ordering : KBO
% 2.95/1.42  
% 2.95/1.42  Simplification rules
% 2.95/1.42  ----------------------
% 2.95/1.42  #Subsume      : 12
% 2.95/1.42  #Demod        : 30
% 2.95/1.42  #Tautology    : 14
% 2.95/1.42  #SimpNegUnit  : 8
% 2.95/1.42  #BackRed      : 0
% 2.95/1.42  
% 2.95/1.42  #Partial instantiations: 0
% 2.95/1.42  #Strategies tried      : 1
% 2.95/1.42  
% 2.95/1.42  Timing (in seconds)
% 2.95/1.42  ----------------------
% 2.95/1.42  Preprocessing        : 0.39
% 2.95/1.42  Parsing              : 0.19
% 2.95/1.42  CNF conversion       : 0.04
% 2.95/1.42  Main loop            : 0.27
% 2.95/1.42  Inferencing          : 0.11
% 2.95/1.42  Reduction            : 0.07
% 2.95/1.42  Demodulation         : 0.05
% 2.95/1.42  BG Simplification    : 0.03
% 2.95/1.42  Subsumption          : 0.05
% 2.95/1.42  Abstraction          : 0.02
% 2.95/1.42  MUC search           : 0.00
% 2.95/1.42  Cooper               : 0.00
% 2.95/1.42  Total                : 0.70
% 2.95/1.42  Index Insertion      : 0.00
% 2.95/1.42  Index Deletion       : 0.00
% 2.95/1.42  Index Matching       : 0.00
% 2.95/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
