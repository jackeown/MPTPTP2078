%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0900+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:02 EST 2020

% Result     : Theorem 3.40s
% Output     : CNFRefutation 3.60s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 197 expanded)
%              Number of leaves         :   46 (  99 expanded)
%              Depth                    :   15
%              Number of atoms          :  342 ( 780 expanded)
%              Number of equality atoms :  268 ( 605 expanded)
%              Maximal formula depth    :   25 (   9 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > k9_mcart_1 > k8_mcart_1 > k11_mcart_1 > k10_mcart_1 > k4_zfmisc_1 > k4_mcart_1 > #nlpp > k1_xboole_0 > #skF_10 > #skF_15 > #skF_19 > #skF_9 > #skF_2 > #skF_1 > #skF_25 > #skF_14 > #skF_13 > #skF_20 > #skF_11 > #skF_8 > #skF_12 > #skF_7 > #skF_21 > #skF_3 > #skF_5 > #skF_22 > #skF_17 > #skF_24 > #skF_23 > #skF_16 > #skF_6 > #skF_4 > #skF_18

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_10',type,(
    '#skF_10': ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_15',type,(
    '#skF_15': ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_19',type,(
    '#skF_19': ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i * $i ) > $i )).

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

tff('#skF_20',type,(
    '#skF_20': ( $i * $i * $i * $i * $i ) > $i )).

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

tff('#skF_17',type,(
    '#skF_17': ( $i * $i * $i * $i * $i ) > $i )).

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

tff('#skF_18',type,(
    '#skF_18': ( $i * $i * $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_199,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ~ ( A != k1_xboole_0
          & B != k1_xboole_0
          & C != k1_xboole_0
          & D != k1_xboole_0
          & ~ ! [E] :
                ( m1_subset_1(E,k4_zfmisc_1(A,B,C,D))
               => E = k4_mcart_1(k8_mcart_1(A,B,C,D,E),k9_mcart_1(A,B,C,D,E),k10_mcart_1(A,B,C,D,E),k11_mcart_1(A,B,C,D,E)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_mcart_1)).

tff(f_179,axiom,(
    ! [A,B,C,D] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & D != k1_xboole_0
        & ? [E] :
            ( m1_subset_1(E,k4_zfmisc_1(A,B,C,D))
            & ! [F] :
                ( m1_subset_1(F,A)
               => ! [G] :
                    ( m1_subset_1(G,B)
                   => ! [H] :
                        ( m1_subset_1(H,C)
                       => ! [I] :
                            ( m1_subset_1(I,D)
                           => E != k4_mcart_1(F,G,H,I) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l68_mcart_1)).

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

tff(c_54,plain,(
    k1_xboole_0 != '#skF_21' ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_52,plain,(
    k1_xboole_0 != '#skF_22' ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_50,plain,(
    k1_xboole_0 != '#skF_23' ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_48,plain,(
    k1_xboole_0 != '#skF_24' ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_46,plain,(
    m1_subset_1('#skF_25',k4_zfmisc_1('#skF_21','#skF_22','#skF_23','#skF_24')) ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_34,plain,(
    ! [B_302,D_304,E_336,C_303,A_301] :
      ( k4_mcart_1('#skF_17'(B_302,E_336,D_304,A_301,C_303),'#skF_18'(B_302,E_336,D_304,A_301,C_303),'#skF_19'(B_302,E_336,D_304,A_301,C_303),'#skF_20'(B_302,E_336,D_304,A_301,C_303)) = E_336
      | ~ m1_subset_1(E_336,k4_zfmisc_1(A_301,B_302,C_303,D_304))
      | k1_xboole_0 = D_304
      | k1_xboole_0 = C_303
      | k1_xboole_0 = B_302
      | k1_xboole_0 = A_301 ) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_30,plain,(
    ! [B_292,C_293,A_291,D_294,E_295] :
      ( m1_subset_1(k8_mcart_1(A_291,B_292,C_293,D_294,E_295),A_291)
      | ~ m1_subset_1(E_295,k4_zfmisc_1(A_291,B_292,C_293,D_294)) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_123,plain,(
    ! [A_487,H_482,G_488,J_481,C_484,B_485,I_486,D_483] :
      ( k8_mcart_1(A_487,B_485,C_484,D_483,k4_mcart_1(G_488,H_482,I_486,J_481)) = G_488
      | ~ m1_subset_1(k8_mcart_1(A_487,B_485,C_484,D_483,k4_mcart_1(G_488,H_482,I_486,J_481)),A_487)
      | ~ m1_subset_1(k4_mcart_1(G_488,H_482,I_486,J_481),k4_zfmisc_1(A_487,B_485,C_484,D_483))
      | k1_xboole_0 = D_483
      | k1_xboole_0 = C_484
      | k1_xboole_0 = B_485
      | k1_xboole_0 = A_487 ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_132,plain,(
    ! [B_491,J_496,G_489,A_493,I_490,D_492,C_495,H_494] :
      ( k8_mcart_1(A_493,B_491,C_495,D_492,k4_mcart_1(G_489,H_494,I_490,J_496)) = G_489
      | k1_xboole_0 = D_492
      | k1_xboole_0 = C_495
      | k1_xboole_0 = B_491
      | k1_xboole_0 = A_493
      | ~ m1_subset_1(k4_mcart_1(G_489,H_494,I_490,J_496),k4_zfmisc_1(A_493,B_491,C_495,D_492)) ) ),
    inference(resolution,[status(thm)],[c_30,c_123])).

tff(c_509,plain,(
    ! [C_601,B_600,D_604,E_603,A_606,C_607,D_605,A_602,B_599] :
      ( k8_mcart_1(A_602,B_599,C_601,D_604,k4_mcart_1('#skF_17'(B_600,E_603,D_605,A_606,C_607),'#skF_18'(B_600,E_603,D_605,A_606,C_607),'#skF_19'(B_600,E_603,D_605,A_606,C_607),'#skF_20'(B_600,E_603,D_605,A_606,C_607))) = '#skF_17'(B_600,E_603,D_605,A_606,C_607)
      | k1_xboole_0 = D_604
      | k1_xboole_0 = C_601
      | k1_xboole_0 = B_599
      | k1_xboole_0 = A_602
      | ~ m1_subset_1(E_603,k4_zfmisc_1(A_602,B_599,C_601,D_604))
      | ~ m1_subset_1(E_603,k4_zfmisc_1(A_606,B_600,C_607,D_605))
      | k1_xboole_0 = D_605
      | k1_xboole_0 = C_607
      | k1_xboole_0 = B_600
      | k1_xboole_0 = A_606 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_132])).

tff(c_524,plain,(
    ! [A_615,B_613,C_611,A_610,D_608,B_609,D_614,C_616,E_612] :
      ( k8_mcart_1(A_610,B_613,C_611,D_608,E_612) = '#skF_17'(B_609,E_612,D_614,A_615,C_616)
      | k1_xboole_0 = D_608
      | k1_xboole_0 = C_611
      | k1_xboole_0 = B_613
      | k1_xboole_0 = A_610
      | ~ m1_subset_1(E_612,k4_zfmisc_1(A_610,B_613,C_611,D_608))
      | ~ m1_subset_1(E_612,k4_zfmisc_1(A_615,B_609,C_616,D_614))
      | k1_xboole_0 = D_614
      | k1_xboole_0 = C_616
      | k1_xboole_0 = B_609
      | k1_xboole_0 = A_615
      | ~ m1_subset_1(E_612,k4_zfmisc_1(A_615,B_609,C_616,D_614))
      | k1_xboole_0 = D_614
      | k1_xboole_0 = C_616
      | k1_xboole_0 = B_609
      | k1_xboole_0 = A_615 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_509])).

tff(c_550,plain,(
    ! [B_609,D_614,A_615,C_616] :
      ( k8_mcart_1('#skF_21','#skF_22','#skF_23','#skF_24','#skF_25') = '#skF_17'(B_609,'#skF_25',D_614,A_615,C_616)
      | k1_xboole_0 = '#skF_24'
      | k1_xboole_0 = '#skF_23'
      | k1_xboole_0 = '#skF_22'
      | k1_xboole_0 = '#skF_21'
      | ~ m1_subset_1('#skF_25',k4_zfmisc_1(A_615,B_609,C_616,D_614))
      | k1_xboole_0 = D_614
      | k1_xboole_0 = C_616
      | k1_xboole_0 = B_609
      | k1_xboole_0 = A_615 ) ),
    inference(resolution,[status(thm)],[c_46,c_524])).

tff(c_562,plain,(
    ! [B_617,D_618,A_619,C_620] :
      ( k8_mcart_1('#skF_21','#skF_22','#skF_23','#skF_24','#skF_25') = '#skF_17'(B_617,'#skF_25',D_618,A_619,C_620)
      | ~ m1_subset_1('#skF_25',k4_zfmisc_1(A_619,B_617,C_620,D_618))
      | k1_xboole_0 = D_618
      | k1_xboole_0 = C_620
      | k1_xboole_0 = B_617
      | k1_xboole_0 = A_619 ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_52,c_50,c_48,c_550])).

tff(c_565,plain,
    ( k8_mcart_1('#skF_21','#skF_22','#skF_23','#skF_24','#skF_25') = '#skF_17'('#skF_22','#skF_25','#skF_24','#skF_21','#skF_23')
    | k1_xboole_0 = '#skF_24'
    | k1_xboole_0 = '#skF_23'
    | k1_xboole_0 = '#skF_22'
    | k1_xboole_0 = '#skF_21' ),
    inference(resolution,[status(thm)],[c_46,c_562])).

tff(c_568,plain,(
    k8_mcart_1('#skF_21','#skF_22','#skF_23','#skF_24','#skF_25') = '#skF_17'('#skF_22','#skF_25','#skF_24','#skF_21','#skF_23') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_52,c_50,c_48,c_565])).

tff(c_32,plain,(
    ! [A_296,B_297,D_299,E_300,C_298] :
      ( m1_subset_1(k9_mcart_1(A_296,B_297,C_298,D_299,E_300),B_297)
      | ~ m1_subset_1(E_300,k4_zfmisc_1(A_296,B_297,C_298,D_299)) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_97,plain,(
    ! [G_452,A_454,C_456,I_451,H_450,J_449,B_455,D_453] :
      ( k9_mcart_1(A_454,B_455,C_456,D_453,k4_mcart_1(G_452,H_450,I_451,J_449)) = H_450
      | ~ m1_subset_1(k9_mcart_1(A_454,B_455,C_456,D_453,k4_mcart_1(G_452,H_450,I_451,J_449)),B_455)
      | ~ m1_subset_1(k4_mcart_1(G_452,H_450,I_451,J_449),k4_zfmisc_1(A_454,B_455,C_456,D_453))
      | k1_xboole_0 = D_453
      | k1_xboole_0 = C_456
      | k1_xboole_0 = B_455
      | k1_xboole_0 = A_454 ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_106,plain,(
    ! [D_463,C_461,H_460,G_464,B_457,A_458,J_462,I_459] :
      ( k9_mcart_1(A_458,B_457,C_461,D_463,k4_mcart_1(G_464,H_460,I_459,J_462)) = H_460
      | k1_xboole_0 = D_463
      | k1_xboole_0 = C_461
      | k1_xboole_0 = B_457
      | k1_xboole_0 = A_458
      | ~ m1_subset_1(k4_mcart_1(G_464,H_460,I_459,J_462),k4_zfmisc_1(A_458,B_457,C_461,D_463)) ) ),
    inference(resolution,[status(thm)],[c_32,c_97])).

tff(c_426,plain,(
    ! [B_576,D_575,D_578,E_577,B_573,C_574,A_579,A_580,C_581] :
      ( k9_mcart_1(A_579,B_576,C_574,D_575,k4_mcart_1('#skF_17'(B_573,E_577,D_578,A_580,C_581),'#skF_18'(B_573,E_577,D_578,A_580,C_581),'#skF_19'(B_573,E_577,D_578,A_580,C_581),'#skF_20'(B_573,E_577,D_578,A_580,C_581))) = '#skF_18'(B_573,E_577,D_578,A_580,C_581)
      | k1_xboole_0 = D_575
      | k1_xboole_0 = C_574
      | k1_xboole_0 = B_576
      | k1_xboole_0 = A_579
      | ~ m1_subset_1(E_577,k4_zfmisc_1(A_579,B_576,C_574,D_575))
      | ~ m1_subset_1(E_577,k4_zfmisc_1(A_580,B_573,C_581,D_578))
      | k1_xboole_0 = D_578
      | k1_xboole_0 = C_581
      | k1_xboole_0 = B_573
      | k1_xboole_0 = A_580 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_106])).

tff(c_441,plain,(
    ! [B_585,D_583,A_588,A_589,C_586,D_587,C_590,B_582,E_584] :
      ( k9_mcart_1(A_588,B_585,C_586,D_583,E_584) = '#skF_18'(B_582,E_584,D_587,A_589,C_590)
      | k1_xboole_0 = D_583
      | k1_xboole_0 = C_586
      | k1_xboole_0 = B_585
      | k1_xboole_0 = A_588
      | ~ m1_subset_1(E_584,k4_zfmisc_1(A_588,B_585,C_586,D_583))
      | ~ m1_subset_1(E_584,k4_zfmisc_1(A_589,B_582,C_590,D_587))
      | k1_xboole_0 = D_587
      | k1_xboole_0 = C_590
      | k1_xboole_0 = B_582
      | k1_xboole_0 = A_589
      | ~ m1_subset_1(E_584,k4_zfmisc_1(A_589,B_582,C_590,D_587))
      | k1_xboole_0 = D_587
      | k1_xboole_0 = C_590
      | k1_xboole_0 = B_582
      | k1_xboole_0 = A_589 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_426])).

tff(c_467,plain,(
    ! [B_582,D_587,A_589,C_590] :
      ( k9_mcart_1('#skF_21','#skF_22','#skF_23','#skF_24','#skF_25') = '#skF_18'(B_582,'#skF_25',D_587,A_589,C_590)
      | k1_xboole_0 = '#skF_24'
      | k1_xboole_0 = '#skF_23'
      | k1_xboole_0 = '#skF_22'
      | k1_xboole_0 = '#skF_21'
      | ~ m1_subset_1('#skF_25',k4_zfmisc_1(A_589,B_582,C_590,D_587))
      | k1_xboole_0 = D_587
      | k1_xboole_0 = C_590
      | k1_xboole_0 = B_582
      | k1_xboole_0 = A_589 ) ),
    inference(resolution,[status(thm)],[c_46,c_441])).

tff(c_479,plain,(
    ! [B_591,D_592,A_593,C_594] :
      ( k9_mcart_1('#skF_21','#skF_22','#skF_23','#skF_24','#skF_25') = '#skF_18'(B_591,'#skF_25',D_592,A_593,C_594)
      | ~ m1_subset_1('#skF_25',k4_zfmisc_1(A_593,B_591,C_594,D_592))
      | k1_xboole_0 = D_592
      | k1_xboole_0 = C_594
      | k1_xboole_0 = B_591
      | k1_xboole_0 = A_593 ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_52,c_50,c_48,c_467])).

tff(c_482,plain,
    ( k9_mcart_1('#skF_21','#skF_22','#skF_23','#skF_24','#skF_25') = '#skF_18'('#skF_22','#skF_25','#skF_24','#skF_21','#skF_23')
    | k1_xboole_0 = '#skF_24'
    | k1_xboole_0 = '#skF_23'
    | k1_xboole_0 = '#skF_22'
    | k1_xboole_0 = '#skF_21' ),
    inference(resolution,[status(thm)],[c_46,c_479])).

tff(c_485,plain,(
    k9_mcart_1('#skF_21','#skF_22','#skF_23','#skF_24','#skF_25') = '#skF_18'('#skF_22','#skF_25','#skF_24','#skF_21','#skF_23') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_52,c_50,c_48,c_482])).

tff(c_28,plain,(
    ! [C_288,E_290,D_289,B_287,A_286] :
      ( m1_subset_1(k11_mcart_1(A_286,B_287,C_288,D_289,E_290),D_289)
      | ~ m1_subset_1(E_290,k4_zfmisc_1(A_286,B_287,C_288,D_289)) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_110,plain,(
    ! [C_471,H_470,B_467,A_466,G_465,I_469,J_472,D_468] :
      ( k11_mcart_1(A_466,B_467,C_471,D_468,k4_mcart_1(G_465,H_470,I_469,J_472)) = J_472
      | ~ m1_subset_1(k11_mcart_1(A_466,B_467,C_471,D_468,k4_mcart_1(G_465,H_470,I_469,J_472)),D_468)
      | ~ m1_subset_1(k4_mcart_1(G_465,H_470,I_469,J_472),k4_zfmisc_1(A_466,B_467,C_471,D_468))
      | k1_xboole_0 = D_468
      | k1_xboole_0 = C_471
      | k1_xboole_0 = B_467
      | k1_xboole_0 = A_466 ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_119,plain,(
    ! [J_474,I_477,B_475,G_476,H_473,D_479,C_478,A_480] :
      ( k11_mcart_1(A_480,B_475,C_478,D_479,k4_mcart_1(G_476,H_473,I_477,J_474)) = J_474
      | k1_xboole_0 = D_479
      | k1_xboole_0 = C_478
      | k1_xboole_0 = B_475
      | k1_xboole_0 = A_480
      | ~ m1_subset_1(k4_mcart_1(G_476,H_473,I_477,J_474),k4_zfmisc_1(A_480,B_475,C_478,D_479)) ) ),
    inference(resolution,[status(thm)],[c_28,c_110])).

tff(c_343,plain,(
    ! [B_552,D_551,E_550,D_549,C_555,B_547,C_548,A_553,A_554] :
      ( k11_mcart_1(A_554,B_552,C_548,D_549,k4_mcart_1('#skF_17'(B_547,E_550,D_551,A_553,C_555),'#skF_18'(B_547,E_550,D_551,A_553,C_555),'#skF_19'(B_547,E_550,D_551,A_553,C_555),'#skF_20'(B_547,E_550,D_551,A_553,C_555))) = '#skF_20'(B_547,E_550,D_551,A_553,C_555)
      | k1_xboole_0 = D_549
      | k1_xboole_0 = C_548
      | k1_xboole_0 = B_552
      | k1_xboole_0 = A_554
      | ~ m1_subset_1(E_550,k4_zfmisc_1(A_554,B_552,C_548,D_549))
      | ~ m1_subset_1(E_550,k4_zfmisc_1(A_553,B_547,C_555,D_551))
      | k1_xboole_0 = D_551
      | k1_xboole_0 = C_555
      | k1_xboole_0 = B_547
      | k1_xboole_0 = A_553 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_119])).

tff(c_358,plain,(
    ! [A_562,B_557,D_561,D_558,E_560,C_564,A_559,C_563,B_556] :
      ( k11_mcart_1(A_559,B_556,C_563,D_558,E_560) = '#skF_20'(B_557,E_560,D_561,A_562,C_564)
      | k1_xboole_0 = D_558
      | k1_xboole_0 = C_563
      | k1_xboole_0 = B_556
      | k1_xboole_0 = A_559
      | ~ m1_subset_1(E_560,k4_zfmisc_1(A_559,B_556,C_563,D_558))
      | ~ m1_subset_1(E_560,k4_zfmisc_1(A_562,B_557,C_564,D_561))
      | k1_xboole_0 = D_561
      | k1_xboole_0 = C_564
      | k1_xboole_0 = B_557
      | k1_xboole_0 = A_562
      | ~ m1_subset_1(E_560,k4_zfmisc_1(A_562,B_557,C_564,D_561))
      | k1_xboole_0 = D_561
      | k1_xboole_0 = C_564
      | k1_xboole_0 = B_557
      | k1_xboole_0 = A_562 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_343])).

tff(c_384,plain,(
    ! [B_557,D_561,A_562,C_564] :
      ( k11_mcart_1('#skF_21','#skF_22','#skF_23','#skF_24','#skF_25') = '#skF_20'(B_557,'#skF_25',D_561,A_562,C_564)
      | k1_xboole_0 = '#skF_24'
      | k1_xboole_0 = '#skF_23'
      | k1_xboole_0 = '#skF_22'
      | k1_xboole_0 = '#skF_21'
      | ~ m1_subset_1('#skF_25',k4_zfmisc_1(A_562,B_557,C_564,D_561))
      | k1_xboole_0 = D_561
      | k1_xboole_0 = C_564
      | k1_xboole_0 = B_557
      | k1_xboole_0 = A_562 ) ),
    inference(resolution,[status(thm)],[c_46,c_358])).

tff(c_396,plain,(
    ! [B_565,D_566,A_567,C_568] :
      ( k11_mcart_1('#skF_21','#skF_22','#skF_23','#skF_24','#skF_25') = '#skF_20'(B_565,'#skF_25',D_566,A_567,C_568)
      | ~ m1_subset_1('#skF_25',k4_zfmisc_1(A_567,B_565,C_568,D_566))
      | k1_xboole_0 = D_566
      | k1_xboole_0 = C_568
      | k1_xboole_0 = B_565
      | k1_xboole_0 = A_567 ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_52,c_50,c_48,c_384])).

tff(c_399,plain,
    ( k11_mcart_1('#skF_21','#skF_22','#skF_23','#skF_24','#skF_25') = '#skF_20'('#skF_22','#skF_25','#skF_24','#skF_21','#skF_23')
    | k1_xboole_0 = '#skF_24'
    | k1_xboole_0 = '#skF_23'
    | k1_xboole_0 = '#skF_22'
    | k1_xboole_0 = '#skF_21' ),
    inference(resolution,[status(thm)],[c_46,c_396])).

tff(c_402,plain,(
    k11_mcart_1('#skF_21','#skF_22','#skF_23','#skF_24','#skF_25') = '#skF_20'('#skF_22','#skF_25','#skF_24','#skF_21','#skF_23') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_52,c_50,c_48,c_399])).

tff(c_26,plain,(
    ! [E_285,D_284,C_283,A_281,B_282] :
      ( m1_subset_1(k10_mcart_1(A_281,B_282,C_283,D_284,E_285),C_283)
      | ~ m1_subset_1(E_285,k4_zfmisc_1(A_281,B_282,C_283,D_284)) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_84,plain,(
    ! [B_438,C_439,H_434,A_440,I_433,D_437,J_436,G_435] :
      ( k10_mcart_1(A_440,B_438,C_439,D_437,k4_mcart_1(G_435,H_434,I_433,J_436)) = I_433
      | ~ m1_subset_1(k10_mcart_1(A_440,B_438,C_439,D_437,k4_mcart_1(G_435,H_434,I_433,J_436)),C_439)
      | ~ m1_subset_1(k4_mcart_1(G_435,H_434,I_433,J_436),k4_zfmisc_1(A_440,B_438,C_439,D_437))
      | k1_xboole_0 = D_437
      | k1_xboole_0 = C_439
      | k1_xboole_0 = B_438
      | k1_xboole_0 = A_440 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_93,plain,(
    ! [D_447,H_446,A_441,C_448,B_444,I_443,J_445,G_442] :
      ( k10_mcart_1(A_441,B_444,C_448,D_447,k4_mcart_1(G_442,H_446,I_443,J_445)) = I_443
      | k1_xboole_0 = D_447
      | k1_xboole_0 = C_448
      | k1_xboole_0 = B_444
      | k1_xboole_0 = A_441
      | ~ m1_subset_1(k4_mcart_1(G_442,H_446,I_443,J_445),k4_zfmisc_1(A_441,B_444,C_448,D_447)) ) ),
    inference(resolution,[status(thm)],[c_26,c_84])).

tff(c_260,plain,(
    ! [B_521,D_529,A_523,B_522,D_525,A_527,C_526,C_528,E_524] :
      ( k10_mcart_1(A_523,B_522,C_526,D_529,k4_mcart_1('#skF_17'(B_521,E_524,D_525,A_527,C_528),'#skF_18'(B_521,E_524,D_525,A_527,C_528),'#skF_19'(B_521,E_524,D_525,A_527,C_528),'#skF_20'(B_521,E_524,D_525,A_527,C_528))) = '#skF_19'(B_521,E_524,D_525,A_527,C_528)
      | k1_xboole_0 = D_529
      | k1_xboole_0 = C_526
      | k1_xboole_0 = B_522
      | k1_xboole_0 = A_523
      | ~ m1_subset_1(E_524,k4_zfmisc_1(A_523,B_522,C_526,D_529))
      | ~ m1_subset_1(E_524,k4_zfmisc_1(A_527,B_521,C_528,D_525))
      | k1_xboole_0 = D_525
      | k1_xboole_0 = C_528
      | k1_xboole_0 = B_521
      | k1_xboole_0 = A_527 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_93])).

tff(c_275,plain,(
    ! [C_532,A_536,E_533,A_538,D_535,D_530,C_537,B_531,B_534] :
      ( k10_mcart_1(A_538,B_534,C_532,D_530,E_533) = '#skF_19'(B_531,E_533,D_535,A_536,C_537)
      | k1_xboole_0 = D_530
      | k1_xboole_0 = C_532
      | k1_xboole_0 = B_534
      | k1_xboole_0 = A_538
      | ~ m1_subset_1(E_533,k4_zfmisc_1(A_538,B_534,C_532,D_530))
      | ~ m1_subset_1(E_533,k4_zfmisc_1(A_536,B_531,C_537,D_535))
      | k1_xboole_0 = D_535
      | k1_xboole_0 = C_537
      | k1_xboole_0 = B_531
      | k1_xboole_0 = A_536
      | ~ m1_subset_1(E_533,k4_zfmisc_1(A_536,B_531,C_537,D_535))
      | k1_xboole_0 = D_535
      | k1_xboole_0 = C_537
      | k1_xboole_0 = B_531
      | k1_xboole_0 = A_536 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_260])).

tff(c_301,plain,(
    ! [B_531,D_535,A_536,C_537] :
      ( k10_mcart_1('#skF_21','#skF_22','#skF_23','#skF_24','#skF_25') = '#skF_19'(B_531,'#skF_25',D_535,A_536,C_537)
      | k1_xboole_0 = '#skF_24'
      | k1_xboole_0 = '#skF_23'
      | k1_xboole_0 = '#skF_22'
      | k1_xboole_0 = '#skF_21'
      | ~ m1_subset_1('#skF_25',k4_zfmisc_1(A_536,B_531,C_537,D_535))
      | k1_xboole_0 = D_535
      | k1_xboole_0 = C_537
      | k1_xboole_0 = B_531
      | k1_xboole_0 = A_536 ) ),
    inference(resolution,[status(thm)],[c_46,c_275])).

tff(c_313,plain,(
    ! [B_539,D_540,A_541,C_542] :
      ( k10_mcart_1('#skF_21','#skF_22','#skF_23','#skF_24','#skF_25') = '#skF_19'(B_539,'#skF_25',D_540,A_541,C_542)
      | ~ m1_subset_1('#skF_25',k4_zfmisc_1(A_541,B_539,C_542,D_540))
      | k1_xboole_0 = D_540
      | k1_xboole_0 = C_542
      | k1_xboole_0 = B_539
      | k1_xboole_0 = A_541 ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_52,c_50,c_48,c_301])).

tff(c_316,plain,
    ( k10_mcart_1('#skF_21','#skF_22','#skF_23','#skF_24','#skF_25') = '#skF_19'('#skF_22','#skF_25','#skF_24','#skF_21','#skF_23')
    | k1_xboole_0 = '#skF_24'
    | k1_xboole_0 = '#skF_23'
    | k1_xboole_0 = '#skF_22'
    | k1_xboole_0 = '#skF_21' ),
    inference(resolution,[status(thm)],[c_46,c_313])).

tff(c_319,plain,(
    k10_mcart_1('#skF_21','#skF_22','#skF_23','#skF_24','#skF_25') = '#skF_19'('#skF_22','#skF_25','#skF_24','#skF_21','#skF_23') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_52,c_50,c_48,c_316])).

tff(c_44,plain,(
    k4_mcart_1(k8_mcart_1('#skF_21','#skF_22','#skF_23','#skF_24','#skF_25'),k9_mcart_1('#skF_21','#skF_22','#skF_23','#skF_24','#skF_25'),k10_mcart_1('#skF_21','#skF_22','#skF_23','#skF_24','#skF_25'),k11_mcart_1('#skF_21','#skF_22','#skF_23','#skF_24','#skF_25')) != '#skF_25' ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_321,plain,(
    k4_mcart_1(k8_mcart_1('#skF_21','#skF_22','#skF_23','#skF_24','#skF_25'),k9_mcart_1('#skF_21','#skF_22','#skF_23','#skF_24','#skF_25'),'#skF_19'('#skF_22','#skF_25','#skF_24','#skF_21','#skF_23'),k11_mcart_1('#skF_21','#skF_22','#skF_23','#skF_24','#skF_25')) != '#skF_25' ),
    inference(demodulation,[status(thm),theory(equality)],[c_319,c_44])).

tff(c_404,plain,(
    k4_mcart_1(k8_mcart_1('#skF_21','#skF_22','#skF_23','#skF_24','#skF_25'),k9_mcart_1('#skF_21','#skF_22','#skF_23','#skF_24','#skF_25'),'#skF_19'('#skF_22','#skF_25','#skF_24','#skF_21','#skF_23'),'#skF_20'('#skF_22','#skF_25','#skF_24','#skF_21','#skF_23')) != '#skF_25' ),
    inference(demodulation,[status(thm),theory(equality)],[c_402,c_321])).

tff(c_487,plain,(
    k4_mcart_1(k8_mcart_1('#skF_21','#skF_22','#skF_23','#skF_24','#skF_25'),'#skF_18'('#skF_22','#skF_25','#skF_24','#skF_21','#skF_23'),'#skF_19'('#skF_22','#skF_25','#skF_24','#skF_21','#skF_23'),'#skF_20'('#skF_22','#skF_25','#skF_24','#skF_21','#skF_23')) != '#skF_25' ),
    inference(demodulation,[status(thm),theory(equality)],[c_485,c_404])).

tff(c_570,plain,(
    k4_mcart_1('#skF_17'('#skF_22','#skF_25','#skF_24','#skF_21','#skF_23'),'#skF_18'('#skF_22','#skF_25','#skF_24','#skF_21','#skF_23'),'#skF_19'('#skF_22','#skF_25','#skF_24','#skF_21','#skF_23'),'#skF_20'('#skF_22','#skF_25','#skF_24','#skF_21','#skF_23')) != '#skF_25' ),
    inference(demodulation,[status(thm),theory(equality)],[c_568,c_487])).

tff(c_590,plain,
    ( ~ m1_subset_1('#skF_25',k4_zfmisc_1('#skF_21','#skF_22','#skF_23','#skF_24'))
    | k1_xboole_0 = '#skF_24'
    | k1_xboole_0 = '#skF_23'
    | k1_xboole_0 = '#skF_22'
    | k1_xboole_0 = '#skF_21' ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_570])).

tff(c_593,plain,
    ( k1_xboole_0 = '#skF_24'
    | k1_xboole_0 = '#skF_23'
    | k1_xboole_0 = '#skF_22'
    | k1_xboole_0 = '#skF_21' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_590])).

tff(c_595,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_52,c_50,c_48,c_593])).

%------------------------------------------------------------------------------
