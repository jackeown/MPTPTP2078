%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.QHjSIHhtWN

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:26 EST 2020

% Result     : Theorem 0.90s
% Output     : Refutation 0.90s
% Verified   : 
% Statistics : Number of formulae       :  163 (1683 expanded)
%              Number of leaves         :   34 ( 505 expanded)
%              Depth                    :   24
%              Number of atoms          :  969 (16509 expanded)
%              Number of equality atoms :  149 (2870 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
    ! [X4: $i] :
      ( ( v1_xboole_0 @ X4 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('1',plain,(
    ! [X59: $i,X60: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X59 ) @ X60 )
      | ( r2_hidden @ X59 @ X60 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf(t43_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( ( k1_tarski @ A )
          = ( k2_xboole_0 @ B @ C ) )
        & ~ ( ( B
              = ( k1_tarski @ A ) )
            & ( C
              = ( k1_tarski @ A ) ) )
        & ~ ( ( B = k1_xboole_0 )
            & ( C
              = ( k1_tarski @ A ) ) )
        & ~ ( ( B
              = ( k1_tarski @ A ) )
            & ( C = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ( ( k1_tarski @ A )
            = ( k2_xboole_0 @ B @ C ) )
          & ~ ( ( B
                = ( k1_tarski @ A ) )
              & ( C
                = ( k1_tarski @ A ) ) )
          & ~ ( ( B = k1_xboole_0 )
              & ( C
                = ( k1_tarski @ A ) ) )
          & ~ ( ( B
                = ( k1_tarski @ A ) )
              & ( C = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t43_zfmisc_1])).

thf('2',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X29: $i,X30: $i] :
      ( r1_tarski @ X29 @ ( k2_xboole_0 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('4',plain,(
    r1_tarski @ sk_B_1 @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('5',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k3_xboole_0 @ X23 @ X24 )
        = X23 )
      | ~ ( r1_tarski @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('6',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['4','5'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('8',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ ( k3_xboole_0 @ X6 @ X9 ) )
      | ~ ( r1_xboole_0 @ X6 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_A @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['1','10'])).

thf('12',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['0','11'])).

thf(l31_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k3_xboole_0 @ B @ ( k1_tarski @ A ) )
        = ( k1_tarski @ A ) ) ) )).

thf('13',plain,(
    ! [X61: $i,X62: $i] :
      ( ( ( k3_xboole_0 @ X62 @ ( k1_tarski @ X61 ) )
        = ( k1_tarski @ X61 ) )
      | ~ ( r2_hidden @ X61 @ X62 ) ) ),
    inference(cnf,[status(esa)],[l31_zfmisc_1])).

thf('14',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( ( k3_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['4','5'])).

thf('16',plain,
    ( ( ( k1_tarski @ sk_A )
      = sk_B_1 )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('18',plain,(
    ! [X25: $i] :
      ( ( k3_xboole_0 @ X25 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('19',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k3_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('21',plain,(
    ! [X28: $i] :
      ( ( k5_xboole_0 @ X28 @ k1_xboole_0 )
      = X28 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['20','21'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('23',plain,(
    ! [X26: $i,X27: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X26 @ X27 ) @ X26 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('25',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ X15 @ X16 )
      | ( r1_tarski @ X15 @ ( k2_xboole_0 @ X17 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    r1_tarski @ sk_C_1 @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['17','26'])).

thf('28',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k3_xboole_0 @ X23 @ X24 )
        = X23 )
      | ~ ( r1_tarski @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('29',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ ( k1_tarski @ sk_A ) )
    = sk_C_1 ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( ( k3_xboole_0 @ sk_C_1 @ sk_B_1 )
      = sk_C_1 )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['16','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('32',plain,
    ( ( ( k3_xboole_0 @ sk_B_1 @ sk_C_1 )
      = sk_C_1 )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['30','31'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('33',plain,(
    ! [X5: $i] :
      ( ( X5 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('34',plain,(
    ! [X29: $i,X30: $i] :
      ( r1_tarski @ X29 @ ( k2_xboole_0 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('35',plain,(
    ! [X10: $i,X12: $i] :
      ( ( ( k4_xboole_0 @ X10 @ X12 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X26: $i,X27: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X26 @ X27 ) @ X26 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('38',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k2_xboole_0 @ X19 @ X18 )
        = X18 )
      | ~ ( r1_tarski @ X19 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['36','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_xboole_0 @ X0 @ X1 )
        = X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['33','40'])).

thf('42',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( ( k1_tarski @ sk_A )
      = sk_C_1 )
    | ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( sk_B_1 != k1_xboole_0 )
    | ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( sk_C_1
     != ( k1_tarski @ sk_A ) )
   <= ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['44'])).

thf('46',plain,
    ( ( sk_C_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['44'])).

thf('47',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( sk_C_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['47'])).

thf('49',plain,
    ( ( ( k1_tarski @ sk_A )
      = sk_B_1 )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('50',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_1 != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['50'])).

thf('52',plain,
    ( ( ( sk_B_1 != sk_B_1 )
      | ( v1_xboole_0 @ sk_B_1 ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['49','51'])).

thf('53',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ! [X5: $i] :
      ( ( X5 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('55',plain,
    ( ( sk_B_1 != k1_xboole_0 )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['44'])).

thf('56',plain,
    ( ! [X0: $i] :
        ( ( sk_B_1 != X0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_B_1
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['53','57'])).

thf('59',plain,(
    sk_C_1
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['46','48','58'])).

thf('60',plain,(
    sk_C_1
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['45','59'])).

thf('61',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('simplify_reflect-',[status(thm)],['43','60'])).

thf('62',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ sk_C_1 )
    = sk_C_1 ),
    inference(clc,[status(thm)],['32','61'])).

thf('63',plain,(
    ! [X4: $i] :
      ( ( v1_xboole_0 @ X4 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('64',plain,(
    ! [X59: $i,X60: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X59 ) @ X60 )
      | ( r2_hidden @ X59 @ X60 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf('65',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ ( k1_tarski @ sk_A ) )
    = sk_C_1 ),
    inference('sup-',[status(thm)],['27','28'])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_C_1 )
      | ~ ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_A @ sk_C_1 )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['64','67'])).

thf('69',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
    | ( r2_hidden @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['63','68'])).

thf('70',plain,
    ( ( ( k1_tarski @ sk_A )
      = sk_B_1 )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('71',plain,(
    ! [X31: $i] :
      ( ( k2_tarski @ X31 @ X31 )
      = ( k1_tarski @ X31 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('72',plain,(
    ! [X63: $i,X64: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X63 @ X64 ) )
      = ( k2_xboole_0 @ X63 @ X64 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['73','76'])).

thf('78',plain,
    ( ( ( k3_tarski @ sk_B_1 )
      = sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['70','77'])).

thf('79',plain,
    ( ( ( k1_tarski @ sk_A )
      = sk_C_1 )
    | ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('80',plain,
    ( ( ( k3_tarski @ sk_B_1 )
      = sk_A )
    | ( ( k1_tarski @ sk_A )
      = sk_C_1 ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    sk_C_1
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['45','59'])).

thf('82',plain,
    ( ( k3_tarski @ sk_B_1 )
    = sk_A ),
    inference('simplify_reflect-',[status(thm)],['80','81'])).

thf('83',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
    | ( r2_hidden @ ( k3_tarski @ sk_B_1 ) @ sk_C_1 ) ),
    inference(demod,[status(thm)],['69','82'])).

thf('84',plain,(
    ! [X5: $i] :
      ( ( X5 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('85',plain,
    ( ( sk_C_1 != k1_xboole_0 )
   <= ( sk_C_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['50'])).

thf('86',plain,
    ( ! [X0: $i] :
        ( ( sk_C_1 != X0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( sk_C_1 != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,
    ( ~ ( v1_xboole_0 @ sk_C_1 )
   <= ( sk_C_1 != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('90',plain,
    ( ( ( k1_tarski @ sk_A )
      = sk_C_1 )
    | ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('91',plain,
    ( ( ( k1_tarski @ sk_A )
      = sk_C_1 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    r1_tarski @ sk_B_1 @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('93',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k2_xboole_0 @ X19 @ X18 )
        = X18 )
      | ~ ( r1_tarski @ X19 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('94',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,
    ( ( ( k2_xboole_0 @ sk_B_1 @ sk_C_1 )
      = ( k1_tarski @ sk_A ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['91','94'])).

thf('96',plain,
    ( ( ( k1_tarski @ sk_A )
      = sk_C_1 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('97',plain,
    ( ( ( k2_xboole_0 @ sk_B_1 @ sk_C_1 )
      = sk_C_1 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,
    ( ( ( k1_tarski @ sk_A )
      = sk_C_1 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['88','97'])).

thf('99',plain,
    ( ( ( k1_tarski @ sk_A )
      = sk_C_1 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['73','76'])).

thf('101',plain,
    ( ( ( k3_tarski @ sk_C_1 )
      = sk_A )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['99','100'])).

thf('102',plain,
    ( ( ( k1_tarski @ ( k3_tarski @ sk_C_1 ) )
      = sk_C_1 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['98','101'])).

thf('103',plain,
    ( ( ( k3_tarski @ sk_C_1 )
      = sk_A )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['99','100'])).

thf('104',plain,(
    sk_C_1
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['45','59'])).

thf('105',plain,
    ( ( sk_C_1
     != ( k1_tarski @ ( k3_tarski @ sk_C_1 ) ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,
    ( sk_B_1
    = ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['102','105'])).

thf('107',plain,
    ( ( sk_C_1 != k1_xboole_0 )
    | ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['50'])).

thf('108',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['106','107'])).

thf('109',plain,(
    ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['87','108'])).

thf('110',plain,(
    r2_hidden @ ( k3_tarski @ sk_B_1 ) @ sk_C_1 ),
    inference(clc,[status(thm)],['83','109'])).

thf('111',plain,(
    ! [X61: $i,X62: $i] :
      ( ( ( k3_xboole_0 @ X62 @ ( k1_tarski @ X61 ) )
        = ( k1_tarski @ X61 ) )
      | ~ ( r2_hidden @ X61 @ X62 ) ) ),
    inference(cnf,[status(esa)],[l31_zfmisc_1])).

thf('112',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ ( k1_tarski @ ( k3_tarski @ sk_B_1 ) ) )
    = ( k1_tarski @ ( k3_tarski @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,
    ( ( ( k1_tarski @ sk_A )
      = sk_B_1 )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('114',plain,
    ( ( k3_tarski @ sk_B_1 )
    = sk_A ),
    inference('simplify_reflect-',[status(thm)],['80','81'])).

thf('115',plain,
    ( ( ( k1_tarski @ ( k3_tarski @ sk_B_1 ) )
      = sk_B_1 )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['113','114'])).

thf('116',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('simplify_reflect-',[status(thm)],['43','60'])).

thf('117',plain,
    ( ( k1_tarski @ ( k3_tarski @ sk_B_1 ) )
    = sk_B_1 ),
    inference(clc,[status(thm)],['115','116'])).

thf('118',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('119',plain,
    ( ( k1_tarski @ ( k3_tarski @ sk_B_1 ) )
    = sk_B_1 ),
    inference(clc,[status(thm)],['115','116'])).

thf('120',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ sk_C_1 )
    = sk_B_1 ),
    inference(demod,[status(thm)],['112','117','118','119'])).

thf('121',plain,(
    sk_C_1 = sk_B_1 ),
    inference('sup+',[status(thm)],['62','120'])).

thf('122',plain,(
    sk_C_1
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['45','59'])).

thf('123',plain,
    ( ( k3_tarski @ sk_B_1 )
    = sk_A ),
    inference('simplify_reflect-',[status(thm)],['80','81'])).

thf('124',plain,(
    sk_C_1
 != ( k1_tarski @ ( k3_tarski @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['122','123'])).

thf('125',plain,
    ( ( k1_tarski @ ( k3_tarski @ sk_B_1 ) )
    = sk_B_1 ),
    inference(clc,[status(thm)],['115','116'])).

thf('126',plain,(
    sk_C_1 != sk_B_1 ),
    inference(demod,[status(thm)],['124','125'])).

thf('127',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['121','126'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.QHjSIHhtWN
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:37:26 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.90/1.11  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.90/1.11  % Solved by: fo/fo7.sh
% 0.90/1.11  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.90/1.11  % done 2002 iterations in 0.586s
% 0.90/1.11  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.90/1.11  % SZS output start Refutation
% 0.90/1.11  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.90/1.11  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.90/1.11  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.90/1.11  thf(sk_A_type, type, sk_A: $i).
% 0.90/1.11  thf(sk_B_type, type, sk_B: $i > $i).
% 0.90/1.11  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.90/1.11  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.90/1.11  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.90/1.11  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.90/1.11  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.90/1.11  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.90/1.11  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.90/1.11  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.90/1.11  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.90/1.11  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.90/1.11  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.90/1.11  thf(d1_xboole_0, axiom,
% 0.90/1.11    (![A:$i]:
% 0.90/1.11     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.90/1.11  thf('0', plain,
% 0.90/1.11      (![X4 : $i]: ((v1_xboole_0 @ X4) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.90/1.11      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.90/1.11  thf(l27_zfmisc_1, axiom,
% 0.90/1.11    (![A:$i,B:$i]:
% 0.90/1.11     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.90/1.11  thf('1', plain,
% 0.90/1.11      (![X59 : $i, X60 : $i]:
% 0.90/1.11         ((r1_xboole_0 @ (k1_tarski @ X59) @ X60) | (r2_hidden @ X59 @ X60))),
% 0.90/1.11      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.90/1.11  thf(t43_zfmisc_1, conjecture,
% 0.90/1.11    (![A:$i,B:$i,C:$i]:
% 0.90/1.11     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.90/1.11          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.90/1.11          ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.90/1.11          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.90/1.11  thf(zf_stmt_0, negated_conjecture,
% 0.90/1.11    (~( ![A:$i,B:$i,C:$i]:
% 0.90/1.11        ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.90/1.11             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.90/1.11             ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.90/1.11             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 0.90/1.11    inference('cnf.neg', [status(esa)], [t43_zfmisc_1])).
% 0.90/1.11  thf('2', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 0.90/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.11  thf(t7_xboole_1, axiom,
% 0.90/1.11    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.90/1.11  thf('3', plain,
% 0.90/1.11      (![X29 : $i, X30 : $i]: (r1_tarski @ X29 @ (k2_xboole_0 @ X29 @ X30))),
% 0.90/1.11      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.90/1.11  thf('4', plain, ((r1_tarski @ sk_B_1 @ (k1_tarski @ sk_A))),
% 0.90/1.11      inference('sup+', [status(thm)], ['2', '3'])).
% 0.90/1.11  thf(t28_xboole_1, axiom,
% 0.90/1.11    (![A:$i,B:$i]:
% 0.90/1.11     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.90/1.11  thf('5', plain,
% 0.90/1.11      (![X23 : $i, X24 : $i]:
% 0.90/1.11         (((k3_xboole_0 @ X23 @ X24) = (X23)) | ~ (r1_tarski @ X23 @ X24))),
% 0.90/1.11      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.90/1.11  thf('6', plain, (((k3_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) = (sk_B_1))),
% 0.90/1.11      inference('sup-', [status(thm)], ['4', '5'])).
% 0.90/1.11  thf(commutativity_k3_xboole_0, axiom,
% 0.90/1.11    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.90/1.11  thf('7', plain,
% 0.90/1.11      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.90/1.11      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.90/1.11  thf(t4_xboole_0, axiom,
% 0.90/1.11    (![A:$i,B:$i]:
% 0.90/1.11     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.90/1.11            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.90/1.11       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.90/1.11            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.90/1.11  thf('8', plain,
% 0.90/1.11      (![X6 : $i, X8 : $i, X9 : $i]:
% 0.90/1.11         (~ (r2_hidden @ X8 @ (k3_xboole_0 @ X6 @ X9))
% 0.90/1.11          | ~ (r1_xboole_0 @ X6 @ X9))),
% 0.90/1.11      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.90/1.11  thf('9', plain,
% 0.90/1.11      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.11         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.90/1.11          | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.90/1.11      inference('sup-', [status(thm)], ['7', '8'])).
% 0.90/1.11  thf('10', plain,
% 0.90/1.11      (![X0 : $i]:
% 0.90/1.11         (~ (r2_hidden @ X0 @ sk_B_1)
% 0.90/1.11          | ~ (r1_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1))),
% 0.90/1.11      inference('sup-', [status(thm)], ['6', '9'])).
% 0.90/1.11  thf('11', plain,
% 0.90/1.11      (![X0 : $i]: ((r2_hidden @ sk_A @ sk_B_1) | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.90/1.11      inference('sup-', [status(thm)], ['1', '10'])).
% 0.90/1.11  thf('12', plain, (((v1_xboole_0 @ sk_B_1) | (r2_hidden @ sk_A @ sk_B_1))),
% 0.90/1.11      inference('sup-', [status(thm)], ['0', '11'])).
% 0.90/1.11  thf(l31_zfmisc_1, axiom,
% 0.90/1.11    (![A:$i,B:$i]:
% 0.90/1.11     ( ( r2_hidden @ A @ B ) =>
% 0.90/1.11       ( ( k3_xboole_0 @ B @ ( k1_tarski @ A ) ) = ( k1_tarski @ A ) ) ))).
% 0.90/1.11  thf('13', plain,
% 0.90/1.11      (![X61 : $i, X62 : $i]:
% 0.90/1.11         (((k3_xboole_0 @ X62 @ (k1_tarski @ X61)) = (k1_tarski @ X61))
% 0.90/1.11          | ~ (r2_hidden @ X61 @ X62))),
% 0.90/1.11      inference('cnf', [status(esa)], [l31_zfmisc_1])).
% 0.90/1.11  thf('14', plain,
% 0.90/1.11      (((v1_xboole_0 @ sk_B_1)
% 0.90/1.11        | ((k3_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A)))),
% 0.90/1.11      inference('sup-', [status(thm)], ['12', '13'])).
% 0.90/1.11  thf('15', plain, (((k3_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) = (sk_B_1))),
% 0.90/1.11      inference('sup-', [status(thm)], ['4', '5'])).
% 0.90/1.11  thf('16', plain,
% 0.90/1.11      ((((k1_tarski @ sk_A) = (sk_B_1)) | (v1_xboole_0 @ sk_B_1))),
% 0.90/1.11      inference('sup+', [status(thm)], ['14', '15'])).
% 0.90/1.11  thf('17', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 0.90/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.11  thf(t2_boole, axiom,
% 0.90/1.11    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.90/1.11  thf('18', plain,
% 0.90/1.11      (![X25 : $i]: ((k3_xboole_0 @ X25 @ k1_xboole_0) = (k1_xboole_0))),
% 0.90/1.11      inference('cnf', [status(esa)], [t2_boole])).
% 0.90/1.11  thf(t100_xboole_1, axiom,
% 0.90/1.11    (![A:$i,B:$i]:
% 0.90/1.11     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.90/1.11  thf('19', plain,
% 0.90/1.11      (![X13 : $i, X14 : $i]:
% 0.90/1.11         ((k4_xboole_0 @ X13 @ X14)
% 0.90/1.11           = (k5_xboole_0 @ X13 @ (k3_xboole_0 @ X13 @ X14)))),
% 0.90/1.11      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.90/1.11  thf('20', plain,
% 0.90/1.11      (![X0 : $i]:
% 0.90/1.11         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.90/1.11      inference('sup+', [status(thm)], ['18', '19'])).
% 0.90/1.11  thf(t5_boole, axiom,
% 0.90/1.11    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.90/1.11  thf('21', plain, (![X28 : $i]: ((k5_xboole_0 @ X28 @ k1_xboole_0) = (X28))),
% 0.90/1.11      inference('cnf', [status(esa)], [t5_boole])).
% 0.90/1.11  thf('22', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.90/1.11      inference('demod', [status(thm)], ['20', '21'])).
% 0.90/1.11  thf(t36_xboole_1, axiom,
% 0.90/1.11    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.90/1.11  thf('23', plain,
% 0.90/1.11      (![X26 : $i, X27 : $i]: (r1_tarski @ (k4_xboole_0 @ X26 @ X27) @ X26)),
% 0.90/1.11      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.90/1.11  thf('24', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.90/1.11      inference('sup+', [status(thm)], ['22', '23'])).
% 0.90/1.11  thf(t10_xboole_1, axiom,
% 0.90/1.11    (![A:$i,B:$i,C:$i]:
% 0.90/1.11     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 0.90/1.11  thf('25', plain,
% 0.90/1.11      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.90/1.11         (~ (r1_tarski @ X15 @ X16)
% 0.90/1.11          | (r1_tarski @ X15 @ (k2_xboole_0 @ X17 @ X16)))),
% 0.90/1.11      inference('cnf', [status(esa)], [t10_xboole_1])).
% 0.90/1.11  thf('26', plain,
% 0.90/1.11      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.90/1.11      inference('sup-', [status(thm)], ['24', '25'])).
% 0.90/1.11  thf('27', plain, ((r1_tarski @ sk_C_1 @ (k1_tarski @ sk_A))),
% 0.90/1.11      inference('sup+', [status(thm)], ['17', '26'])).
% 0.90/1.11  thf('28', plain,
% 0.90/1.11      (![X23 : $i, X24 : $i]:
% 0.90/1.11         (((k3_xboole_0 @ X23 @ X24) = (X23)) | ~ (r1_tarski @ X23 @ X24))),
% 0.90/1.11      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.90/1.11  thf('29', plain, (((k3_xboole_0 @ sk_C_1 @ (k1_tarski @ sk_A)) = (sk_C_1))),
% 0.90/1.11      inference('sup-', [status(thm)], ['27', '28'])).
% 0.90/1.11  thf('30', plain,
% 0.90/1.11      ((((k3_xboole_0 @ sk_C_1 @ sk_B_1) = (sk_C_1)) | (v1_xboole_0 @ sk_B_1))),
% 0.90/1.11      inference('sup+', [status(thm)], ['16', '29'])).
% 0.90/1.11  thf('31', plain,
% 0.90/1.11      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.90/1.11      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.90/1.11  thf('32', plain,
% 0.90/1.11      ((((k3_xboole_0 @ sk_B_1 @ sk_C_1) = (sk_C_1)) | (v1_xboole_0 @ sk_B_1))),
% 0.90/1.11      inference('demod', [status(thm)], ['30', '31'])).
% 0.90/1.11  thf(l13_xboole_0, axiom,
% 0.90/1.11    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.90/1.11  thf('33', plain,
% 0.90/1.11      (![X5 : $i]: (((X5) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X5))),
% 0.90/1.11      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.90/1.11  thf('34', plain,
% 0.90/1.11      (![X29 : $i, X30 : $i]: (r1_tarski @ X29 @ (k2_xboole_0 @ X29 @ X30))),
% 0.90/1.11      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.90/1.11  thf(l32_xboole_1, axiom,
% 0.90/1.11    (![A:$i,B:$i]:
% 0.90/1.11     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.90/1.11  thf('35', plain,
% 0.90/1.11      (![X10 : $i, X12 : $i]:
% 0.90/1.11         (((k4_xboole_0 @ X10 @ X12) = (k1_xboole_0))
% 0.90/1.11          | ~ (r1_tarski @ X10 @ X12))),
% 0.90/1.11      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.90/1.11  thf('36', plain,
% 0.90/1.11      (![X0 : $i, X1 : $i]:
% 0.90/1.11         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.90/1.11      inference('sup-', [status(thm)], ['34', '35'])).
% 0.90/1.11  thf('37', plain,
% 0.90/1.11      (![X26 : $i, X27 : $i]: (r1_tarski @ (k4_xboole_0 @ X26 @ X27) @ X26)),
% 0.90/1.11      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.90/1.11  thf(t12_xboole_1, axiom,
% 0.90/1.11    (![A:$i,B:$i]:
% 0.90/1.11     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.90/1.11  thf('38', plain,
% 0.90/1.11      (![X18 : $i, X19 : $i]:
% 0.90/1.11         (((k2_xboole_0 @ X19 @ X18) = (X18)) | ~ (r1_tarski @ X19 @ X18))),
% 0.90/1.11      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.90/1.11  thf('39', plain,
% 0.90/1.11      (![X0 : $i, X1 : $i]:
% 0.90/1.11         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 0.90/1.11      inference('sup-', [status(thm)], ['37', '38'])).
% 0.90/1.11  thf('40', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.90/1.11      inference('sup+', [status(thm)], ['36', '39'])).
% 0.90/1.11  thf('41', plain,
% 0.90/1.11      (![X0 : $i, X1 : $i]:
% 0.90/1.11         (((k2_xboole_0 @ X0 @ X1) = (X1)) | ~ (v1_xboole_0 @ X0))),
% 0.90/1.11      inference('sup+', [status(thm)], ['33', '40'])).
% 0.90/1.11  thf('42', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 0.90/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.11  thf('43', plain,
% 0.90/1.11      ((((k1_tarski @ sk_A) = (sk_C_1)) | ~ (v1_xboole_0 @ sk_B_1))),
% 0.90/1.11      inference('sup+', [status(thm)], ['41', '42'])).
% 0.90/1.11  thf('44', plain,
% 0.90/1.11      ((((sk_B_1) != (k1_xboole_0)) | ((sk_C_1) != (k1_tarski @ sk_A)))),
% 0.90/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.11  thf('45', plain,
% 0.90/1.11      ((((sk_C_1) != (k1_tarski @ sk_A)))
% 0.90/1.11         <= (~ (((sk_C_1) = (k1_tarski @ sk_A))))),
% 0.90/1.11      inference('split', [status(esa)], ['44'])).
% 0.90/1.11  thf('46', plain,
% 0.90/1.11      (~ (((sk_C_1) = (k1_tarski @ sk_A))) | ~ (((sk_B_1) = (k1_xboole_0)))),
% 0.90/1.11      inference('split', [status(esa)], ['44'])).
% 0.90/1.11  thf('47', plain,
% 0.90/1.11      ((((sk_B_1) != (k1_tarski @ sk_A)) | ((sk_C_1) != (k1_tarski @ sk_A)))),
% 0.90/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.11  thf('48', plain,
% 0.90/1.11      (~ (((sk_C_1) = (k1_tarski @ sk_A))) | 
% 0.90/1.11       ~ (((sk_B_1) = (k1_tarski @ sk_A)))),
% 0.90/1.11      inference('split', [status(esa)], ['47'])).
% 0.90/1.11  thf('49', plain,
% 0.90/1.11      ((((k1_tarski @ sk_A) = (sk_B_1)) | (v1_xboole_0 @ sk_B_1))),
% 0.90/1.11      inference('sup+', [status(thm)], ['14', '15'])).
% 0.90/1.11  thf('50', plain,
% 0.90/1.11      ((((sk_B_1) != (k1_tarski @ sk_A)) | ((sk_C_1) != (k1_xboole_0)))),
% 0.90/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.11  thf('51', plain,
% 0.90/1.11      ((((sk_B_1) != (k1_tarski @ sk_A)))
% 0.90/1.11         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.90/1.11      inference('split', [status(esa)], ['50'])).
% 0.90/1.11  thf('52', plain,
% 0.90/1.11      (((((sk_B_1) != (sk_B_1)) | (v1_xboole_0 @ sk_B_1)))
% 0.90/1.11         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.90/1.11      inference('sup-', [status(thm)], ['49', '51'])).
% 0.90/1.11  thf('53', plain,
% 0.90/1.11      (((v1_xboole_0 @ sk_B_1)) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.90/1.11      inference('simplify', [status(thm)], ['52'])).
% 0.90/1.11  thf('54', plain,
% 0.90/1.11      (![X5 : $i]: (((X5) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X5))),
% 0.90/1.11      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.90/1.11  thf('55', plain,
% 0.90/1.11      ((((sk_B_1) != (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 0.90/1.11      inference('split', [status(esa)], ['44'])).
% 0.90/1.11  thf('56', plain,
% 0.90/1.11      ((![X0 : $i]: (((sk_B_1) != (X0)) | ~ (v1_xboole_0 @ X0)))
% 0.90/1.11         <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 0.90/1.11      inference('sup-', [status(thm)], ['54', '55'])).
% 0.90/1.11  thf('57', plain,
% 0.90/1.11      ((~ (v1_xboole_0 @ sk_B_1)) <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 0.90/1.11      inference('simplify', [status(thm)], ['56'])).
% 0.90/1.11  thf('58', plain,
% 0.90/1.11      ((((sk_B_1) = (k1_xboole_0))) | (((sk_B_1) = (k1_tarski @ sk_A)))),
% 0.90/1.11      inference('sup-', [status(thm)], ['53', '57'])).
% 0.90/1.11  thf('59', plain, (~ (((sk_C_1) = (k1_tarski @ sk_A)))),
% 0.90/1.11      inference('sat_resolution*', [status(thm)], ['46', '48', '58'])).
% 0.90/1.11  thf('60', plain, (((sk_C_1) != (k1_tarski @ sk_A))),
% 0.90/1.11      inference('simpl_trail', [status(thm)], ['45', '59'])).
% 0.90/1.11  thf('61', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.90/1.11      inference('simplify_reflect-', [status(thm)], ['43', '60'])).
% 0.90/1.11  thf('62', plain, (((k3_xboole_0 @ sk_B_1 @ sk_C_1) = (sk_C_1))),
% 0.90/1.11      inference('clc', [status(thm)], ['32', '61'])).
% 0.90/1.11  thf('63', plain,
% 0.90/1.11      (![X4 : $i]: ((v1_xboole_0 @ X4) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.90/1.11      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.90/1.11  thf('64', plain,
% 0.90/1.11      (![X59 : $i, X60 : $i]:
% 0.90/1.11         ((r1_xboole_0 @ (k1_tarski @ X59) @ X60) | (r2_hidden @ X59 @ X60))),
% 0.90/1.11      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.90/1.11  thf('65', plain, (((k3_xboole_0 @ sk_C_1 @ (k1_tarski @ sk_A)) = (sk_C_1))),
% 0.90/1.11      inference('sup-', [status(thm)], ['27', '28'])).
% 0.90/1.11  thf('66', plain,
% 0.90/1.11      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.11         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.90/1.11          | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.90/1.11      inference('sup-', [status(thm)], ['7', '8'])).
% 0.90/1.11  thf('67', plain,
% 0.90/1.11      (![X0 : $i]:
% 0.90/1.11         (~ (r2_hidden @ X0 @ sk_C_1)
% 0.90/1.11          | ~ (r1_xboole_0 @ (k1_tarski @ sk_A) @ sk_C_1))),
% 0.90/1.11      inference('sup-', [status(thm)], ['65', '66'])).
% 0.90/1.11  thf('68', plain,
% 0.90/1.11      (![X0 : $i]: ((r2_hidden @ sk_A @ sk_C_1) | ~ (r2_hidden @ X0 @ sk_C_1))),
% 0.90/1.11      inference('sup-', [status(thm)], ['64', '67'])).
% 0.90/1.11  thf('69', plain, (((v1_xboole_0 @ sk_C_1) | (r2_hidden @ sk_A @ sk_C_1))),
% 0.90/1.11      inference('sup-', [status(thm)], ['63', '68'])).
% 0.90/1.11  thf('70', plain,
% 0.90/1.11      ((((k1_tarski @ sk_A) = (sk_B_1)) | (v1_xboole_0 @ sk_B_1))),
% 0.90/1.11      inference('sup+', [status(thm)], ['14', '15'])).
% 0.90/1.11  thf(t69_enumset1, axiom,
% 0.90/1.11    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.90/1.11  thf('71', plain,
% 0.90/1.11      (![X31 : $i]: ((k2_tarski @ X31 @ X31) = (k1_tarski @ X31))),
% 0.90/1.11      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.90/1.11  thf(l51_zfmisc_1, axiom,
% 0.90/1.11    (![A:$i,B:$i]:
% 0.90/1.11     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.90/1.11  thf('72', plain,
% 0.90/1.11      (![X63 : $i, X64 : $i]:
% 0.90/1.11         ((k3_tarski @ (k2_tarski @ X63 @ X64)) = (k2_xboole_0 @ X63 @ X64))),
% 0.90/1.11      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.90/1.11  thf('73', plain,
% 0.90/1.11      (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (k2_xboole_0 @ X0 @ X0))),
% 0.90/1.11      inference('sup+', [status(thm)], ['71', '72'])).
% 0.90/1.11  thf('74', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.90/1.11      inference('demod', [status(thm)], ['20', '21'])).
% 0.90/1.11  thf('75', plain,
% 0.90/1.11      (![X0 : $i, X1 : $i]:
% 0.90/1.11         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 0.90/1.11      inference('sup-', [status(thm)], ['37', '38'])).
% 0.90/1.11  thf('76', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.90/1.11      inference('sup+', [status(thm)], ['74', '75'])).
% 0.90/1.11  thf('77', plain, (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (X0))),
% 0.90/1.11      inference('demod', [status(thm)], ['73', '76'])).
% 0.90/1.11  thf('78', plain,
% 0.90/1.11      ((((k3_tarski @ sk_B_1) = (sk_A)) | (v1_xboole_0 @ sk_B_1))),
% 0.90/1.11      inference('sup+', [status(thm)], ['70', '77'])).
% 0.90/1.11  thf('79', plain,
% 0.90/1.11      ((((k1_tarski @ sk_A) = (sk_C_1)) | ~ (v1_xboole_0 @ sk_B_1))),
% 0.90/1.11      inference('sup+', [status(thm)], ['41', '42'])).
% 0.90/1.11  thf('80', plain,
% 0.90/1.11      ((((k3_tarski @ sk_B_1) = (sk_A)) | ((k1_tarski @ sk_A) = (sk_C_1)))),
% 0.90/1.11      inference('sup-', [status(thm)], ['78', '79'])).
% 0.90/1.11  thf('81', plain, (((sk_C_1) != (k1_tarski @ sk_A))),
% 0.90/1.11      inference('simpl_trail', [status(thm)], ['45', '59'])).
% 0.90/1.11  thf('82', plain, (((k3_tarski @ sk_B_1) = (sk_A))),
% 0.90/1.11      inference('simplify_reflect-', [status(thm)], ['80', '81'])).
% 0.90/1.11  thf('83', plain,
% 0.90/1.11      (((v1_xboole_0 @ sk_C_1) | (r2_hidden @ (k3_tarski @ sk_B_1) @ sk_C_1))),
% 0.90/1.11      inference('demod', [status(thm)], ['69', '82'])).
% 0.90/1.11  thf('84', plain,
% 0.90/1.11      (![X5 : $i]: (((X5) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X5))),
% 0.90/1.11      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.90/1.11  thf('85', plain,
% 0.90/1.11      ((((sk_C_1) != (k1_xboole_0))) <= (~ (((sk_C_1) = (k1_xboole_0))))),
% 0.90/1.11      inference('split', [status(esa)], ['50'])).
% 0.90/1.11  thf('86', plain,
% 0.90/1.11      ((![X0 : $i]: (((sk_C_1) != (X0)) | ~ (v1_xboole_0 @ X0)))
% 0.90/1.11         <= (~ (((sk_C_1) = (k1_xboole_0))))),
% 0.90/1.11      inference('sup-', [status(thm)], ['84', '85'])).
% 0.90/1.11  thf('87', plain,
% 0.90/1.11      ((~ (v1_xboole_0 @ sk_C_1)) <= (~ (((sk_C_1) = (k1_xboole_0))))),
% 0.90/1.11      inference('simplify', [status(thm)], ['86'])).
% 0.90/1.11  thf('88', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 0.90/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.11  thf('89', plain,
% 0.90/1.11      (((v1_xboole_0 @ sk_B_1)) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.90/1.11      inference('simplify', [status(thm)], ['52'])).
% 0.90/1.11  thf('90', plain,
% 0.90/1.11      ((((k1_tarski @ sk_A) = (sk_C_1)) | ~ (v1_xboole_0 @ sk_B_1))),
% 0.90/1.11      inference('sup+', [status(thm)], ['41', '42'])).
% 0.90/1.11  thf('91', plain,
% 0.90/1.11      ((((k1_tarski @ sk_A) = (sk_C_1)))
% 0.90/1.11         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.90/1.11      inference('sup-', [status(thm)], ['89', '90'])).
% 0.90/1.11  thf('92', plain, ((r1_tarski @ sk_B_1 @ (k1_tarski @ sk_A))),
% 0.90/1.11      inference('sup+', [status(thm)], ['2', '3'])).
% 0.90/1.11  thf('93', plain,
% 0.90/1.11      (![X18 : $i, X19 : $i]:
% 0.90/1.11         (((k2_xboole_0 @ X19 @ X18) = (X18)) | ~ (r1_tarski @ X19 @ X18))),
% 0.90/1.11      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.90/1.11  thf('94', plain,
% 0.90/1.11      (((k2_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A))),
% 0.90/1.11      inference('sup-', [status(thm)], ['92', '93'])).
% 0.90/1.11  thf('95', plain,
% 0.90/1.11      ((((k2_xboole_0 @ sk_B_1 @ sk_C_1) = (k1_tarski @ sk_A)))
% 0.90/1.11         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.90/1.11      inference('sup+', [status(thm)], ['91', '94'])).
% 0.90/1.11  thf('96', plain,
% 0.90/1.11      ((((k1_tarski @ sk_A) = (sk_C_1)))
% 0.90/1.11         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.90/1.11      inference('sup-', [status(thm)], ['89', '90'])).
% 0.90/1.11  thf('97', plain,
% 0.90/1.11      ((((k2_xboole_0 @ sk_B_1 @ sk_C_1) = (sk_C_1)))
% 0.90/1.11         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.90/1.11      inference('demod', [status(thm)], ['95', '96'])).
% 0.90/1.11  thf('98', plain,
% 0.90/1.11      ((((k1_tarski @ sk_A) = (sk_C_1)))
% 0.90/1.11         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.90/1.11      inference('sup+', [status(thm)], ['88', '97'])).
% 0.90/1.11  thf('99', plain,
% 0.90/1.11      ((((k1_tarski @ sk_A) = (sk_C_1)))
% 0.90/1.11         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.90/1.11      inference('sup-', [status(thm)], ['89', '90'])).
% 0.90/1.11  thf('100', plain, (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (X0))),
% 0.90/1.11      inference('demod', [status(thm)], ['73', '76'])).
% 0.90/1.11  thf('101', plain,
% 0.90/1.11      ((((k3_tarski @ sk_C_1) = (sk_A)))
% 0.90/1.11         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.90/1.11      inference('sup+', [status(thm)], ['99', '100'])).
% 0.90/1.11  thf('102', plain,
% 0.90/1.11      ((((k1_tarski @ (k3_tarski @ sk_C_1)) = (sk_C_1)))
% 0.90/1.11         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.90/1.11      inference('demod', [status(thm)], ['98', '101'])).
% 0.90/1.11  thf('103', plain,
% 0.90/1.11      ((((k3_tarski @ sk_C_1) = (sk_A)))
% 0.90/1.11         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.90/1.11      inference('sup+', [status(thm)], ['99', '100'])).
% 0.90/1.11  thf('104', plain, (((sk_C_1) != (k1_tarski @ sk_A))),
% 0.90/1.11      inference('simpl_trail', [status(thm)], ['45', '59'])).
% 0.90/1.11  thf('105', plain,
% 0.90/1.11      ((((sk_C_1) != (k1_tarski @ (k3_tarski @ sk_C_1))))
% 0.90/1.11         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.90/1.11      inference('sup-', [status(thm)], ['103', '104'])).
% 0.90/1.11  thf('106', plain, ((((sk_B_1) = (k1_tarski @ sk_A)))),
% 0.90/1.11      inference('simplify_reflect-', [status(thm)], ['102', '105'])).
% 0.90/1.11  thf('107', plain,
% 0.90/1.11      (~ (((sk_C_1) = (k1_xboole_0))) | ~ (((sk_B_1) = (k1_tarski @ sk_A)))),
% 0.90/1.11      inference('split', [status(esa)], ['50'])).
% 0.90/1.11  thf('108', plain, (~ (((sk_C_1) = (k1_xboole_0)))),
% 0.90/1.11      inference('sat_resolution*', [status(thm)], ['106', '107'])).
% 0.90/1.11  thf('109', plain, (~ (v1_xboole_0 @ sk_C_1)),
% 0.90/1.11      inference('simpl_trail', [status(thm)], ['87', '108'])).
% 0.90/1.11  thf('110', plain, ((r2_hidden @ (k3_tarski @ sk_B_1) @ sk_C_1)),
% 0.90/1.11      inference('clc', [status(thm)], ['83', '109'])).
% 0.90/1.11  thf('111', plain,
% 0.90/1.11      (![X61 : $i, X62 : $i]:
% 0.90/1.11         (((k3_xboole_0 @ X62 @ (k1_tarski @ X61)) = (k1_tarski @ X61))
% 0.90/1.11          | ~ (r2_hidden @ X61 @ X62))),
% 0.90/1.11      inference('cnf', [status(esa)], [l31_zfmisc_1])).
% 0.90/1.11  thf('112', plain,
% 0.90/1.11      (((k3_xboole_0 @ sk_C_1 @ (k1_tarski @ (k3_tarski @ sk_B_1)))
% 0.90/1.11         = (k1_tarski @ (k3_tarski @ sk_B_1)))),
% 0.90/1.11      inference('sup-', [status(thm)], ['110', '111'])).
% 0.90/1.11  thf('113', plain,
% 0.90/1.11      ((((k1_tarski @ sk_A) = (sk_B_1)) | (v1_xboole_0 @ sk_B_1))),
% 0.90/1.11      inference('sup+', [status(thm)], ['14', '15'])).
% 0.90/1.11  thf('114', plain, (((k3_tarski @ sk_B_1) = (sk_A))),
% 0.90/1.11      inference('simplify_reflect-', [status(thm)], ['80', '81'])).
% 0.90/1.11  thf('115', plain,
% 0.90/1.11      ((((k1_tarski @ (k3_tarski @ sk_B_1)) = (sk_B_1))
% 0.90/1.11        | (v1_xboole_0 @ sk_B_1))),
% 0.90/1.11      inference('demod', [status(thm)], ['113', '114'])).
% 0.90/1.11  thf('116', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.90/1.11      inference('simplify_reflect-', [status(thm)], ['43', '60'])).
% 0.90/1.11  thf('117', plain, (((k1_tarski @ (k3_tarski @ sk_B_1)) = (sk_B_1))),
% 0.90/1.11      inference('clc', [status(thm)], ['115', '116'])).
% 0.90/1.11  thf('118', plain,
% 0.90/1.11      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.90/1.11      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.90/1.11  thf('119', plain, (((k1_tarski @ (k3_tarski @ sk_B_1)) = (sk_B_1))),
% 0.90/1.11      inference('clc', [status(thm)], ['115', '116'])).
% 0.90/1.11  thf('120', plain, (((k3_xboole_0 @ sk_B_1 @ sk_C_1) = (sk_B_1))),
% 0.90/1.11      inference('demod', [status(thm)], ['112', '117', '118', '119'])).
% 0.90/1.11  thf('121', plain, (((sk_C_1) = (sk_B_1))),
% 0.90/1.11      inference('sup+', [status(thm)], ['62', '120'])).
% 0.90/1.11  thf('122', plain, (((sk_C_1) != (k1_tarski @ sk_A))),
% 0.90/1.11      inference('simpl_trail', [status(thm)], ['45', '59'])).
% 0.90/1.11  thf('123', plain, (((k3_tarski @ sk_B_1) = (sk_A))),
% 0.90/1.11      inference('simplify_reflect-', [status(thm)], ['80', '81'])).
% 0.90/1.11  thf('124', plain, (((sk_C_1) != (k1_tarski @ (k3_tarski @ sk_B_1)))),
% 0.90/1.11      inference('demod', [status(thm)], ['122', '123'])).
% 0.90/1.11  thf('125', plain, (((k1_tarski @ (k3_tarski @ sk_B_1)) = (sk_B_1))),
% 0.90/1.11      inference('clc', [status(thm)], ['115', '116'])).
% 0.90/1.11  thf('126', plain, (((sk_C_1) != (sk_B_1))),
% 0.90/1.11      inference('demod', [status(thm)], ['124', '125'])).
% 0.90/1.11  thf('127', plain, ($false),
% 0.90/1.11      inference('simplify_reflect-', [status(thm)], ['121', '126'])).
% 0.90/1.11  
% 0.90/1.11  % SZS output end Refutation
% 0.90/1.11  
% 0.90/1.12  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
