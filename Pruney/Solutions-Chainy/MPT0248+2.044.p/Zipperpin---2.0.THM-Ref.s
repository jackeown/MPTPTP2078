%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.qp7VNQrdv7

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:23 EST 2020

% Result     : Theorem 2.66s
% Output     : Refutation 2.66s
% Verified   : 
% Statistics : Number of formulae       :  223 (1325 expanded)
%              Number of leaves         :   39 ( 395 expanded)
%              Depth                    :   25
%              Number of atoms          : 1461 (13964 expanded)
%              Number of equality atoms :  186 (2417 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

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

thf('0',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('1',plain,(
    ! [X60: $i,X61: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X60 ) @ X61 )
      | ( r2_hidden @ X60 @ X61 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) @ X0 )
      | ( r2_hidden @ sk_A @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X30: $i,X31: $i] :
      ( r1_tarski @ X30 @ ( k2_xboole_0 @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('4',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k3_xboole_0 @ X24 @ X25 )
        = X24 )
      | ~ ( r1_tarski @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('6',plain,(
    ! [X6: $i] :
      ( ( v1_xboole_0 @ X6 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('8',plain,(
    ! [X8: $i,X10: $i] :
      ( ( r1_tarski @ X8 @ X10 )
      | ( r2_hidden @ ( sk_C @ X10 @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('9',plain,(
    ! [X8: $i,X10: $i] :
      ( ( r1_tarski @ X8 @ X10 )
      | ~ ( r2_hidden @ ( sk_C @ X10 @ X8 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['10'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('12',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k2_xboole_0 @ X23 @ X22 )
        = X22 )
      | ~ ( r1_tarski @ X23 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(t29_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ C ) ) )).

thf('14',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X26 @ X27 ) @ ( k2_xboole_0 @ X26 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t29_xboole_1])).

thf('15',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k3_xboole_0 @ X24 @ X25 )
        = X24 )
      | ~ ( r1_tarski @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X2 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['7','19'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('21',plain,(
    ! [X14: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X16 @ ( k3_xboole_0 @ X14 @ X17 ) )
      | ~ ( r1_xboole_0 @ X14 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['6','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 )
      | ( v1_xboole_0 @ ( k3_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,
    ( ( r2_hidden @ sk_A @ sk_B_1 )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['2','27'])).

thf('29',plain,(
    ! [X8: $i,X10: $i] :
      ( ( r1_tarski @ X8 @ X10 )
      | ( r2_hidden @ ( sk_C @ X10 @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('30',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ~ ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k2_xboole_0 @ X23 @ X22 )
        = X22 )
      | ~ ( r1_tarski @ X23 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( sk_B_1 != k1_xboole_0 )
    | ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( sk_C_2
     != ( k1_tarski @ sk_A ) )
   <= ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['35'])).

thf('37',plain,
    ( ( sk_C_2
     != ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) )
   <= ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['34','36'])).

thf('38',plain,
    ( ( ( sk_C_2 != sk_C_2 )
      | ~ ( v1_xboole_0 @ sk_B_1 ) )
   <= ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['33','37'])).

thf('39',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
   <= ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,
    ( ( sk_C_2
     != ( k1_tarski @ sk_A ) )
    | ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['35'])).

thf('41',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( sk_C_2
     != ( k1_tarski @ sk_A ) )
    | ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['41'])).

thf('43',plain,(
    ! [X30: $i,X31: $i] :
      ( r1_tarski @ X30 @ ( k2_xboole_0 @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('44',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('45',plain,(
    ! [X62: $i,X63: $i] :
      ( ( X63
        = ( k1_tarski @ X62 ) )
      | ( X63 = k1_xboole_0 )
      | ~ ( r1_tarski @ X63 @ ( k1_tarski @ X62 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) )
      | ( X0 = k1_xboole_0 )
      | ( X0
        = ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) )
      | ( X0 = k1_xboole_0 )
      | ( X0
        = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,
    ( ( sk_B_1
      = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['43','48'])).

thf('50',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_2 != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['51'])).

thf('53',plain,
    ( ( sk_B_1
     != ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['50','52'])).

thf('54',plain,
    ( ( ( sk_B_1 != sk_B_1 )
      | ( sk_B_1 = k1_xboole_0 ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['49','53'])).

thf('55',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,
    ( ( sk_B_1 != k1_xboole_0 )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['35'])).

thf('57',plain,
    ( ( sk_B_1 != sk_B_1 )
   <= ( ( sk_B_1 != k1_xboole_0 )
      & ( sk_B_1
       != ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_B_1
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    sk_C_2
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['40','42','58'])).

thf('60',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['39','59'])).

thf('61',plain,(
    r2_hidden @ sk_A @ sk_B_1 ),
    inference(clc,[status(thm)],['28','60'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('62',plain,(
    ! [X57: $i,X59: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X57 ) @ X59 )
      | ~ ( r2_hidden @ X57 @ X59 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('63',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    r1_tarski @ ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) @ sk_B_1 ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k3_xboole_0 @ X24 @ X25 )
        = X24 )
      | ~ ( r1_tarski @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('67',plain,
    ( ( k3_xboole_0 @ ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) @ sk_B_1 )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('70',plain,
    ( sk_B_1
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['67','68','69'])).

thf(l98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('71',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k5_xboole_0 @ X18 @ X19 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X18 @ X19 ) @ ( k3_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[l98_xboole_1])).

thf('72',plain,
    ( ( k5_xboole_0 @ sk_B_1 @ sk_C_2 )
    = ( k4_xboole_0 @ sk_B_1 @ ( k3_xboole_0 @ sk_B_1 @ sk_C_2 ) ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('74',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X26 @ X27 ) @ ( k2_xboole_0 @ X26 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t29_xboole_1])).

thf('75',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k2_xboole_0 @ X23 @ X22 )
        = X22 )
      | ~ ( r1_tarski @ X23 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('76',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X2 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['73','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('81',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k5_xboole_0 @ X18 @ X19 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X18 @ X19 ) @ ( k3_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[l98_xboole_1])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X30: $i,X31: $i] :
      ( r1_tarski @ X30 @ ( k2_xboole_0 @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('84',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k2_xboole_0 @ X23 @ X22 )
        = X22 )
      | ~ ( r1_tarski @ X23 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['82','85'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['79','86'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('88',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('89',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X20 @ X21 )
      = ( k5_xboole_0 @ X20 @ ( k3_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['87','88','89','90'])).

thf('92',plain,
    ( ( k5_xboole_0 @ sk_B_1 @ sk_C_2 )
    = ( k4_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['72','91'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('93',plain,(
    ! [X35: $i] :
      ( ( k5_xboole_0 @ X35 @ X35 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('94',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X32 @ X33 ) @ X34 )
      = ( k5_xboole_0 @ X32 @ ( k5_xboole_0 @ X33 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('97',plain,(
    ! [X29: $i] :
      ( ( k5_xboole_0 @ X29 @ k1_xboole_0 )
      = X29 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['95','98'])).

thf('100',plain,
    ( sk_C_2
    = ( k5_xboole_0 @ sk_B_1 @ ( k4_xboole_0 @ sk_B_1 @ sk_C_2 ) ) ),
    inference('sup+',[status(thm)],['92','99'])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('102',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X20 @ X21 )
      = ( k5_xboole_0 @ X20 @ ( k3_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['95','98'])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('107',plain,
    ( sk_C_2
    = ( k3_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['100','105','106'])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('109',plain,
    ( ( k2_xboole_0 @ sk_C_2 @ sk_B_1 )
    = sk_B_1 ),
    inference('sup+',[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('111',plain,
    ( ~ ( r1_xboole_0 @ sk_B_1 @ sk_C_2 )
    | ( v1_xboole_0 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['10'])).

thf('113',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k3_xboole_0 @ X24 @ X25 )
        = X24 )
      | ~ ( r1_tarski @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r1_xboole_0 @ X14 @ X15 )
      | ( r2_hidden @ ( sk_C_1 @ X15 @ X14 ) @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('116',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ~ ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('117',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['114','117'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('119',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_xboole_0 @ X11 @ X12 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('120',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k3_xboole_0 @ X0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('122',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['120','121'])).

thf('123',plain,
    ( ( sk_C_2 != k1_xboole_0 )
   <= ( sk_C_2 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['51'])).

thf('124',plain,
    ( ! [X0: $i] :
        ( ( sk_C_2 != X0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( sk_C_2 != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,
    ( ~ ( v1_xboole_0 @ sk_C_2 )
   <= ( sk_C_2 != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['124'])).

thf('126',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('127',plain,(
    ! [X6: $i] :
      ( ( v1_xboole_0 @ X6 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('128',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    ! [X63: $i,X64: $i] :
      ( ( r1_tarski @ X63 @ ( k1_tarski @ X64 ) )
      | ( X63 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('130',plain,(
    ! [X64: $i] :
      ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ X64 ) ) ),
    inference(simplify,[status(thm)],['129'])).

thf('131',plain,(
    r1_tarski @ k1_xboole_0 @ ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['128','130'])).

thf('132',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k3_xboole_0 @ X24 @ X25 )
        = X24 )
      | ~ ( r1_tarski @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('133',plain,
    ( ( k3_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,(
    ! [X14: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X16 @ ( k3_xboole_0 @ X14 @ X17 ) )
      | ~ ( r1_xboole_0 @ X14 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('135',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['133','134'])).

thf('136',plain,
    ( ( k3_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['131','132'])).

thf('137',plain,(
    ! [X11: $i,X13: $i] :
      ( ( r1_xboole_0 @ X11 @ X13 )
      | ( ( k3_xboole_0 @ X11 @ X13 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('138',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,(
    r1_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference(simplify,[status(thm)],['138'])).

thf('140',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['135','139'])).

thf('141',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['127','140'])).

thf('142',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['126','141'])).

thf('143',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['39','59'])).

thf('144',plain,
    ( sk_B_1
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,
    ( ( sk_C_2 != k1_xboole_0 )
    | ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['51'])).

thf('146',plain,(
    sk_C_2 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['144','145'])).

thf('147',plain,(
    ~ ( v1_xboole_0 @ sk_C_2 ) ),
    inference(simpl_trail,[status(thm)],['125','146'])).

thf('148',plain,(
    ~ ( r1_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference(clc,[status(thm)],['111','147'])).

thf('149',plain,
    ( sk_B_1
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('150',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) @ X0 )
      | ( r2_hidden @ sk_A @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('151',plain,
    ( sk_B_1
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('152',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_B_1 @ X0 )
      | ( r2_hidden @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['150','151'])).

thf('153',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('154',plain,(
    ! [X36: $i] :
      ( ( k2_tarski @ X36 @ X36 )
      = ( k1_tarski @ X36 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('155',plain,(
    ! [X65: $i,X66: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X65 @ X66 ) )
      = ( k2_xboole_0 @ X65 @ X66 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('156',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['154','155'])).

thf('157',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('158',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['156','157'])).

thf('159',plain,
    ( ( k3_tarski @ ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) )
    = sk_A ),
    inference('sup+',[status(thm)],['153','158'])).

thf('160',plain,
    ( sk_B_1
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('161',plain,
    ( ( k3_tarski @ sk_B_1 )
    = sk_A ),
    inference(demod,[status(thm)],['159','160'])).

thf('162',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_B_1 @ X0 )
      | ( r2_hidden @ ( k3_tarski @ sk_B_1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['152','161'])).

thf('163',plain,(
    ! [X57: $i,X59: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X57 ) @ X59 )
      | ~ ( r2_hidden @ X57 @ X59 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('164',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_B_1 @ X0 )
      | ( r1_tarski @ ( k1_tarski @ ( k3_tarski @ sk_B_1 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['162','163'])).

thf('165',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,
    ( sk_B_1
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('167',plain,
    ( ( k1_tarski @ sk_A )
    = sk_B_1 ),
    inference(demod,[status(thm)],['165','166'])).

thf('168',plain,
    ( ( k3_tarski @ sk_B_1 )
    = sk_A ),
    inference(demod,[status(thm)],['159','160'])).

thf('169',plain,
    ( ( k1_tarski @ ( k3_tarski @ sk_B_1 ) )
    = sk_B_1 ),
    inference(demod,[status(thm)],['167','168'])).

thf('170',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_B_1 @ X0 )
      | ( r1_tarski @ sk_B_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['164','169'])).

thf('171',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k2_xboole_0 @ X23 @ X22 )
        = X22 )
      | ~ ( r1_tarski @ X23 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('172',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_B_1 @ X0 )
      | ( ( k2_xboole_0 @ sk_B_1 @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['170','171'])).

thf('173',plain,
    ( ( sk_B_1 = sk_C_2 )
    | ( r1_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['149','172'])).

thf('174',plain,
    ( ( sk_C_2
     != ( k1_tarski @ sk_A ) )
   <= ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['35'])).

thf('175',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('176',plain,
    ( ( sk_C_2
     != ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) )
   <= ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['174','175'])).

thf('177',plain,(
    sk_C_2
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['40','42','58'])).

thf('178',plain,(
    sk_C_2
 != ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference(simpl_trail,[status(thm)],['176','177'])).

thf('179',plain,
    ( sk_B_1
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('180',plain,(
    sk_C_2 != sk_B_1 ),
    inference(demod,[status(thm)],['178','179'])).

thf('181',plain,(
    r1_xboole_0 @ sk_B_1 @ sk_C_2 ),
    inference('simplify_reflect-',[status(thm)],['173','180'])).

thf('182',plain,(
    $false ),
    inference(demod,[status(thm)],['148','181'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.qp7VNQrdv7
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:29:45 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 2.66/2.84  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.66/2.84  % Solved by: fo/fo7.sh
% 2.66/2.84  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.66/2.84  % done 4132 iterations in 2.395s
% 2.66/2.84  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.66/2.84  % SZS output start Refutation
% 2.66/2.84  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 2.66/2.84  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 2.66/2.84  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.66/2.84  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 2.66/2.84  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.66/2.84  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 2.66/2.84  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 2.66/2.84  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 2.66/2.84  thf(sk_B_type, type, sk_B: $i > $i).
% 2.66/2.84  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 2.66/2.84  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 2.66/2.84  thf(sk_C_2_type, type, sk_C_2: $i).
% 2.66/2.84  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 2.66/2.84  thf(sk_B_1_type, type, sk_B_1: $i).
% 2.66/2.84  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.66/2.84  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 2.66/2.84  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 2.66/2.84  thf(sk_A_type, type, sk_A: $i).
% 2.66/2.84  thf(t43_zfmisc_1, conjecture,
% 2.66/2.84    (![A:$i,B:$i,C:$i]:
% 2.66/2.84     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 2.66/2.84          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 2.66/2.84          ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 2.66/2.84          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 2.66/2.84  thf(zf_stmt_0, negated_conjecture,
% 2.66/2.84    (~( ![A:$i,B:$i,C:$i]:
% 2.66/2.84        ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 2.66/2.84             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 2.66/2.84             ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 2.66/2.84             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 2.66/2.84    inference('cnf.neg', [status(esa)], [t43_zfmisc_1])).
% 2.66/2.84  thf('0', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))),
% 2.66/2.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.66/2.84  thf(l27_zfmisc_1, axiom,
% 2.66/2.84    (![A:$i,B:$i]:
% 2.66/2.84     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 2.66/2.84  thf('1', plain,
% 2.66/2.84      (![X60 : $i, X61 : $i]:
% 2.66/2.84         ((r1_xboole_0 @ (k1_tarski @ X60) @ X61) | (r2_hidden @ X60 @ X61))),
% 2.66/2.84      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 2.66/2.84  thf('2', plain,
% 2.66/2.84      (![X0 : $i]:
% 2.66/2.84         ((r1_xboole_0 @ (k2_xboole_0 @ sk_B_1 @ sk_C_2) @ X0)
% 2.66/2.84          | (r2_hidden @ sk_A @ X0))),
% 2.66/2.84      inference('sup+', [status(thm)], ['0', '1'])).
% 2.66/2.84  thf(t7_xboole_1, axiom,
% 2.66/2.84    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 2.66/2.84  thf('3', plain,
% 2.66/2.84      (![X30 : $i, X31 : $i]: (r1_tarski @ X30 @ (k2_xboole_0 @ X30 @ X31))),
% 2.66/2.84      inference('cnf', [status(esa)], [t7_xboole_1])).
% 2.66/2.84  thf(t28_xboole_1, axiom,
% 2.66/2.84    (![A:$i,B:$i]:
% 2.66/2.84     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 2.66/2.84  thf('4', plain,
% 2.66/2.84      (![X24 : $i, X25 : $i]:
% 2.66/2.84         (((k3_xboole_0 @ X24 @ X25) = (X24)) | ~ (r1_tarski @ X24 @ X25))),
% 2.66/2.84      inference('cnf', [status(esa)], [t28_xboole_1])).
% 2.66/2.84  thf('5', plain,
% 2.66/2.84      (![X0 : $i, X1 : $i]:
% 2.66/2.84         ((k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)) = (X1))),
% 2.66/2.84      inference('sup-', [status(thm)], ['3', '4'])).
% 2.66/2.84  thf(d1_xboole_0, axiom,
% 2.66/2.84    (![A:$i]:
% 2.66/2.84     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 2.66/2.84  thf('6', plain,
% 2.66/2.84      (![X6 : $i]: ((v1_xboole_0 @ X6) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 2.66/2.84      inference('cnf', [status(esa)], [d1_xboole_0])).
% 2.66/2.84  thf(commutativity_k3_xboole_0, axiom,
% 2.66/2.84    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 2.66/2.84  thf('7', plain,
% 2.66/2.84      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.66/2.84      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.66/2.84  thf(d3_tarski, axiom,
% 2.66/2.84    (![A:$i,B:$i]:
% 2.66/2.84     ( ( r1_tarski @ A @ B ) <=>
% 2.66/2.84       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 2.66/2.84  thf('8', plain,
% 2.66/2.84      (![X8 : $i, X10 : $i]:
% 2.66/2.84         ((r1_tarski @ X8 @ X10) | (r2_hidden @ (sk_C @ X10 @ X8) @ X8))),
% 2.66/2.84      inference('cnf', [status(esa)], [d3_tarski])).
% 2.66/2.84  thf('9', plain,
% 2.66/2.84      (![X8 : $i, X10 : $i]:
% 2.66/2.84         ((r1_tarski @ X8 @ X10) | ~ (r2_hidden @ (sk_C @ X10 @ X8) @ X10))),
% 2.66/2.84      inference('cnf', [status(esa)], [d3_tarski])).
% 2.66/2.84  thf('10', plain,
% 2.66/2.84      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 2.66/2.84      inference('sup-', [status(thm)], ['8', '9'])).
% 2.66/2.84  thf('11', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 2.66/2.84      inference('simplify', [status(thm)], ['10'])).
% 2.66/2.84  thf(t12_xboole_1, axiom,
% 2.66/2.84    (![A:$i,B:$i]:
% 2.66/2.84     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 2.66/2.84  thf('12', plain,
% 2.66/2.84      (![X22 : $i, X23 : $i]:
% 2.66/2.84         (((k2_xboole_0 @ X23 @ X22) = (X22)) | ~ (r1_tarski @ X23 @ X22))),
% 2.66/2.84      inference('cnf', [status(esa)], [t12_xboole_1])).
% 2.66/2.84  thf('13', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 2.66/2.84      inference('sup-', [status(thm)], ['11', '12'])).
% 2.66/2.84  thf(t29_xboole_1, axiom,
% 2.66/2.84    (![A:$i,B:$i,C:$i]:
% 2.66/2.84     ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ C ) ))).
% 2.66/2.84  thf('14', plain,
% 2.66/2.84      (![X26 : $i, X27 : $i, X28 : $i]:
% 2.66/2.84         (r1_tarski @ (k3_xboole_0 @ X26 @ X27) @ (k2_xboole_0 @ X26 @ X28))),
% 2.66/2.84      inference('cnf', [status(esa)], [t29_xboole_1])).
% 2.66/2.84  thf('15', plain,
% 2.66/2.84      (![X24 : $i, X25 : $i]:
% 2.66/2.84         (((k3_xboole_0 @ X24 @ X25) = (X24)) | ~ (r1_tarski @ X24 @ X25))),
% 2.66/2.84      inference('cnf', [status(esa)], [t28_xboole_1])).
% 2.66/2.84  thf('16', plain,
% 2.66/2.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.66/2.84         ((k3_xboole_0 @ (k3_xboole_0 @ X1 @ X2) @ (k2_xboole_0 @ X1 @ X0))
% 2.66/2.84           = (k3_xboole_0 @ X1 @ X2))),
% 2.66/2.84      inference('sup-', [status(thm)], ['14', '15'])).
% 2.66/2.84  thf('17', plain,
% 2.66/2.84      (![X0 : $i, X1 : $i]:
% 2.66/2.84         ((k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0)
% 2.66/2.84           = (k3_xboole_0 @ X0 @ X1))),
% 2.66/2.84      inference('sup+', [status(thm)], ['13', '16'])).
% 2.66/2.84  thf('18', plain,
% 2.66/2.84      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.66/2.84      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.66/2.84  thf('19', plain,
% 2.66/2.84      (![X0 : $i, X1 : $i]:
% 2.66/2.84         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 2.66/2.84           = (k3_xboole_0 @ X0 @ X1))),
% 2.66/2.84      inference('demod', [status(thm)], ['17', '18'])).
% 2.66/2.84  thf('20', plain,
% 2.66/2.84      (![X0 : $i, X1 : $i]:
% 2.66/2.84         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 2.66/2.84           = (k3_xboole_0 @ X0 @ X1))),
% 2.66/2.84      inference('sup+', [status(thm)], ['7', '19'])).
% 2.66/2.84  thf(t4_xboole_0, axiom,
% 2.66/2.84    (![A:$i,B:$i]:
% 2.66/2.84     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 2.66/2.84            ( r1_xboole_0 @ A @ B ) ) ) & 
% 2.66/2.84       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 2.66/2.84            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 2.66/2.84  thf('21', plain,
% 2.66/2.84      (![X14 : $i, X16 : $i, X17 : $i]:
% 2.66/2.84         (~ (r2_hidden @ X16 @ (k3_xboole_0 @ X14 @ X17))
% 2.66/2.84          | ~ (r1_xboole_0 @ X14 @ X17))),
% 2.66/2.84      inference('cnf', [status(esa)], [t4_xboole_0])).
% 2.66/2.84  thf('22', plain,
% 2.66/2.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.66/2.84         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 2.66/2.84          | ~ (r1_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X1)))),
% 2.66/2.84      inference('sup-', [status(thm)], ['20', '21'])).
% 2.66/2.84  thf('23', plain,
% 2.66/2.84      (![X0 : $i, X1 : $i]:
% 2.66/2.84         ((v1_xboole_0 @ (k3_xboole_0 @ X1 @ X0))
% 2.66/2.84          | ~ (r1_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X1)))),
% 2.66/2.84      inference('sup-', [status(thm)], ['6', '22'])).
% 2.66/2.85  thf('24', plain,
% 2.66/2.85      (![X0 : $i, X1 : $i]:
% 2.66/2.85         (~ (r1_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0)
% 2.66/2.85          | (v1_xboole_0 @ (k3_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0)))),
% 2.66/2.85      inference('sup-', [status(thm)], ['5', '23'])).
% 2.66/2.85  thf('25', plain,
% 2.66/2.85      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.66/2.85      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.66/2.85  thf('26', plain,
% 2.66/2.85      (![X0 : $i, X1 : $i]:
% 2.66/2.85         ((k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)) = (X1))),
% 2.66/2.85      inference('sup-', [status(thm)], ['3', '4'])).
% 2.66/2.85  thf('27', plain,
% 2.66/2.85      (![X0 : $i, X1 : $i]:
% 2.66/2.85         (~ (r1_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0) | (v1_xboole_0 @ X0))),
% 2.66/2.85      inference('demod', [status(thm)], ['24', '25', '26'])).
% 2.66/2.85  thf('28', plain, (((r2_hidden @ sk_A @ sk_B_1) | (v1_xboole_0 @ sk_B_1))),
% 2.66/2.85      inference('sup-', [status(thm)], ['2', '27'])).
% 2.66/2.85  thf('29', plain,
% 2.66/2.85      (![X8 : $i, X10 : $i]:
% 2.66/2.85         ((r1_tarski @ X8 @ X10) | (r2_hidden @ (sk_C @ X10 @ X8) @ X8))),
% 2.66/2.85      inference('cnf', [status(esa)], [d3_tarski])).
% 2.66/2.85  thf('30', plain,
% 2.66/2.85      (![X4 : $i, X5 : $i]: (~ (r2_hidden @ X4 @ X5) | ~ (v1_xboole_0 @ X5))),
% 2.66/2.85      inference('cnf', [status(esa)], [d1_xboole_0])).
% 2.66/2.85  thf('31', plain,
% 2.66/2.85      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 2.66/2.85      inference('sup-', [status(thm)], ['29', '30'])).
% 2.66/2.85  thf('32', plain,
% 2.66/2.85      (![X22 : $i, X23 : $i]:
% 2.66/2.85         (((k2_xboole_0 @ X23 @ X22) = (X22)) | ~ (r1_tarski @ X23 @ X22))),
% 2.66/2.85      inference('cnf', [status(esa)], [t12_xboole_1])).
% 2.66/2.85  thf('33', plain,
% 2.66/2.85      (![X0 : $i, X1 : $i]:
% 2.66/2.85         (~ (v1_xboole_0 @ X1) | ((k2_xboole_0 @ X1 @ X0) = (X0)))),
% 2.66/2.85      inference('sup-', [status(thm)], ['31', '32'])).
% 2.66/2.85  thf('34', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))),
% 2.66/2.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.66/2.85  thf('35', plain,
% 2.66/2.85      ((((sk_B_1) != (k1_xboole_0)) | ((sk_C_2) != (k1_tarski @ sk_A)))),
% 2.66/2.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.66/2.85  thf('36', plain,
% 2.66/2.85      ((((sk_C_2) != (k1_tarski @ sk_A)))
% 2.66/2.85         <= (~ (((sk_C_2) = (k1_tarski @ sk_A))))),
% 2.66/2.85      inference('split', [status(esa)], ['35'])).
% 2.66/2.85  thf('37', plain,
% 2.66/2.85      ((((sk_C_2) != (k2_xboole_0 @ sk_B_1 @ sk_C_2)))
% 2.66/2.85         <= (~ (((sk_C_2) = (k1_tarski @ sk_A))))),
% 2.66/2.85      inference('sup-', [status(thm)], ['34', '36'])).
% 2.66/2.85  thf('38', plain,
% 2.66/2.85      (((((sk_C_2) != (sk_C_2)) | ~ (v1_xboole_0 @ sk_B_1)))
% 2.66/2.85         <= (~ (((sk_C_2) = (k1_tarski @ sk_A))))),
% 2.66/2.85      inference('sup-', [status(thm)], ['33', '37'])).
% 2.66/2.85  thf('39', plain,
% 2.66/2.85      ((~ (v1_xboole_0 @ sk_B_1)) <= (~ (((sk_C_2) = (k1_tarski @ sk_A))))),
% 2.66/2.85      inference('simplify', [status(thm)], ['38'])).
% 2.66/2.85  thf('40', plain,
% 2.66/2.85      (~ (((sk_C_2) = (k1_tarski @ sk_A))) | ~ (((sk_B_1) = (k1_xboole_0)))),
% 2.66/2.85      inference('split', [status(esa)], ['35'])).
% 2.66/2.85  thf('41', plain,
% 2.66/2.85      ((((sk_B_1) != (k1_tarski @ sk_A)) | ((sk_C_2) != (k1_tarski @ sk_A)))),
% 2.66/2.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.66/2.85  thf('42', plain,
% 2.66/2.85      (~ (((sk_C_2) = (k1_tarski @ sk_A))) | 
% 2.66/2.85       ~ (((sk_B_1) = (k1_tarski @ sk_A)))),
% 2.66/2.85      inference('split', [status(esa)], ['41'])).
% 2.66/2.85  thf('43', plain,
% 2.66/2.85      (![X30 : $i, X31 : $i]: (r1_tarski @ X30 @ (k2_xboole_0 @ X30 @ X31))),
% 2.66/2.85      inference('cnf', [status(esa)], [t7_xboole_1])).
% 2.66/2.85  thf('44', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))),
% 2.66/2.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.66/2.85  thf(l3_zfmisc_1, axiom,
% 2.66/2.85    (![A:$i,B:$i]:
% 2.66/2.85     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 2.66/2.85       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 2.66/2.85  thf('45', plain,
% 2.66/2.85      (![X62 : $i, X63 : $i]:
% 2.66/2.85         (((X63) = (k1_tarski @ X62))
% 2.66/2.85          | ((X63) = (k1_xboole_0))
% 2.66/2.85          | ~ (r1_tarski @ X63 @ (k1_tarski @ X62)))),
% 2.66/2.85      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 2.66/2.85  thf('46', plain,
% 2.66/2.85      (![X0 : $i]:
% 2.66/2.85         (~ (r1_tarski @ X0 @ (k2_xboole_0 @ sk_B_1 @ sk_C_2))
% 2.66/2.85          | ((X0) = (k1_xboole_0))
% 2.66/2.85          | ((X0) = (k1_tarski @ sk_A)))),
% 2.66/2.85      inference('sup-', [status(thm)], ['44', '45'])).
% 2.66/2.85  thf('47', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))),
% 2.66/2.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.66/2.85  thf('48', plain,
% 2.66/2.85      (![X0 : $i]:
% 2.66/2.85         (~ (r1_tarski @ X0 @ (k2_xboole_0 @ sk_B_1 @ sk_C_2))
% 2.66/2.85          | ((X0) = (k1_xboole_0))
% 2.66/2.85          | ((X0) = (k2_xboole_0 @ sk_B_1 @ sk_C_2)))),
% 2.66/2.85      inference('demod', [status(thm)], ['46', '47'])).
% 2.66/2.85  thf('49', plain,
% 2.66/2.85      ((((sk_B_1) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))
% 2.66/2.85        | ((sk_B_1) = (k1_xboole_0)))),
% 2.66/2.85      inference('sup-', [status(thm)], ['43', '48'])).
% 2.66/2.85  thf('50', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))),
% 2.66/2.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.66/2.85  thf('51', plain,
% 2.66/2.85      ((((sk_B_1) != (k1_tarski @ sk_A)) | ((sk_C_2) != (k1_xboole_0)))),
% 2.66/2.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.66/2.85  thf('52', plain,
% 2.66/2.85      ((((sk_B_1) != (k1_tarski @ sk_A)))
% 2.66/2.85         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 2.66/2.85      inference('split', [status(esa)], ['51'])).
% 2.66/2.85  thf('53', plain,
% 2.66/2.85      ((((sk_B_1) != (k2_xboole_0 @ sk_B_1 @ sk_C_2)))
% 2.66/2.85         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 2.66/2.85      inference('sup-', [status(thm)], ['50', '52'])).
% 2.66/2.85  thf('54', plain,
% 2.66/2.85      (((((sk_B_1) != (sk_B_1)) | ((sk_B_1) = (k1_xboole_0))))
% 2.66/2.85         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 2.66/2.85      inference('sup-', [status(thm)], ['49', '53'])).
% 2.66/2.85  thf('55', plain,
% 2.66/2.85      ((((sk_B_1) = (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 2.66/2.85      inference('simplify', [status(thm)], ['54'])).
% 2.66/2.85  thf('56', plain,
% 2.66/2.85      ((((sk_B_1) != (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 2.66/2.85      inference('split', [status(esa)], ['35'])).
% 2.66/2.85  thf('57', plain,
% 2.66/2.85      ((((sk_B_1) != (sk_B_1)))
% 2.66/2.85         <= (~ (((sk_B_1) = (k1_xboole_0))) & 
% 2.66/2.85             ~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 2.66/2.85      inference('sup-', [status(thm)], ['55', '56'])).
% 2.66/2.85  thf('58', plain,
% 2.66/2.85      ((((sk_B_1) = (k1_xboole_0))) | (((sk_B_1) = (k1_tarski @ sk_A)))),
% 2.66/2.85      inference('simplify', [status(thm)], ['57'])).
% 2.66/2.85  thf('59', plain, (~ (((sk_C_2) = (k1_tarski @ sk_A)))),
% 2.66/2.85      inference('sat_resolution*', [status(thm)], ['40', '42', '58'])).
% 2.66/2.85  thf('60', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 2.66/2.85      inference('simpl_trail', [status(thm)], ['39', '59'])).
% 2.66/2.85  thf('61', plain, ((r2_hidden @ sk_A @ sk_B_1)),
% 2.66/2.85      inference('clc', [status(thm)], ['28', '60'])).
% 2.66/2.85  thf(l1_zfmisc_1, axiom,
% 2.66/2.85    (![A:$i,B:$i]:
% 2.66/2.85     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 2.66/2.85  thf('62', plain,
% 2.66/2.85      (![X57 : $i, X59 : $i]:
% 2.66/2.85         ((r1_tarski @ (k1_tarski @ X57) @ X59) | ~ (r2_hidden @ X57 @ X59))),
% 2.66/2.85      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 2.66/2.85  thf('63', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ sk_B_1)),
% 2.66/2.85      inference('sup-', [status(thm)], ['61', '62'])).
% 2.66/2.85  thf('64', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))),
% 2.66/2.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.66/2.85  thf('65', plain, ((r1_tarski @ (k2_xboole_0 @ sk_B_1 @ sk_C_2) @ sk_B_1)),
% 2.66/2.85      inference('demod', [status(thm)], ['63', '64'])).
% 2.66/2.85  thf('66', plain,
% 2.66/2.85      (![X24 : $i, X25 : $i]:
% 2.66/2.85         (((k3_xboole_0 @ X24 @ X25) = (X24)) | ~ (r1_tarski @ X24 @ X25))),
% 2.66/2.85      inference('cnf', [status(esa)], [t28_xboole_1])).
% 2.66/2.85  thf('67', plain,
% 2.66/2.85      (((k3_xboole_0 @ (k2_xboole_0 @ sk_B_1 @ sk_C_2) @ sk_B_1)
% 2.66/2.85         = (k2_xboole_0 @ sk_B_1 @ sk_C_2))),
% 2.66/2.85      inference('sup-', [status(thm)], ['65', '66'])).
% 2.66/2.85  thf('68', plain,
% 2.66/2.85      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.66/2.85      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.66/2.85  thf('69', plain,
% 2.66/2.85      (![X0 : $i, X1 : $i]:
% 2.66/2.85         ((k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)) = (X1))),
% 2.66/2.85      inference('sup-', [status(thm)], ['3', '4'])).
% 2.66/2.85  thf('70', plain, (((sk_B_1) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))),
% 2.66/2.85      inference('demod', [status(thm)], ['67', '68', '69'])).
% 2.66/2.85  thf(l98_xboole_1, axiom,
% 2.66/2.85    (![A:$i,B:$i]:
% 2.66/2.85     ( ( k5_xboole_0 @ A @ B ) =
% 2.66/2.85       ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 2.66/2.85  thf('71', plain,
% 2.66/2.85      (![X18 : $i, X19 : $i]:
% 2.66/2.85         ((k5_xboole_0 @ X18 @ X19)
% 2.66/2.85           = (k4_xboole_0 @ (k2_xboole_0 @ X18 @ X19) @ 
% 2.66/2.85              (k3_xboole_0 @ X18 @ X19)))),
% 2.66/2.85      inference('cnf', [status(esa)], [l98_xboole_1])).
% 2.66/2.85  thf('72', plain,
% 2.66/2.85      (((k5_xboole_0 @ sk_B_1 @ sk_C_2)
% 2.66/2.85         = (k4_xboole_0 @ sk_B_1 @ (k3_xboole_0 @ sk_B_1 @ sk_C_2)))),
% 2.66/2.85      inference('sup+', [status(thm)], ['70', '71'])).
% 2.66/2.85  thf('73', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 2.66/2.85      inference('sup-', [status(thm)], ['11', '12'])).
% 2.66/2.85  thf('74', plain,
% 2.66/2.85      (![X26 : $i, X27 : $i, X28 : $i]:
% 2.66/2.85         (r1_tarski @ (k3_xboole_0 @ X26 @ X27) @ (k2_xboole_0 @ X26 @ X28))),
% 2.66/2.85      inference('cnf', [status(esa)], [t29_xboole_1])).
% 2.66/2.85  thf('75', plain,
% 2.66/2.85      (![X22 : $i, X23 : $i]:
% 2.66/2.85         (((k2_xboole_0 @ X23 @ X22) = (X22)) | ~ (r1_tarski @ X23 @ X22))),
% 2.66/2.85      inference('cnf', [status(esa)], [t12_xboole_1])).
% 2.66/2.85  thf('76', plain,
% 2.66/2.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.66/2.85         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X2) @ (k2_xboole_0 @ X1 @ X0))
% 2.66/2.85           = (k2_xboole_0 @ X1 @ X0))),
% 2.66/2.85      inference('sup-', [status(thm)], ['74', '75'])).
% 2.66/2.85  thf('77', plain,
% 2.66/2.85      (![X0 : $i, X1 : $i]:
% 2.66/2.85         ((k2_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0)
% 2.66/2.85           = (k2_xboole_0 @ X0 @ X0))),
% 2.66/2.85      inference('sup+', [status(thm)], ['73', '76'])).
% 2.66/2.85  thf('78', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 2.66/2.85      inference('sup-', [status(thm)], ['11', '12'])).
% 2.66/2.85  thf('79', plain,
% 2.66/2.85      (![X0 : $i, X1 : $i]:
% 2.66/2.85         ((k2_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 2.66/2.85      inference('demod', [status(thm)], ['77', '78'])).
% 2.66/2.85  thf('80', plain,
% 2.66/2.85      (![X0 : $i, X1 : $i]:
% 2.66/2.85         ((k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)) = (X1))),
% 2.66/2.85      inference('sup-', [status(thm)], ['3', '4'])).
% 2.66/2.85  thf('81', plain,
% 2.66/2.85      (![X18 : $i, X19 : $i]:
% 2.66/2.85         ((k5_xboole_0 @ X18 @ X19)
% 2.66/2.85           = (k4_xboole_0 @ (k2_xboole_0 @ X18 @ X19) @ 
% 2.66/2.85              (k3_xboole_0 @ X18 @ X19)))),
% 2.66/2.85      inference('cnf', [status(esa)], [l98_xboole_1])).
% 2.66/2.85  thf('82', plain,
% 2.66/2.85      (![X0 : $i, X1 : $i]:
% 2.66/2.85         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))
% 2.66/2.85           = (k4_xboole_0 @ (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)) @ X0))),
% 2.66/2.85      inference('sup+', [status(thm)], ['80', '81'])).
% 2.66/2.85  thf('83', plain,
% 2.66/2.85      (![X30 : $i, X31 : $i]: (r1_tarski @ X30 @ (k2_xboole_0 @ X30 @ X31))),
% 2.66/2.85      inference('cnf', [status(esa)], [t7_xboole_1])).
% 2.66/2.85  thf('84', plain,
% 2.66/2.85      (![X22 : $i, X23 : $i]:
% 2.66/2.85         (((k2_xboole_0 @ X23 @ X22) = (X22)) | ~ (r1_tarski @ X23 @ X22))),
% 2.66/2.85      inference('cnf', [status(esa)], [t12_xboole_1])).
% 2.66/2.85  thf('85', plain,
% 2.66/2.85      (![X0 : $i, X1 : $i]:
% 2.66/2.85         ((k2_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))
% 2.66/2.85           = (k2_xboole_0 @ X1 @ X0))),
% 2.66/2.85      inference('sup-', [status(thm)], ['83', '84'])).
% 2.66/2.85  thf('86', plain,
% 2.66/2.85      (![X0 : $i, X1 : $i]:
% 2.66/2.85         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))
% 2.66/2.85           = (k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0))),
% 2.66/2.85      inference('demod', [status(thm)], ['82', '85'])).
% 2.66/2.85  thf('87', plain,
% 2.66/2.85      (![X0 : $i, X1 : $i]:
% 2.66/2.85         ((k5_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0)
% 2.66/2.85           = (k4_xboole_0 @ (k2_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) @ 
% 2.66/2.85              (k3_xboole_0 @ X0 @ X1)))),
% 2.66/2.85      inference('sup+', [status(thm)], ['79', '86'])).
% 2.66/2.85  thf(commutativity_k5_xboole_0, axiom,
% 2.66/2.85    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 2.66/2.85  thf('88', plain,
% 2.66/2.85      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 2.66/2.85      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 2.66/2.85  thf(t100_xboole_1, axiom,
% 2.66/2.85    (![A:$i,B:$i]:
% 2.66/2.85     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 2.66/2.85  thf('89', plain,
% 2.66/2.85      (![X20 : $i, X21 : $i]:
% 2.66/2.85         ((k4_xboole_0 @ X20 @ X21)
% 2.66/2.85           = (k5_xboole_0 @ X20 @ (k3_xboole_0 @ X20 @ X21)))),
% 2.66/2.85      inference('cnf', [status(esa)], [t100_xboole_1])).
% 2.66/2.85  thf('90', plain,
% 2.66/2.85      (![X0 : $i, X1 : $i]:
% 2.66/2.85         ((k2_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 2.66/2.85      inference('demod', [status(thm)], ['77', '78'])).
% 2.66/2.85  thf('91', plain,
% 2.66/2.85      (![X0 : $i, X1 : $i]:
% 2.66/2.85         ((k4_xboole_0 @ X0 @ X1)
% 2.66/2.85           = (k4_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 2.66/2.85      inference('demod', [status(thm)], ['87', '88', '89', '90'])).
% 2.66/2.85  thf('92', plain,
% 2.66/2.85      (((k5_xboole_0 @ sk_B_1 @ sk_C_2) = (k4_xboole_0 @ sk_B_1 @ sk_C_2))),
% 2.66/2.85      inference('demod', [status(thm)], ['72', '91'])).
% 2.66/2.85  thf(t92_xboole_1, axiom,
% 2.66/2.85    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 2.66/2.85  thf('93', plain, (![X35 : $i]: ((k5_xboole_0 @ X35 @ X35) = (k1_xboole_0))),
% 2.66/2.85      inference('cnf', [status(esa)], [t92_xboole_1])).
% 2.66/2.85  thf(t91_xboole_1, axiom,
% 2.66/2.85    (![A:$i,B:$i,C:$i]:
% 2.66/2.85     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 2.66/2.85       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 2.66/2.85  thf('94', plain,
% 2.66/2.85      (![X32 : $i, X33 : $i, X34 : $i]:
% 2.66/2.85         ((k5_xboole_0 @ (k5_xboole_0 @ X32 @ X33) @ X34)
% 2.66/2.85           = (k5_xboole_0 @ X32 @ (k5_xboole_0 @ X33 @ X34)))),
% 2.66/2.85      inference('cnf', [status(esa)], [t91_xboole_1])).
% 2.66/2.85  thf('95', plain,
% 2.66/2.85      (![X0 : $i, X1 : $i]:
% 2.66/2.85         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 2.66/2.85           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 2.66/2.85      inference('sup+', [status(thm)], ['93', '94'])).
% 2.66/2.85  thf('96', plain,
% 2.66/2.85      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 2.66/2.85      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 2.66/2.85  thf(t5_boole, axiom,
% 2.66/2.85    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 2.66/2.85  thf('97', plain, (![X29 : $i]: ((k5_xboole_0 @ X29 @ k1_xboole_0) = (X29))),
% 2.66/2.85      inference('cnf', [status(esa)], [t5_boole])).
% 2.66/2.85  thf('98', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 2.66/2.85      inference('sup+', [status(thm)], ['96', '97'])).
% 2.66/2.85  thf('99', plain,
% 2.66/2.85      (![X0 : $i, X1 : $i]:
% 2.66/2.85         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 2.66/2.85      inference('demod', [status(thm)], ['95', '98'])).
% 2.66/2.85  thf('100', plain,
% 2.66/2.85      (((sk_C_2) = (k5_xboole_0 @ sk_B_1 @ (k4_xboole_0 @ sk_B_1 @ sk_C_2)))),
% 2.66/2.85      inference('sup+', [status(thm)], ['92', '99'])).
% 2.66/2.85  thf('101', plain,
% 2.66/2.85      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.66/2.85      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.66/2.85  thf('102', plain,
% 2.66/2.85      (![X20 : $i, X21 : $i]:
% 2.66/2.85         ((k4_xboole_0 @ X20 @ X21)
% 2.66/2.85           = (k5_xboole_0 @ X20 @ (k3_xboole_0 @ X20 @ X21)))),
% 2.66/2.85      inference('cnf', [status(esa)], [t100_xboole_1])).
% 2.66/2.85  thf('103', plain,
% 2.66/2.85      (![X0 : $i, X1 : $i]:
% 2.66/2.85         ((k4_xboole_0 @ X0 @ X1)
% 2.66/2.85           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 2.66/2.85      inference('sup+', [status(thm)], ['101', '102'])).
% 2.66/2.85  thf('104', plain,
% 2.66/2.85      (![X0 : $i, X1 : $i]:
% 2.66/2.85         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 2.66/2.85      inference('demod', [status(thm)], ['95', '98'])).
% 2.66/2.85  thf('105', plain,
% 2.66/2.85      (![X0 : $i, X1 : $i]:
% 2.66/2.85         ((k3_xboole_0 @ X0 @ X1)
% 2.66/2.85           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 2.66/2.85      inference('sup+', [status(thm)], ['103', '104'])).
% 2.66/2.85  thf('106', plain,
% 2.66/2.85      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.66/2.85      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.66/2.85  thf('107', plain, (((sk_C_2) = (k3_xboole_0 @ sk_B_1 @ sk_C_2))),
% 2.66/2.85      inference('demod', [status(thm)], ['100', '105', '106'])).
% 2.66/2.85  thf('108', plain,
% 2.66/2.85      (![X0 : $i, X1 : $i]:
% 2.66/2.85         ((k2_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 2.66/2.85      inference('demod', [status(thm)], ['77', '78'])).
% 2.66/2.85  thf('109', plain, (((k2_xboole_0 @ sk_C_2 @ sk_B_1) = (sk_B_1))),
% 2.66/2.85      inference('sup+', [status(thm)], ['107', '108'])).
% 2.66/2.85  thf('110', plain,
% 2.66/2.85      (![X0 : $i, X1 : $i]:
% 2.66/2.85         (~ (r1_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0) | (v1_xboole_0 @ X0))),
% 2.66/2.85      inference('demod', [status(thm)], ['24', '25', '26'])).
% 2.66/2.85  thf('111', plain,
% 2.66/2.85      ((~ (r1_xboole_0 @ sk_B_1 @ sk_C_2) | (v1_xboole_0 @ sk_C_2))),
% 2.66/2.85      inference('sup-', [status(thm)], ['109', '110'])).
% 2.66/2.85  thf('112', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 2.66/2.85      inference('simplify', [status(thm)], ['10'])).
% 2.66/2.85  thf('113', plain,
% 2.66/2.85      (![X24 : $i, X25 : $i]:
% 2.66/2.85         (((k3_xboole_0 @ X24 @ X25) = (X24)) | ~ (r1_tarski @ X24 @ X25))),
% 2.66/2.85      inference('cnf', [status(esa)], [t28_xboole_1])).
% 2.66/2.85  thf('114', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 2.66/2.85      inference('sup-', [status(thm)], ['112', '113'])).
% 2.66/2.85  thf('115', plain,
% 2.66/2.85      (![X14 : $i, X15 : $i]:
% 2.66/2.85         ((r1_xboole_0 @ X14 @ X15)
% 2.66/2.85          | (r2_hidden @ (sk_C_1 @ X15 @ X14) @ (k3_xboole_0 @ X14 @ X15)))),
% 2.66/2.85      inference('cnf', [status(esa)], [t4_xboole_0])).
% 2.66/2.85  thf('116', plain,
% 2.66/2.85      (![X4 : $i, X5 : $i]: (~ (r2_hidden @ X4 @ X5) | ~ (v1_xboole_0 @ X5))),
% 2.66/2.85      inference('cnf', [status(esa)], [d1_xboole_0])).
% 2.66/2.85  thf('117', plain,
% 2.66/2.85      (![X0 : $i, X1 : $i]:
% 2.66/2.85         ((r1_xboole_0 @ X1 @ X0) | ~ (v1_xboole_0 @ (k3_xboole_0 @ X1 @ X0)))),
% 2.66/2.85      inference('sup-', [status(thm)], ['115', '116'])).
% 2.66/2.85  thf('118', plain,
% 2.66/2.85      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (r1_xboole_0 @ X0 @ X0))),
% 2.66/2.85      inference('sup-', [status(thm)], ['114', '117'])).
% 2.66/2.85  thf(d7_xboole_0, axiom,
% 2.66/2.85    (![A:$i,B:$i]:
% 2.66/2.85     ( ( r1_xboole_0 @ A @ B ) <=>
% 2.66/2.85       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 2.66/2.85  thf('119', plain,
% 2.66/2.85      (![X11 : $i, X12 : $i]:
% 2.66/2.85         (((k3_xboole_0 @ X11 @ X12) = (k1_xboole_0))
% 2.66/2.85          | ~ (r1_xboole_0 @ X11 @ X12))),
% 2.66/2.85      inference('cnf', [status(esa)], [d7_xboole_0])).
% 2.66/2.85  thf('120', plain,
% 2.66/2.85      (![X0 : $i]:
% 2.66/2.85         (~ (v1_xboole_0 @ X0) | ((k3_xboole_0 @ X0 @ X0) = (k1_xboole_0)))),
% 2.66/2.85      inference('sup-', [status(thm)], ['118', '119'])).
% 2.66/2.85  thf('121', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 2.66/2.85      inference('sup-', [status(thm)], ['112', '113'])).
% 2.66/2.85  thf('122', plain,
% 2.66/2.85      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 2.66/2.85      inference('sup+', [status(thm)], ['120', '121'])).
% 2.66/2.85  thf('123', plain,
% 2.66/2.85      ((((sk_C_2) != (k1_xboole_0))) <= (~ (((sk_C_2) = (k1_xboole_0))))),
% 2.66/2.85      inference('split', [status(esa)], ['51'])).
% 2.66/2.85  thf('124', plain,
% 2.66/2.85      ((![X0 : $i]: (((sk_C_2) != (X0)) | ~ (v1_xboole_0 @ X0)))
% 2.66/2.85         <= (~ (((sk_C_2) = (k1_xboole_0))))),
% 2.66/2.85      inference('sup-', [status(thm)], ['122', '123'])).
% 2.66/2.85  thf('125', plain,
% 2.66/2.85      ((~ (v1_xboole_0 @ sk_C_2)) <= (~ (((sk_C_2) = (k1_xboole_0))))),
% 2.66/2.85      inference('simplify', [status(thm)], ['124'])).
% 2.66/2.85  thf('126', plain,
% 2.66/2.85      ((((sk_B_1) = (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 2.66/2.85      inference('simplify', [status(thm)], ['54'])).
% 2.66/2.85  thf('127', plain,
% 2.66/2.85      (![X6 : $i]: ((v1_xboole_0 @ X6) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 2.66/2.85      inference('cnf', [status(esa)], [d1_xboole_0])).
% 2.66/2.85  thf('128', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))),
% 2.66/2.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.66/2.85  thf('129', plain,
% 2.66/2.85      (![X63 : $i, X64 : $i]:
% 2.66/2.85         ((r1_tarski @ X63 @ (k1_tarski @ X64)) | ((X63) != (k1_xboole_0)))),
% 2.66/2.85      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 2.66/2.85  thf('130', plain,
% 2.66/2.85      (![X64 : $i]: (r1_tarski @ k1_xboole_0 @ (k1_tarski @ X64))),
% 2.66/2.85      inference('simplify', [status(thm)], ['129'])).
% 2.66/2.85  thf('131', plain,
% 2.66/2.85      ((r1_tarski @ k1_xboole_0 @ (k2_xboole_0 @ sk_B_1 @ sk_C_2))),
% 2.66/2.85      inference('sup+', [status(thm)], ['128', '130'])).
% 2.66/2.85  thf('132', plain,
% 2.66/2.85      (![X24 : $i, X25 : $i]:
% 2.66/2.85         (((k3_xboole_0 @ X24 @ X25) = (X24)) | ~ (r1_tarski @ X24 @ X25))),
% 2.66/2.85      inference('cnf', [status(esa)], [t28_xboole_1])).
% 2.66/2.85  thf('133', plain,
% 2.66/2.85      (((k3_xboole_0 @ k1_xboole_0 @ (k2_xboole_0 @ sk_B_1 @ sk_C_2))
% 2.66/2.85         = (k1_xboole_0))),
% 2.66/2.85      inference('sup-', [status(thm)], ['131', '132'])).
% 2.66/2.85  thf('134', plain,
% 2.66/2.85      (![X14 : $i, X16 : $i, X17 : $i]:
% 2.66/2.85         (~ (r2_hidden @ X16 @ (k3_xboole_0 @ X14 @ X17))
% 2.66/2.85          | ~ (r1_xboole_0 @ X14 @ X17))),
% 2.66/2.85      inference('cnf', [status(esa)], [t4_xboole_0])).
% 2.66/2.85  thf('135', plain,
% 2.66/2.85      (![X0 : $i]:
% 2.66/2.85         (~ (r2_hidden @ X0 @ k1_xboole_0)
% 2.66/2.85          | ~ (r1_xboole_0 @ k1_xboole_0 @ (k2_xboole_0 @ sk_B_1 @ sk_C_2)))),
% 2.66/2.85      inference('sup-', [status(thm)], ['133', '134'])).
% 2.66/2.85  thf('136', plain,
% 2.66/2.85      (((k3_xboole_0 @ k1_xboole_0 @ (k2_xboole_0 @ sk_B_1 @ sk_C_2))
% 2.66/2.85         = (k1_xboole_0))),
% 2.66/2.85      inference('sup-', [status(thm)], ['131', '132'])).
% 2.66/2.85  thf('137', plain,
% 2.66/2.85      (![X11 : $i, X13 : $i]:
% 2.66/2.85         ((r1_xboole_0 @ X11 @ X13)
% 2.66/2.85          | ((k3_xboole_0 @ X11 @ X13) != (k1_xboole_0)))),
% 2.66/2.85      inference('cnf', [status(esa)], [d7_xboole_0])).
% 2.66/2.85  thf('138', plain,
% 2.66/2.85      ((((k1_xboole_0) != (k1_xboole_0))
% 2.66/2.85        | (r1_xboole_0 @ k1_xboole_0 @ (k2_xboole_0 @ sk_B_1 @ sk_C_2)))),
% 2.66/2.85      inference('sup-', [status(thm)], ['136', '137'])).
% 2.66/2.85  thf('139', plain,
% 2.66/2.85      ((r1_xboole_0 @ k1_xboole_0 @ (k2_xboole_0 @ sk_B_1 @ sk_C_2))),
% 2.66/2.85      inference('simplify', [status(thm)], ['138'])).
% 2.66/2.85  thf('140', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 2.66/2.85      inference('demod', [status(thm)], ['135', '139'])).
% 2.66/2.85  thf('141', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.66/2.85      inference('sup-', [status(thm)], ['127', '140'])).
% 2.66/2.85  thf('142', plain,
% 2.66/2.85      (((v1_xboole_0 @ sk_B_1)) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 2.66/2.85      inference('sup+', [status(thm)], ['126', '141'])).
% 2.66/2.85  thf('143', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 2.66/2.85      inference('simpl_trail', [status(thm)], ['39', '59'])).
% 2.66/2.85  thf('144', plain, ((((sk_B_1) = (k1_tarski @ sk_A)))),
% 2.66/2.85      inference('sup-', [status(thm)], ['142', '143'])).
% 2.66/2.85  thf('145', plain,
% 2.66/2.85      (~ (((sk_C_2) = (k1_xboole_0))) | ~ (((sk_B_1) = (k1_tarski @ sk_A)))),
% 2.66/2.85      inference('split', [status(esa)], ['51'])).
% 2.66/2.85  thf('146', plain, (~ (((sk_C_2) = (k1_xboole_0)))),
% 2.66/2.85      inference('sat_resolution*', [status(thm)], ['144', '145'])).
% 2.66/2.85  thf('147', plain, (~ (v1_xboole_0 @ sk_C_2)),
% 2.66/2.85      inference('simpl_trail', [status(thm)], ['125', '146'])).
% 2.66/2.85  thf('148', plain, (~ (r1_xboole_0 @ sk_B_1 @ sk_C_2)),
% 2.66/2.85      inference('clc', [status(thm)], ['111', '147'])).
% 2.66/2.85  thf('149', plain, (((sk_B_1) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))),
% 2.66/2.85      inference('demod', [status(thm)], ['67', '68', '69'])).
% 2.66/2.85  thf('150', plain,
% 2.66/2.85      (![X0 : $i]:
% 2.66/2.85         ((r1_xboole_0 @ (k2_xboole_0 @ sk_B_1 @ sk_C_2) @ X0)
% 2.66/2.85          | (r2_hidden @ sk_A @ X0))),
% 2.66/2.85      inference('sup+', [status(thm)], ['0', '1'])).
% 2.66/2.85  thf('151', plain, (((sk_B_1) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))),
% 2.66/2.85      inference('demod', [status(thm)], ['67', '68', '69'])).
% 2.66/2.85  thf('152', plain,
% 2.66/2.85      (![X0 : $i]: ((r1_xboole_0 @ sk_B_1 @ X0) | (r2_hidden @ sk_A @ X0))),
% 2.66/2.85      inference('demod', [status(thm)], ['150', '151'])).
% 2.66/2.85  thf('153', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))),
% 2.66/2.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.66/2.85  thf(t69_enumset1, axiom,
% 2.66/2.85    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 2.66/2.85  thf('154', plain,
% 2.66/2.85      (![X36 : $i]: ((k2_tarski @ X36 @ X36) = (k1_tarski @ X36))),
% 2.66/2.85      inference('cnf', [status(esa)], [t69_enumset1])).
% 2.66/2.85  thf(l51_zfmisc_1, axiom,
% 2.66/2.85    (![A:$i,B:$i]:
% 2.66/2.85     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 2.66/2.85  thf('155', plain,
% 2.66/2.85      (![X65 : $i, X66 : $i]:
% 2.66/2.85         ((k3_tarski @ (k2_tarski @ X65 @ X66)) = (k2_xboole_0 @ X65 @ X66))),
% 2.66/2.85      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 2.66/2.85  thf('156', plain,
% 2.66/2.85      (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (k2_xboole_0 @ X0 @ X0))),
% 2.66/2.85      inference('sup+', [status(thm)], ['154', '155'])).
% 2.66/2.85  thf('157', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 2.66/2.85      inference('sup-', [status(thm)], ['11', '12'])).
% 2.66/2.85  thf('158', plain, (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (X0))),
% 2.66/2.85      inference('demod', [status(thm)], ['156', '157'])).
% 2.66/2.85  thf('159', plain, (((k3_tarski @ (k2_xboole_0 @ sk_B_1 @ sk_C_2)) = (sk_A))),
% 2.66/2.85      inference('sup+', [status(thm)], ['153', '158'])).
% 2.66/2.85  thf('160', plain, (((sk_B_1) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))),
% 2.66/2.85      inference('demod', [status(thm)], ['67', '68', '69'])).
% 2.66/2.85  thf('161', plain, (((k3_tarski @ sk_B_1) = (sk_A))),
% 2.66/2.85      inference('demod', [status(thm)], ['159', '160'])).
% 2.66/2.85  thf('162', plain,
% 2.66/2.85      (![X0 : $i]:
% 2.66/2.85         ((r1_xboole_0 @ sk_B_1 @ X0) | (r2_hidden @ (k3_tarski @ sk_B_1) @ X0))),
% 2.66/2.85      inference('demod', [status(thm)], ['152', '161'])).
% 2.66/2.85  thf('163', plain,
% 2.66/2.85      (![X57 : $i, X59 : $i]:
% 2.66/2.85         ((r1_tarski @ (k1_tarski @ X57) @ X59) | ~ (r2_hidden @ X57 @ X59))),
% 2.66/2.85      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 2.66/2.85  thf('164', plain,
% 2.66/2.85      (![X0 : $i]:
% 2.66/2.85         ((r1_xboole_0 @ sk_B_1 @ X0)
% 2.66/2.85          | (r1_tarski @ (k1_tarski @ (k3_tarski @ sk_B_1)) @ X0))),
% 2.66/2.85      inference('sup-', [status(thm)], ['162', '163'])).
% 2.66/2.85  thf('165', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))),
% 2.66/2.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.66/2.85  thf('166', plain, (((sk_B_1) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))),
% 2.66/2.85      inference('demod', [status(thm)], ['67', '68', '69'])).
% 2.66/2.85  thf('167', plain, (((k1_tarski @ sk_A) = (sk_B_1))),
% 2.66/2.85      inference('demod', [status(thm)], ['165', '166'])).
% 2.66/2.85  thf('168', plain, (((k3_tarski @ sk_B_1) = (sk_A))),
% 2.66/2.85      inference('demod', [status(thm)], ['159', '160'])).
% 2.66/2.85  thf('169', plain, (((k1_tarski @ (k3_tarski @ sk_B_1)) = (sk_B_1))),
% 2.66/2.85      inference('demod', [status(thm)], ['167', '168'])).
% 2.66/2.85  thf('170', plain,
% 2.66/2.85      (![X0 : $i]: ((r1_xboole_0 @ sk_B_1 @ X0) | (r1_tarski @ sk_B_1 @ X0))),
% 2.66/2.85      inference('demod', [status(thm)], ['164', '169'])).
% 2.66/2.85  thf('171', plain,
% 2.66/2.85      (![X22 : $i, X23 : $i]:
% 2.66/2.85         (((k2_xboole_0 @ X23 @ X22) = (X22)) | ~ (r1_tarski @ X23 @ X22))),
% 2.66/2.85      inference('cnf', [status(esa)], [t12_xboole_1])).
% 2.66/2.85  thf('172', plain,
% 2.66/2.85      (![X0 : $i]:
% 2.66/2.85         ((r1_xboole_0 @ sk_B_1 @ X0) | ((k2_xboole_0 @ sk_B_1 @ X0) = (X0)))),
% 2.66/2.85      inference('sup-', [status(thm)], ['170', '171'])).
% 2.66/2.85  thf('173', plain,
% 2.66/2.85      ((((sk_B_1) = (sk_C_2)) | (r1_xboole_0 @ sk_B_1 @ sk_C_2))),
% 2.66/2.85      inference('sup+', [status(thm)], ['149', '172'])).
% 2.66/2.85  thf('174', plain,
% 2.66/2.85      ((((sk_C_2) != (k1_tarski @ sk_A)))
% 2.66/2.85         <= (~ (((sk_C_2) = (k1_tarski @ sk_A))))),
% 2.66/2.85      inference('split', [status(esa)], ['35'])).
% 2.66/2.85  thf('175', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))),
% 2.66/2.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.66/2.85  thf('176', plain,
% 2.66/2.85      ((((sk_C_2) != (k2_xboole_0 @ sk_B_1 @ sk_C_2)))
% 2.66/2.85         <= (~ (((sk_C_2) = (k1_tarski @ sk_A))))),
% 2.66/2.85      inference('demod', [status(thm)], ['174', '175'])).
% 2.66/2.85  thf('177', plain, (~ (((sk_C_2) = (k1_tarski @ sk_A)))),
% 2.66/2.85      inference('sat_resolution*', [status(thm)], ['40', '42', '58'])).
% 2.66/2.85  thf('178', plain, (((sk_C_2) != (k2_xboole_0 @ sk_B_1 @ sk_C_2))),
% 2.66/2.85      inference('simpl_trail', [status(thm)], ['176', '177'])).
% 2.66/2.85  thf('179', plain, (((sk_B_1) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))),
% 2.66/2.85      inference('demod', [status(thm)], ['67', '68', '69'])).
% 2.66/2.85  thf('180', plain, (((sk_C_2) != (sk_B_1))),
% 2.66/2.85      inference('demod', [status(thm)], ['178', '179'])).
% 2.66/2.85  thf('181', plain, ((r1_xboole_0 @ sk_B_1 @ sk_C_2)),
% 2.66/2.85      inference('simplify_reflect-', [status(thm)], ['173', '180'])).
% 2.66/2.85  thf('182', plain, ($false), inference('demod', [status(thm)], ['148', '181'])).
% 2.66/2.85  
% 2.66/2.85  % SZS output end Refutation
% 2.66/2.85  
% 2.66/2.85  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
