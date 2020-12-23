%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.zxq8mxcDXt

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:53 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  192 ( 455 expanded)
%              Number of leaves         :   37 ( 162 expanded)
%              Depth                    :   22
%              Number of atoms          : 1340 (3502 expanded)
%              Number of equality atoms :  132 ( 345 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(t25_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) )
        = ( k2_subset_1 @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) )
          = ( k2_subset_1 @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t25_subset_1])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('1',plain,(
    ! [X62: $i,X63: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X62 @ X63 ) @ ( k1_zfmisc_1 @ X62 ) )
      | ~ ( m1_subset_1 @ X63 @ ( k1_zfmisc_1 @ X62 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('2',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X60: $i,X61: $i] :
      ( ( ( k3_subset_1 @ X60 @ X61 )
        = ( k4_xboole_0 @ X60 @ X61 ) )
      | ~ ( m1_subset_1 @ X61 @ ( k1_zfmisc_1 @ X60 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('5',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(demod,[status(thm)],['2','5'])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('7',plain,(
    ! [X56: $i,X57: $i] :
      ( ~ ( m1_subset_1 @ X56 @ X57 )
      | ( r2_hidden @ X56 @ X57 )
      | ( v1_xboole_0 @ X57 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('8',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ ( k4_xboole_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('9',plain,(
    ! [X64: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X64 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('10',plain,(
    r2_hidden @ ( k4_xboole_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['8','9'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('11',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ~ ( r2_hidden @ X52 @ X51 )
      | ( r1_tarski @ X52 @ X50 )
      | ( X51
       != ( k1_zfmisc_1 @ X50 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('12',plain,(
    ! [X50: $i,X52: $i] :
      ( ( r1_tarski @ X52 @ X50 )
      | ~ ( r2_hidden @ X52 @ ( k1_zfmisc_1 @ X50 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_A ),
    inference('sup-',[status(thm)],['10','12'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('14',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_xboole_0 @ X11 @ X12 )
        = X11 )
      | ~ ( r1_tarski @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('15',plain,
    ( ( k3_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_A )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('17',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['15','16'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('18',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf(t112_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ B ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ A @ C ) @ B ) ) )).

thf('19',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X6 @ X8 ) @ ( k3_xboole_0 @ X7 @ X8 ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X6 @ X7 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t112_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,
    ( ( k4_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = ( k3_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['17','23'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('25',plain,(
    ! [X13: $i] :
      ( r1_tarski @ k1_xboole_0 @ X13 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('26',plain,(
    ! [X49: $i,X50: $i,X51: $i] :
      ( ~ ( r1_tarski @ X49 @ X50 )
      | ( r2_hidden @ X49 @ X51 )
      | ( X51
       != ( k1_zfmisc_1 @ X50 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('27',plain,(
    ! [X49: $i,X50: $i] :
      ( ( r2_hidden @ X49 @ ( k1_zfmisc_1 @ X50 ) )
      | ~ ( r1_tarski @ X49 @ X50 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( r2_hidden @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','27'])).

thf('29',plain,(
    ! [X56: $i,X57: $i] :
      ( ~ ( r2_hidden @ X56 @ X57 )
      | ( m1_subset_1 @ X56 @ X57 )
      | ( v1_xboole_0 @ X57 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X64: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X64 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X62: $i,X63: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X62 @ X63 ) @ ( k1_zfmisc_1 @ X62 ) )
      | ~ ( m1_subset_1 @ X63 @ ( k1_zfmisc_1 @ X62 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['30','31'])).

thf('36',plain,(
    ! [X60: $i,X61: $i] :
      ( ( ( k3_subset_1 @ X60 @ X61 )
        = ( k4_xboole_0 @ X60 @ X61 ) )
      | ~ ( m1_subset_1 @ X61 @ ( k1_zfmisc_1 @ X60 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X13: $i] :
      ( r1_tarski @ k1_xboole_0 @ X13 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('39',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_xboole_0 @ X11 @ X12 )
        = X11 )
      | ~ ( r1_tarski @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('45',plain,(
    ! [X16: $i] :
      ( ( k5_xboole_0 @ X16 @ k1_xboole_0 )
      = X16 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['37','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['34','47'])).

thf('49',plain,(
    ! [X56: $i,X57: $i] :
      ( ~ ( m1_subset_1 @ X56 @ X57 )
      | ( r2_hidden @ X56 @ X57 )
      | ( v1_xboole_0 @ X57 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X64: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X64 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X50: $i,X52: $i] :
      ( ( r1_tarski @ X52 @ X50 )
      | ~ ( r2_hidden @ X52 @ ( k1_zfmisc_1 @ X50 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('54',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_xboole_0 @ X11 @ X12 )
        = X11 )
      | ~ ( r1_tarski @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('58',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['56','59'])).

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = A ) )).

thf('61',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k3_xboole_0 @ X9 @ ( k2_xboole_0 @ X9 @ X10 ) )
      = X9 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('62',plain,(
    ! [X54: $i,X55: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X54 @ X55 ) )
      = ( k2_xboole_0 @ X54 @ X55 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('63',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k3_xboole_0 @ X9 @ ( k3_tarski @ ( k2_tarski @ X9 @ X10 ) ) )
      = X9 ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_tarski @ ( k2_tarski @ X0 @ X1 ) ) )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('66',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k2_xboole_0 @ X14 @ X15 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('67',plain,(
    ! [X54: $i,X55: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X54 @ X55 ) )
      = ( k2_xboole_0 @ X54 @ X55 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('68',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k3_tarski @ ( k2_tarski @ X14 @ X15 ) ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['65','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['60','69'])).

thf('71',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ! [X56: $i,X57: $i] :
      ( ~ ( m1_subset_1 @ X56 @ X57 )
      | ( r2_hidden @ X56 @ X57 )
      | ( v1_xboole_0 @ X57 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('73',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X64: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X64 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('75',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X50: $i,X52: $i] :
      ( ( r1_tarski @ X52 @ X50 )
      | ~ ( r2_hidden @ X52 @ ( k1_zfmisc_1 @ X50 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('77',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_xboole_0 @ X11 @ X12 )
        = X11 )
      | ~ ( r1_tarski @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('79',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('81',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('82',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('83',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['65','68'])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('86',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X17 @ X18 ) @ X19 )
      = ( k5_xboole_0 @ X17 @ ( k5_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('89',plain,(
    ! [X16: $i] :
      ( ( k5_xboole_0 @ X16 @ k1_xboole_0 )
      = X16 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['87','90'])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['84','91'])).

thf('93',plain,
    ( sk_B
    = ( k5_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['83','92'])).

thf('94',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['77','78'])).

thf('95',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('96',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_A )
    = ( k5_xboole_0 @ sk_B @ sk_B ) ),
    inference('sup+',[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['65','68'])).

thf('98',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['96','97'])).

thf(t94_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('99',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_xboole_0 @ X20 @ X21 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X20 @ X21 ) @ ( k3_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t94_xboole_1])).

thf('100',plain,(
    ! [X54: $i,X55: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X54 @ X55 ) )
      = ( k2_xboole_0 @ X54 @ X55 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('101',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X17 @ X18 ) @ X19 )
      = ( k5_xboole_0 @ X17 @ ( k5_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('103',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X20 @ X21 ) )
      = ( k5_xboole_0 @ X20 @ ( k4_xboole_0 @ X21 @ X20 ) ) ) ),
    inference(demod,[status(thm)],['99','100','101','102'])).

thf('104',plain,
    ( ( k3_tarski @ ( k2_tarski @ sk_A @ sk_B ) )
    = ( k5_xboole_0 @ sk_A @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['98','103'])).

thf('105',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['88','89'])).

thf('107',plain,
    ( ( k3_tarski @ ( k2_tarski @ sk_A @ sk_B ) )
    = sk_A ),
    inference(demod,[status(thm)],['104','105','106'])).

thf('108',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k3_xboole_0 @ X9 @ ( k3_tarski @ ( k2_tarski @ X9 @ X10 ) ) )
      = X9 ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('109',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_A )
    = sk_A ),
    inference('sup+',[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X6 @ X8 ) @ ( k3_xboole_0 @ X7 @ X8 ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X6 @ X7 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t112_xboole_1])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ sk_A @ ( k3_xboole_0 @ X0 @ sk_A ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ sk_A @ X0 ) @ sk_A ) ) ),
    inference('sup+',[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ X0 )
      = ( k3_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['111','112','113'])).

thf('115',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['93','114'])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('117',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['77','78'])).

thf('118',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['115','116','117'])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('120',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['24','70','118','119'])).

thf('121',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('122',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['84','91'])).

thf('123',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['121','122'])).

thf('124',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('125',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['123','124'])).

thf('126',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ ( k4_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_B ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['120','125'])).

thf('127',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('128',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['88','89'])).

thf('129',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['126','127','128'])).

thf('130',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X20 @ X21 ) )
      = ( k5_xboole_0 @ X20 @ ( k4_xboole_0 @ X21 @ X20 ) ) ) ),
    inference(demod,[status(thm)],['99','100','101','102'])).

thf('131',plain,
    ( ( k3_tarski @ ( k2_tarski @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) ) )
    = ( k5_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['129','130'])).

thf('132',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X20 @ X21 ) )
      = ( k5_xboole_0 @ X20 @ ( k4_xboole_0 @ X21 @ X20 ) ) ) ),
    inference(demod,[status(thm)],['99','100','101','102'])).

thf('133',plain,
    ( ( k3_tarski @ ( k2_tarski @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) ) )
    = ( k3_tarski @ ( k2_tarski @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['131','132'])).

thf('134',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('135',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['87','90'])).

thf('136',plain,
    ( sk_A
    = ( k5_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['134','135'])).

thf('137',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X20 @ X21 ) )
      = ( k5_xboole_0 @ X20 @ ( k4_xboole_0 @ X21 @ X20 ) ) ) ),
    inference(demod,[status(thm)],['99','100','101','102'])).

thf('138',plain,
    ( sk_A
    = ( k3_tarski @ ( k2_tarski @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['136','137'])).

thf('139',plain,
    ( ( k3_tarski @ ( k2_tarski @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) ) )
    = sk_A ),
    inference(demod,[status(thm)],['133','138'])).

thf('140',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
 != ( k2_subset_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('141',plain,(
    ! [X59: $i] :
      ( ( k2_subset_1 @ X59 )
      = X59 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('142',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
 != sk_A ),
    inference(demod,[status(thm)],['140','141'])).

thf('143',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('144',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) )
 != sk_A ),
    inference(demod,[status(thm)],['142','143'])).

thf('145',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(demod,[status(thm)],['2','5'])).

thf('146',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('147',plain,(
    ! [X65: $i,X66: $i,X67: $i] :
      ( ~ ( m1_subset_1 @ X65 @ ( k1_zfmisc_1 @ X66 ) )
      | ~ ( m1_subset_1 @ X67 @ ( k1_zfmisc_1 @ X66 ) )
      | ( ( k4_subset_1 @ X66 @ X65 @ X67 )
        = ( k2_xboole_0 @ X65 @ X67 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('148',plain,(
    ! [X54: $i,X55: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X54 @ X55 ) )
      = ( k2_xboole_0 @ X54 @ X55 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('149',plain,(
    ! [X65: $i,X66: $i,X67: $i] :
      ( ~ ( m1_subset_1 @ X65 @ ( k1_zfmisc_1 @ X66 ) )
      | ~ ( m1_subset_1 @ X67 @ ( k1_zfmisc_1 @ X66 ) )
      | ( ( k4_subset_1 @ X66 @ X65 @ X67 )
        = ( k3_tarski @ ( k2_tarski @ X65 @ X67 ) ) ) ) ),
    inference(demod,[status(thm)],['147','148'])).

thf('150',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ sk_A @ sk_B @ X0 )
        = ( k3_tarski @ ( k2_tarski @ sk_B @ X0 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['146','149'])).

thf('151',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = ( k3_tarski @ ( k2_tarski @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['145','150'])).

thf('152',plain,(
    ( k3_tarski @ ( k2_tarski @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) ) )
 != sk_A ),
    inference(demod,[status(thm)],['144','151'])).

thf('153',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['139','152'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.zxq8mxcDXt
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:41:59 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.46/0.65  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.46/0.65  % Solved by: fo/fo7.sh
% 0.46/0.65  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.65  % done 371 iterations in 0.196s
% 0.46/0.65  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.46/0.65  % SZS output start Refutation
% 0.46/0.65  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.46/0.65  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.46/0.65  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.46/0.65  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.65  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.46/0.65  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.65  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.46/0.65  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.46/0.65  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.46/0.65  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.46/0.65  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.46/0.65  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.46/0.65  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.46/0.65  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.65  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.46/0.65  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.46/0.65  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.46/0.65  thf(t25_subset_1, conjecture,
% 0.46/0.65    (![A:$i,B:$i]:
% 0.46/0.65     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.46/0.65       ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) ) =
% 0.46/0.65         ( k2_subset_1 @ A ) ) ))).
% 0.46/0.65  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.65    (~( ![A:$i,B:$i]:
% 0.46/0.65        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.46/0.65          ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) ) =
% 0.46/0.65            ( k2_subset_1 @ A ) ) ) )),
% 0.46/0.65    inference('cnf.neg', [status(esa)], [t25_subset_1])).
% 0.46/0.65  thf('0', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf(dt_k3_subset_1, axiom,
% 0.46/0.65    (![A:$i,B:$i]:
% 0.46/0.65     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.46/0.65       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.46/0.65  thf('1', plain,
% 0.46/0.65      (![X62 : $i, X63 : $i]:
% 0.46/0.65         ((m1_subset_1 @ (k3_subset_1 @ X62 @ X63) @ (k1_zfmisc_1 @ X62))
% 0.46/0.65          | ~ (m1_subset_1 @ X63 @ (k1_zfmisc_1 @ X62)))),
% 0.46/0.65      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.46/0.65  thf('2', plain,
% 0.46/0.65      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.46/0.65      inference('sup-', [status(thm)], ['0', '1'])).
% 0.46/0.65  thf('3', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf(d5_subset_1, axiom,
% 0.46/0.65    (![A:$i,B:$i]:
% 0.46/0.65     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.46/0.65       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.46/0.65  thf('4', plain,
% 0.46/0.65      (![X60 : $i, X61 : $i]:
% 0.46/0.65         (((k3_subset_1 @ X60 @ X61) = (k4_xboole_0 @ X60 @ X61))
% 0.46/0.65          | ~ (m1_subset_1 @ X61 @ (k1_zfmisc_1 @ X60)))),
% 0.46/0.65      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.46/0.65  thf('5', plain,
% 0.46/0.65      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.46/0.65      inference('sup-', [status(thm)], ['3', '4'])).
% 0.46/0.65  thf('6', plain,
% 0.46/0.65      ((m1_subset_1 @ (k4_xboole_0 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.46/0.65      inference('demod', [status(thm)], ['2', '5'])).
% 0.46/0.65  thf(d2_subset_1, axiom,
% 0.46/0.65    (![A:$i,B:$i]:
% 0.46/0.65     ( ( ( v1_xboole_0 @ A ) =>
% 0.46/0.65         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.46/0.65       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.46/0.65         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.46/0.65  thf('7', plain,
% 0.46/0.65      (![X56 : $i, X57 : $i]:
% 0.46/0.65         (~ (m1_subset_1 @ X56 @ X57)
% 0.46/0.65          | (r2_hidden @ X56 @ X57)
% 0.46/0.65          | (v1_xboole_0 @ X57))),
% 0.46/0.65      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.46/0.65  thf('8', plain,
% 0.46/0.65      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.46/0.65        | (r2_hidden @ (k4_xboole_0 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['6', '7'])).
% 0.46/0.65  thf(fc1_subset_1, axiom,
% 0.46/0.65    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.46/0.65  thf('9', plain, (![X64 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X64))),
% 0.46/0.65      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.46/0.65  thf('10', plain,
% 0.46/0.65      ((r2_hidden @ (k4_xboole_0 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.46/0.65      inference('clc', [status(thm)], ['8', '9'])).
% 0.46/0.65  thf(d1_zfmisc_1, axiom,
% 0.46/0.65    (![A:$i,B:$i]:
% 0.46/0.65     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.46/0.65       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.46/0.65  thf('11', plain,
% 0.46/0.65      (![X50 : $i, X51 : $i, X52 : $i]:
% 0.46/0.65         (~ (r2_hidden @ X52 @ X51)
% 0.46/0.65          | (r1_tarski @ X52 @ X50)
% 0.46/0.65          | ((X51) != (k1_zfmisc_1 @ X50)))),
% 0.46/0.65      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.46/0.65  thf('12', plain,
% 0.46/0.65      (![X50 : $i, X52 : $i]:
% 0.46/0.65         ((r1_tarski @ X52 @ X50) | ~ (r2_hidden @ X52 @ (k1_zfmisc_1 @ X50)))),
% 0.46/0.65      inference('simplify', [status(thm)], ['11'])).
% 0.46/0.65  thf('13', plain, ((r1_tarski @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_A)),
% 0.46/0.65      inference('sup-', [status(thm)], ['10', '12'])).
% 0.46/0.65  thf(t28_xboole_1, axiom,
% 0.46/0.65    (![A:$i,B:$i]:
% 0.46/0.65     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.46/0.65  thf('14', plain,
% 0.46/0.65      (![X11 : $i, X12 : $i]:
% 0.46/0.65         (((k3_xboole_0 @ X11 @ X12) = (X11)) | ~ (r1_tarski @ X11 @ X12))),
% 0.46/0.65      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.46/0.65  thf('15', plain,
% 0.46/0.65      (((k3_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_A)
% 0.46/0.65         = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.46/0.65      inference('sup-', [status(thm)], ['13', '14'])).
% 0.46/0.65  thf(commutativity_k3_xboole_0, axiom,
% 0.46/0.65    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.46/0.65  thf('16', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.46/0.65      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.46/0.65  thf('17', plain,
% 0.46/0.65      (((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B))
% 0.46/0.65         = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.46/0.65      inference('demod', [status(thm)], ['15', '16'])).
% 0.46/0.65  thf(t100_xboole_1, axiom,
% 0.46/0.65    (![A:$i,B:$i]:
% 0.46/0.65     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.46/0.65  thf('18', plain,
% 0.46/0.65      (![X4 : $i, X5 : $i]:
% 0.46/0.65         ((k4_xboole_0 @ X4 @ X5)
% 0.46/0.65           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 0.46/0.65      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.46/0.65  thf(t112_xboole_1, axiom,
% 0.46/0.65    (![A:$i,B:$i,C:$i]:
% 0.46/0.65     ( ( k5_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ B ) ) =
% 0.46/0.65       ( k3_xboole_0 @ ( k5_xboole_0 @ A @ C ) @ B ) ))).
% 0.46/0.65  thf('19', plain,
% 0.46/0.65      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.46/0.65         ((k5_xboole_0 @ (k3_xboole_0 @ X6 @ X8) @ (k3_xboole_0 @ X7 @ X8))
% 0.46/0.65           = (k3_xboole_0 @ (k5_xboole_0 @ X6 @ X7) @ X8))),
% 0.46/0.65      inference('cnf', [status(esa)], [t112_xboole_1])).
% 0.46/0.65  thf('20', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]:
% 0.46/0.65         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0)
% 0.46/0.65           = (k3_xboole_0 @ (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)) @ X0))),
% 0.46/0.65      inference('sup+', [status(thm)], ['18', '19'])).
% 0.46/0.65  thf('21', plain,
% 0.46/0.65      (![X4 : $i, X5 : $i]:
% 0.46/0.65         ((k4_xboole_0 @ X4 @ X5)
% 0.46/0.65           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 0.46/0.65      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.46/0.65  thf('22', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.46/0.65      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.46/0.65  thf('23', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]:
% 0.46/0.65         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0)
% 0.46/0.65           = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.46/0.65      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.46/0.65  thf('24', plain,
% 0.46/0.65      (((k4_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ 
% 0.46/0.65         (k4_xboole_0 @ sk_A @ sk_B))
% 0.46/0.65         = (k3_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ 
% 0.46/0.65            (k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B))))),
% 0.46/0.65      inference('sup+', [status(thm)], ['17', '23'])).
% 0.46/0.65  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.46/0.65  thf('25', plain, (![X13 : $i]: (r1_tarski @ k1_xboole_0 @ X13)),
% 0.46/0.65      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.46/0.65  thf('26', plain,
% 0.46/0.65      (![X49 : $i, X50 : $i, X51 : $i]:
% 0.46/0.65         (~ (r1_tarski @ X49 @ X50)
% 0.46/0.65          | (r2_hidden @ X49 @ X51)
% 0.46/0.65          | ((X51) != (k1_zfmisc_1 @ X50)))),
% 0.46/0.65      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.46/0.65  thf('27', plain,
% 0.46/0.65      (![X49 : $i, X50 : $i]:
% 0.46/0.65         ((r2_hidden @ X49 @ (k1_zfmisc_1 @ X50)) | ~ (r1_tarski @ X49 @ X50))),
% 0.46/0.65      inference('simplify', [status(thm)], ['26'])).
% 0.46/0.65  thf('28', plain,
% 0.46/0.65      (![X0 : $i]: (r2_hidden @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.46/0.65      inference('sup-', [status(thm)], ['25', '27'])).
% 0.46/0.65  thf('29', plain,
% 0.46/0.65      (![X56 : $i, X57 : $i]:
% 0.46/0.65         (~ (r2_hidden @ X56 @ X57)
% 0.46/0.65          | (m1_subset_1 @ X56 @ X57)
% 0.46/0.65          | (v1_xboole_0 @ X57))),
% 0.46/0.65      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.46/0.65  thf('30', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 0.46/0.65          | (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['28', '29'])).
% 0.46/0.65  thf('31', plain, (![X64 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X64))),
% 0.46/0.65      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.46/0.65  thf('32', plain,
% 0.46/0.65      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.46/0.65      inference('clc', [status(thm)], ['30', '31'])).
% 0.46/0.65  thf('33', plain,
% 0.46/0.65      (![X62 : $i, X63 : $i]:
% 0.46/0.65         ((m1_subset_1 @ (k3_subset_1 @ X62 @ X63) @ (k1_zfmisc_1 @ X62))
% 0.46/0.65          | ~ (m1_subset_1 @ X63 @ (k1_zfmisc_1 @ X62)))),
% 0.46/0.65      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.46/0.65  thf('34', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (m1_subset_1 @ (k3_subset_1 @ X0 @ k1_xboole_0) @ (k1_zfmisc_1 @ X0))),
% 0.46/0.65      inference('sup-', [status(thm)], ['32', '33'])).
% 0.46/0.65  thf('35', plain,
% 0.46/0.65      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.46/0.65      inference('clc', [status(thm)], ['30', '31'])).
% 0.46/0.65  thf('36', plain,
% 0.46/0.65      (![X60 : $i, X61 : $i]:
% 0.46/0.65         (((k3_subset_1 @ X60 @ X61) = (k4_xboole_0 @ X60 @ X61))
% 0.46/0.65          | ~ (m1_subset_1 @ X61 @ (k1_zfmisc_1 @ X60)))),
% 0.46/0.65      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.46/0.65  thf('37', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         ((k3_subset_1 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.46/0.65      inference('sup-', [status(thm)], ['35', '36'])).
% 0.46/0.65  thf('38', plain, (![X13 : $i]: (r1_tarski @ k1_xboole_0 @ X13)),
% 0.46/0.65      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.46/0.65  thf('39', plain,
% 0.46/0.65      (![X11 : $i, X12 : $i]:
% 0.46/0.65         (((k3_xboole_0 @ X11 @ X12) = (X11)) | ~ (r1_tarski @ X11 @ X12))),
% 0.46/0.65      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.46/0.65  thf('40', plain,
% 0.46/0.65      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.46/0.65      inference('sup-', [status(thm)], ['38', '39'])).
% 0.46/0.65  thf('41', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.46/0.65      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.46/0.65  thf('42', plain,
% 0.46/0.65      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.46/0.65      inference('sup+', [status(thm)], ['40', '41'])).
% 0.46/0.65  thf('43', plain,
% 0.46/0.65      (![X4 : $i, X5 : $i]:
% 0.46/0.65         ((k4_xboole_0 @ X4 @ X5)
% 0.46/0.65           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 0.46/0.65      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.46/0.65  thf('44', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.46/0.65      inference('sup+', [status(thm)], ['42', '43'])).
% 0.46/0.65  thf(t5_boole, axiom,
% 0.46/0.65    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.46/0.65  thf('45', plain, (![X16 : $i]: ((k5_xboole_0 @ X16 @ k1_xboole_0) = (X16))),
% 0.46/0.65      inference('cnf', [status(esa)], [t5_boole])).
% 0.46/0.65  thf('46', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.46/0.65      inference('sup+', [status(thm)], ['44', '45'])).
% 0.46/0.65  thf('47', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 0.46/0.65      inference('demod', [status(thm)], ['37', '46'])).
% 0.46/0.65  thf('48', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.46/0.65      inference('demod', [status(thm)], ['34', '47'])).
% 0.46/0.65  thf('49', plain,
% 0.46/0.65      (![X56 : $i, X57 : $i]:
% 0.46/0.65         (~ (m1_subset_1 @ X56 @ X57)
% 0.46/0.65          | (r2_hidden @ X56 @ X57)
% 0.46/0.65          | (v1_xboole_0 @ X57))),
% 0.46/0.65      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.46/0.65  thf('50', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 0.46/0.65          | (r2_hidden @ X0 @ (k1_zfmisc_1 @ X0)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['48', '49'])).
% 0.46/0.65  thf('51', plain, (![X64 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X64))),
% 0.46/0.65      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.46/0.65  thf('52', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.46/0.65      inference('clc', [status(thm)], ['50', '51'])).
% 0.46/0.65  thf('53', plain,
% 0.46/0.65      (![X50 : $i, X52 : $i]:
% 0.46/0.65         ((r1_tarski @ X52 @ X50) | ~ (r2_hidden @ X52 @ (k1_zfmisc_1 @ X50)))),
% 0.46/0.65      inference('simplify', [status(thm)], ['11'])).
% 0.46/0.65  thf('54', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.46/0.65      inference('sup-', [status(thm)], ['52', '53'])).
% 0.46/0.65  thf('55', plain,
% 0.46/0.65      (![X11 : $i, X12 : $i]:
% 0.46/0.65         (((k3_xboole_0 @ X11 @ X12) = (X11)) | ~ (r1_tarski @ X11 @ X12))),
% 0.46/0.65      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.46/0.65  thf('56', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.46/0.65      inference('sup-', [status(thm)], ['54', '55'])).
% 0.46/0.65  thf('57', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.46/0.65      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.46/0.65  thf('58', plain,
% 0.46/0.65      (![X4 : $i, X5 : $i]:
% 0.46/0.65         ((k4_xboole_0 @ X4 @ X5)
% 0.46/0.65           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 0.46/0.65      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.46/0.65  thf('59', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]:
% 0.46/0.65         ((k4_xboole_0 @ X0 @ X1)
% 0.46/0.65           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.46/0.65      inference('sup+', [status(thm)], ['57', '58'])).
% 0.46/0.65  thf('60', plain,
% 0.46/0.65      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.46/0.65      inference('sup+', [status(thm)], ['56', '59'])).
% 0.46/0.65  thf(t21_xboole_1, axiom,
% 0.46/0.65    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.46/0.65  thf('61', plain,
% 0.46/0.65      (![X9 : $i, X10 : $i]:
% 0.46/0.65         ((k3_xboole_0 @ X9 @ (k2_xboole_0 @ X9 @ X10)) = (X9))),
% 0.46/0.65      inference('cnf', [status(esa)], [t21_xboole_1])).
% 0.46/0.65  thf(l51_zfmisc_1, axiom,
% 0.46/0.65    (![A:$i,B:$i]:
% 0.46/0.65     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.46/0.65  thf('62', plain,
% 0.46/0.65      (![X54 : $i, X55 : $i]:
% 0.46/0.65         ((k3_tarski @ (k2_tarski @ X54 @ X55)) = (k2_xboole_0 @ X54 @ X55))),
% 0.46/0.65      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.46/0.65  thf('63', plain,
% 0.46/0.65      (![X9 : $i, X10 : $i]:
% 0.46/0.65         ((k3_xboole_0 @ X9 @ (k3_tarski @ (k2_tarski @ X9 @ X10))) = (X9))),
% 0.46/0.65      inference('demod', [status(thm)], ['61', '62'])).
% 0.46/0.65  thf('64', plain,
% 0.46/0.65      (![X4 : $i, X5 : $i]:
% 0.46/0.65         ((k4_xboole_0 @ X4 @ X5)
% 0.46/0.65           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 0.46/0.65      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.46/0.65  thf('65', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]:
% 0.46/0.65         ((k4_xboole_0 @ X0 @ (k3_tarski @ (k2_tarski @ X0 @ X1)))
% 0.46/0.65           = (k5_xboole_0 @ X0 @ X0))),
% 0.46/0.65      inference('sup+', [status(thm)], ['63', '64'])).
% 0.46/0.65  thf(t46_xboole_1, axiom,
% 0.46/0.65    (![A:$i,B:$i]:
% 0.46/0.65     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.46/0.65  thf('66', plain,
% 0.46/0.65      (![X14 : $i, X15 : $i]:
% 0.46/0.65         ((k4_xboole_0 @ X14 @ (k2_xboole_0 @ X14 @ X15)) = (k1_xboole_0))),
% 0.46/0.65      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.46/0.65  thf('67', plain,
% 0.46/0.65      (![X54 : $i, X55 : $i]:
% 0.46/0.65         ((k3_tarski @ (k2_tarski @ X54 @ X55)) = (k2_xboole_0 @ X54 @ X55))),
% 0.46/0.65      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.46/0.65  thf('68', plain,
% 0.46/0.65      (![X14 : $i, X15 : $i]:
% 0.46/0.65         ((k4_xboole_0 @ X14 @ (k3_tarski @ (k2_tarski @ X14 @ X15)))
% 0.46/0.65           = (k1_xboole_0))),
% 0.46/0.65      inference('demod', [status(thm)], ['66', '67'])).
% 0.46/0.65  thf('69', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.46/0.65      inference('sup+', [status(thm)], ['65', '68'])).
% 0.46/0.65  thf('70', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.46/0.65      inference('sup+', [status(thm)], ['60', '69'])).
% 0.46/0.65  thf('71', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('72', plain,
% 0.46/0.65      (![X56 : $i, X57 : $i]:
% 0.46/0.65         (~ (m1_subset_1 @ X56 @ X57)
% 0.46/0.65          | (r2_hidden @ X56 @ X57)
% 0.46/0.65          | (v1_xboole_0 @ X57))),
% 0.46/0.65      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.46/0.65  thf('73', plain,
% 0.46/0.65      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.46/0.65        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['71', '72'])).
% 0.46/0.65  thf('74', plain, (![X64 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X64))),
% 0.46/0.65      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.46/0.65  thf('75', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.46/0.65      inference('clc', [status(thm)], ['73', '74'])).
% 0.46/0.65  thf('76', plain,
% 0.46/0.65      (![X50 : $i, X52 : $i]:
% 0.46/0.65         ((r1_tarski @ X52 @ X50) | ~ (r2_hidden @ X52 @ (k1_zfmisc_1 @ X50)))),
% 0.46/0.65      inference('simplify', [status(thm)], ['11'])).
% 0.46/0.65  thf('77', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.46/0.65      inference('sup-', [status(thm)], ['75', '76'])).
% 0.46/0.65  thf('78', plain,
% 0.46/0.65      (![X11 : $i, X12 : $i]:
% 0.46/0.65         (((k3_xboole_0 @ X11 @ X12) = (X11)) | ~ (r1_tarski @ X11 @ X12))),
% 0.46/0.65      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.46/0.65  thf('79', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 0.46/0.65      inference('sup-', [status(thm)], ['77', '78'])).
% 0.46/0.65  thf('80', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]:
% 0.46/0.65         ((k4_xboole_0 @ X0 @ X1)
% 0.46/0.65           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.46/0.65      inference('sup+', [status(thm)], ['57', '58'])).
% 0.46/0.65  thf('81', plain,
% 0.46/0.65      (((k4_xboole_0 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 0.46/0.65      inference('sup+', [status(thm)], ['79', '80'])).
% 0.46/0.65  thf(commutativity_k5_xboole_0, axiom,
% 0.46/0.65    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.46/0.65  thf('82', plain,
% 0.46/0.65      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.46/0.65      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.46/0.65  thf('83', plain,
% 0.46/0.65      (((k4_xboole_0 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_B @ sk_A))),
% 0.46/0.65      inference('demod', [status(thm)], ['81', '82'])).
% 0.46/0.65  thf('84', plain,
% 0.46/0.65      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.46/0.65      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.46/0.65  thf('85', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.46/0.65      inference('sup+', [status(thm)], ['65', '68'])).
% 0.46/0.65  thf(t91_xboole_1, axiom,
% 0.46/0.65    (![A:$i,B:$i,C:$i]:
% 0.46/0.65     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.46/0.65       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.46/0.65  thf('86', plain,
% 0.46/0.65      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.46/0.65         ((k5_xboole_0 @ (k5_xboole_0 @ X17 @ X18) @ X19)
% 0.46/0.65           = (k5_xboole_0 @ X17 @ (k5_xboole_0 @ X18 @ X19)))),
% 0.46/0.65      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.46/0.65  thf('87', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]:
% 0.46/0.65         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.46/0.65           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.46/0.65      inference('sup+', [status(thm)], ['85', '86'])).
% 0.46/0.65  thf('88', plain,
% 0.46/0.65      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.46/0.65      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.46/0.65  thf('89', plain, (![X16 : $i]: ((k5_xboole_0 @ X16 @ k1_xboole_0) = (X16))),
% 0.46/0.65      inference('cnf', [status(esa)], [t5_boole])).
% 0.46/0.65  thf('90', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.46/0.65      inference('sup+', [status(thm)], ['88', '89'])).
% 0.46/0.65  thf('91', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]:
% 0.46/0.65         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.46/0.65      inference('demod', [status(thm)], ['87', '90'])).
% 0.46/0.65  thf('92', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]:
% 0.46/0.65         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.46/0.65      inference('sup+', [status(thm)], ['84', '91'])).
% 0.46/0.65  thf('93', plain,
% 0.46/0.65      (((sk_B) = (k5_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B)))),
% 0.46/0.65      inference('sup+', [status(thm)], ['83', '92'])).
% 0.46/0.65  thf('94', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 0.46/0.65      inference('sup-', [status(thm)], ['77', '78'])).
% 0.46/0.65  thf('95', plain,
% 0.46/0.65      (![X4 : $i, X5 : $i]:
% 0.46/0.65         ((k4_xboole_0 @ X4 @ X5)
% 0.46/0.65           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 0.46/0.65      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.46/0.65  thf('96', plain,
% 0.46/0.65      (((k4_xboole_0 @ sk_B @ sk_A) = (k5_xboole_0 @ sk_B @ sk_B))),
% 0.46/0.65      inference('sup+', [status(thm)], ['94', '95'])).
% 0.46/0.65  thf('97', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.46/0.65      inference('sup+', [status(thm)], ['65', '68'])).
% 0.46/0.65  thf('98', plain, (((k4_xboole_0 @ sk_B @ sk_A) = (k1_xboole_0))),
% 0.46/0.65      inference('demod', [status(thm)], ['96', '97'])).
% 0.46/0.65  thf(t94_xboole_1, axiom,
% 0.46/0.65    (![A:$i,B:$i]:
% 0.46/0.65     ( ( k2_xboole_0 @ A @ B ) =
% 0.46/0.65       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.46/0.65  thf('99', plain,
% 0.46/0.65      (![X20 : $i, X21 : $i]:
% 0.46/0.65         ((k2_xboole_0 @ X20 @ X21)
% 0.46/0.65           = (k5_xboole_0 @ (k5_xboole_0 @ X20 @ X21) @ 
% 0.46/0.65              (k3_xboole_0 @ X20 @ X21)))),
% 0.46/0.65      inference('cnf', [status(esa)], [t94_xboole_1])).
% 0.46/0.65  thf('100', plain,
% 0.46/0.65      (![X54 : $i, X55 : $i]:
% 0.46/0.65         ((k3_tarski @ (k2_tarski @ X54 @ X55)) = (k2_xboole_0 @ X54 @ X55))),
% 0.46/0.65      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.46/0.65  thf('101', plain,
% 0.46/0.65      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.46/0.65         ((k5_xboole_0 @ (k5_xboole_0 @ X17 @ X18) @ X19)
% 0.46/0.65           = (k5_xboole_0 @ X17 @ (k5_xboole_0 @ X18 @ X19)))),
% 0.46/0.65      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.46/0.65  thf('102', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]:
% 0.46/0.65         ((k4_xboole_0 @ X0 @ X1)
% 0.46/0.65           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.46/0.65      inference('sup+', [status(thm)], ['57', '58'])).
% 0.46/0.65  thf('103', plain,
% 0.46/0.65      (![X20 : $i, X21 : $i]:
% 0.46/0.65         ((k3_tarski @ (k2_tarski @ X20 @ X21))
% 0.46/0.65           = (k5_xboole_0 @ X20 @ (k4_xboole_0 @ X21 @ X20)))),
% 0.46/0.65      inference('demod', [status(thm)], ['99', '100', '101', '102'])).
% 0.46/0.65  thf('104', plain,
% 0.46/0.65      (((k3_tarski @ (k2_tarski @ sk_A @ sk_B))
% 0.46/0.65         = (k5_xboole_0 @ sk_A @ k1_xboole_0))),
% 0.46/0.65      inference('sup+', [status(thm)], ['98', '103'])).
% 0.46/0.65  thf('105', plain,
% 0.46/0.65      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.46/0.65      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.46/0.65  thf('106', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.46/0.65      inference('sup+', [status(thm)], ['88', '89'])).
% 0.46/0.65  thf('107', plain, (((k3_tarski @ (k2_tarski @ sk_A @ sk_B)) = (sk_A))),
% 0.46/0.65      inference('demod', [status(thm)], ['104', '105', '106'])).
% 0.46/0.65  thf('108', plain,
% 0.46/0.65      (![X9 : $i, X10 : $i]:
% 0.46/0.65         ((k3_xboole_0 @ X9 @ (k3_tarski @ (k2_tarski @ X9 @ X10))) = (X9))),
% 0.46/0.65      inference('demod', [status(thm)], ['61', '62'])).
% 0.46/0.65  thf('109', plain, (((k3_xboole_0 @ sk_A @ sk_A) = (sk_A))),
% 0.46/0.65      inference('sup+', [status(thm)], ['107', '108'])).
% 0.46/0.65  thf('110', plain,
% 0.46/0.65      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.46/0.65         ((k5_xboole_0 @ (k3_xboole_0 @ X6 @ X8) @ (k3_xboole_0 @ X7 @ X8))
% 0.46/0.65           = (k3_xboole_0 @ (k5_xboole_0 @ X6 @ X7) @ X8))),
% 0.46/0.65      inference('cnf', [status(esa)], [t112_xboole_1])).
% 0.46/0.65  thf('111', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         ((k5_xboole_0 @ sk_A @ (k3_xboole_0 @ X0 @ sk_A))
% 0.46/0.65           = (k3_xboole_0 @ (k5_xboole_0 @ sk_A @ X0) @ sk_A))),
% 0.46/0.65      inference('sup+', [status(thm)], ['109', '110'])).
% 0.46/0.65  thf('112', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]:
% 0.46/0.65         ((k4_xboole_0 @ X0 @ X1)
% 0.46/0.65           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.46/0.65      inference('sup+', [status(thm)], ['57', '58'])).
% 0.46/0.65  thf('113', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.46/0.65      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.46/0.65  thf('114', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         ((k4_xboole_0 @ sk_A @ X0)
% 0.46/0.65           = (k3_xboole_0 @ sk_A @ (k5_xboole_0 @ sk_A @ X0)))),
% 0.46/0.65      inference('demod', [status(thm)], ['111', '112', '113'])).
% 0.46/0.65  thf('115', plain,
% 0.46/0.65      (((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B))
% 0.46/0.65         = (k3_xboole_0 @ sk_A @ sk_B))),
% 0.46/0.65      inference('sup+', [status(thm)], ['93', '114'])).
% 0.46/0.65  thf('116', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.46/0.65      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.46/0.65  thf('117', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 0.46/0.65      inference('sup-', [status(thm)], ['77', '78'])).
% 0.46/0.65  thf('118', plain,
% 0.46/0.65      (((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B)) = (sk_B))),
% 0.46/0.65      inference('demod', [status(thm)], ['115', '116', '117'])).
% 0.46/0.65  thf('119', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.46/0.65      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.46/0.65  thf('120', plain,
% 0.46/0.65      (((k1_xboole_0) = (k3_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B)))),
% 0.46/0.65      inference('demod', [status(thm)], ['24', '70', '118', '119'])).
% 0.46/0.65  thf('121', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]:
% 0.46/0.65         ((k4_xboole_0 @ X0 @ X1)
% 0.46/0.65           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.46/0.65      inference('sup+', [status(thm)], ['57', '58'])).
% 0.46/0.65  thf('122', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]:
% 0.46/0.65         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.46/0.65      inference('sup+', [status(thm)], ['84', '91'])).
% 0.46/0.65  thf('123', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]:
% 0.46/0.65         ((X1)
% 0.46/0.65           = (k5_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0)))),
% 0.46/0.65      inference('sup+', [status(thm)], ['121', '122'])).
% 0.46/0.65  thf('124', plain,
% 0.46/0.65      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.46/0.65      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.46/0.65  thf('125', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]:
% 0.46/0.65         ((X1)
% 0.46/0.65           = (k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X0 @ X1)))),
% 0.46/0.65      inference('demod', [status(thm)], ['123', '124'])).
% 0.46/0.65  thf('126', plain,
% 0.46/0.65      (((k4_xboole_0 @ sk_A @ sk_B)
% 0.46/0.65         = (k5_xboole_0 @ (k4_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_B) @ 
% 0.46/0.65            k1_xboole_0))),
% 0.46/0.65      inference('sup+', [status(thm)], ['120', '125'])).
% 0.46/0.65  thf('127', plain,
% 0.46/0.65      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.46/0.65      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.46/0.65  thf('128', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.46/0.65      inference('sup+', [status(thm)], ['88', '89'])).
% 0.46/0.65  thf('129', plain,
% 0.46/0.65      (((k4_xboole_0 @ sk_A @ sk_B)
% 0.46/0.65         = (k4_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_B))),
% 0.46/0.65      inference('demod', [status(thm)], ['126', '127', '128'])).
% 0.46/0.65  thf('130', plain,
% 0.46/0.65      (![X20 : $i, X21 : $i]:
% 0.46/0.65         ((k3_tarski @ (k2_tarski @ X20 @ X21))
% 0.46/0.65           = (k5_xboole_0 @ X20 @ (k4_xboole_0 @ X21 @ X20)))),
% 0.46/0.65      inference('demod', [status(thm)], ['99', '100', '101', '102'])).
% 0.46/0.65  thf('131', plain,
% 0.46/0.65      (((k3_tarski @ (k2_tarski @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B)))
% 0.46/0.65         = (k5_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B)))),
% 0.46/0.65      inference('sup+', [status(thm)], ['129', '130'])).
% 0.46/0.65  thf('132', plain,
% 0.46/0.65      (![X20 : $i, X21 : $i]:
% 0.46/0.65         ((k3_tarski @ (k2_tarski @ X20 @ X21))
% 0.46/0.65           = (k5_xboole_0 @ X20 @ (k4_xboole_0 @ X21 @ X20)))),
% 0.46/0.65      inference('demod', [status(thm)], ['99', '100', '101', '102'])).
% 0.46/0.65  thf('133', plain,
% 0.46/0.65      (((k3_tarski @ (k2_tarski @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B)))
% 0.46/0.65         = (k3_tarski @ (k2_tarski @ sk_B @ sk_A)))),
% 0.46/0.65      inference('demod', [status(thm)], ['131', '132'])).
% 0.46/0.65  thf('134', plain,
% 0.46/0.65      (((k4_xboole_0 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_B @ sk_A))),
% 0.46/0.65      inference('demod', [status(thm)], ['81', '82'])).
% 0.46/0.65  thf('135', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]:
% 0.46/0.65         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.46/0.65      inference('demod', [status(thm)], ['87', '90'])).
% 0.46/0.65  thf('136', plain,
% 0.46/0.65      (((sk_A) = (k5_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B)))),
% 0.46/0.65      inference('sup+', [status(thm)], ['134', '135'])).
% 0.46/0.65  thf('137', plain,
% 0.46/0.65      (![X20 : $i, X21 : $i]:
% 0.46/0.65         ((k3_tarski @ (k2_tarski @ X20 @ X21))
% 0.46/0.65           = (k5_xboole_0 @ X20 @ (k4_xboole_0 @ X21 @ X20)))),
% 0.46/0.65      inference('demod', [status(thm)], ['99', '100', '101', '102'])).
% 0.46/0.65  thf('138', plain, (((sk_A) = (k3_tarski @ (k2_tarski @ sk_B @ sk_A)))),
% 0.46/0.65      inference('demod', [status(thm)], ['136', '137'])).
% 0.46/0.65  thf('139', plain,
% 0.46/0.65      (((k3_tarski @ (k2_tarski @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B))) = (sk_A))),
% 0.46/0.65      inference('demod', [status(thm)], ['133', '138'])).
% 0.46/0.65  thf('140', plain,
% 0.46/0.65      (((k4_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 0.46/0.65         != (k2_subset_1 @ sk_A))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.46/0.65  thf('141', plain, (![X59 : $i]: ((k2_subset_1 @ X59) = (X59))),
% 0.46/0.65      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.46/0.65  thf('142', plain,
% 0.46/0.65      (((k4_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)) != (sk_A))),
% 0.46/0.65      inference('demod', [status(thm)], ['140', '141'])).
% 0.46/0.65  thf('143', plain,
% 0.46/0.65      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.46/0.65      inference('sup-', [status(thm)], ['3', '4'])).
% 0.46/0.65  thf('144', plain,
% 0.46/0.65      (((k4_subset_1 @ sk_A @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B)) != (sk_A))),
% 0.46/0.65      inference('demod', [status(thm)], ['142', '143'])).
% 0.46/0.65  thf('145', plain,
% 0.46/0.65      ((m1_subset_1 @ (k4_xboole_0 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.46/0.65      inference('demod', [status(thm)], ['2', '5'])).
% 0.46/0.65  thf('146', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf(redefinition_k4_subset_1, axiom,
% 0.46/0.65    (![A:$i,B:$i,C:$i]:
% 0.46/0.65     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.46/0.65         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.46/0.65       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.46/0.65  thf('147', plain,
% 0.46/0.65      (![X65 : $i, X66 : $i, X67 : $i]:
% 0.46/0.65         (~ (m1_subset_1 @ X65 @ (k1_zfmisc_1 @ X66))
% 0.46/0.65          | ~ (m1_subset_1 @ X67 @ (k1_zfmisc_1 @ X66))
% 0.46/0.65          | ((k4_subset_1 @ X66 @ X65 @ X67) = (k2_xboole_0 @ X65 @ X67)))),
% 0.46/0.65      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.46/0.65  thf('148', plain,
% 0.46/0.65      (![X54 : $i, X55 : $i]:
% 0.46/0.65         ((k3_tarski @ (k2_tarski @ X54 @ X55)) = (k2_xboole_0 @ X54 @ X55))),
% 0.46/0.65      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.46/0.65  thf('149', plain,
% 0.46/0.65      (![X65 : $i, X66 : $i, X67 : $i]:
% 0.46/0.65         (~ (m1_subset_1 @ X65 @ (k1_zfmisc_1 @ X66))
% 0.46/0.65          | ~ (m1_subset_1 @ X67 @ (k1_zfmisc_1 @ X66))
% 0.46/0.65          | ((k4_subset_1 @ X66 @ X65 @ X67)
% 0.46/0.65              = (k3_tarski @ (k2_tarski @ X65 @ X67))))),
% 0.46/0.65      inference('demod', [status(thm)], ['147', '148'])).
% 0.46/0.65  thf('150', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (((k4_subset_1 @ sk_A @ sk_B @ X0)
% 0.46/0.65            = (k3_tarski @ (k2_tarski @ sk_B @ X0)))
% 0.46/0.65          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['146', '149'])).
% 0.46/0.65  thf('151', plain,
% 0.46/0.65      (((k4_subset_1 @ sk_A @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B))
% 0.46/0.65         = (k3_tarski @ (k2_tarski @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B))))),
% 0.46/0.65      inference('sup-', [status(thm)], ['145', '150'])).
% 0.46/0.65  thf('152', plain,
% 0.46/0.65      (((k3_tarski @ (k2_tarski @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B)))
% 0.46/0.65         != (sk_A))),
% 0.46/0.65      inference('demod', [status(thm)], ['144', '151'])).
% 0.46/0.65  thf('153', plain, ($false),
% 0.46/0.65      inference('simplify_reflect-', [status(thm)], ['139', '152'])).
% 0.46/0.65  
% 0.46/0.65  % SZS output end Refutation
% 0.46/0.65  
% 0.46/0.66  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
