%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.kmPqNXEMUs

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:55 EST 2020

% Result     : Theorem 0.61s
% Output     : Refutation 0.61s
% Verified   : 
% Statistics : Number of formulae       :  154 ( 325 expanded)
%              Number of leaves         :   36 ( 116 expanded)
%              Depth                    :   19
%              Number of atoms          : 1155 (2566 expanded)
%              Number of equality atoms :  109 ( 246 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

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

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('1',plain,(
    ! [X56: $i,X57: $i] :
      ( ~ ( m1_subset_1 @ X56 @ X57 )
      | ( r2_hidden @ X56 @ X57 )
      | ( v1_xboole_0 @ X57 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('2',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('3',plain,(
    ! [X64: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X64 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('4',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['2','3'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('5',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ~ ( r2_hidden @ X52 @ X51 )
      | ( r1_tarski @ X52 @ X50 )
      | ( X51
       != ( k1_zfmisc_1 @ X50 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('6',plain,(
    ! [X50: $i,X52: $i] :
      ( ( r1_tarski @ X52 @ X50 )
      | ~ ( r2_hidden @ X52 @ ( k1_zfmisc_1 @ X50 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['4','6'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('8',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('9',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['7','8'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('11',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['9','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('15',plain,(
    ! [X60: $i,X61: $i] :
      ( ( ( k3_subset_1 @ X60 @ X61 )
        = ( k4_xboole_0 @ X60 @ X61 ) )
      | ~ ( m1_subset_1 @ X61 @ ( k1_zfmisc_1 @ X60 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('16',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['13','16'])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('18',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X16 @ X17 ) @ X18 )
      = ( k5_xboole_0 @ X16 @ ( k5_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('19',plain,(
    ! [X19: $i] :
      ( ( k5_xboole_0 @ X19 @ X19 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( k5_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['17','20'])).

thf('22',plain,(
    ! [X19: $i] :
      ( ( k5_xboole_0 @ X19 @ X19 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('23',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X16 @ X17 ) @ X18 )
      = ( k5_xboole_0 @ X16 @ ( k5_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X19: $i] :
      ( ( k5_xboole_0 @ X19 @ X19 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('28',plain,(
    ! [X15: $i] :
      ( ( k5_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['24','29'])).

thf('31',plain,
    ( ( k5_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k5_xboole_0 @ sk_A @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['21','30'])).

thf('32',plain,(
    ! [X15: $i] :
      ( ( k5_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('33',plain,
    ( ( k5_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = sk_A ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('35',plain,(
    ! [X62: $i,X63: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X62 @ X63 ) @ ( k1_zfmisc_1 @ X62 ) )
      | ~ ( m1_subset_1 @ X63 @ ( k1_zfmisc_1 @ X62 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('36',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X56: $i,X57: $i] :
      ( ~ ( m1_subset_1 @ X56 @ X57 )
      | ( r2_hidden @ X56 @ X57 )
      | ( v1_xboole_0 @ X57 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('38',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X64: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X64 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('40',plain,(
    r2_hidden @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X50: $i,X52: $i] :
      ( ( r1_tarski @ X52 @ X50 )
      | ~ ( r2_hidden @ X52 @ ( k1_zfmisc_1 @ X50 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('42',plain,(
    r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_A ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('44',plain,
    ( ( k3_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_A )
    = ( k3_subset_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('46',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k3_subset_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf(t112_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ B ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ A @ C ) @ B ) ) )).

thf('48',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X10 @ X12 ) @ ( k3_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X10 @ X11 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[t112_xboole_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('53',plain,
    ( ( k4_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k3_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['46','52'])).

thf('54',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('55',plain,(
    ! [X60: $i,X61: $i] :
      ( ( ( k3_subset_1 @ X60 @ X61 )
        = ( k4_xboole_0 @ X60 @ X61 ) )
      | ~ ( m1_subset_1 @ X61 @ ( k1_zfmisc_1 @ X60 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('56',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k3_subset_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('58',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('59',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k5_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('61',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k5_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['13','16'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['24','29'])).

thf('64',plain,
    ( sk_B
    = ( k5_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,
    ( sk_B
    = ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['61','64'])).

thf('66',plain,
    ( sk_B
    = ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['56','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('68',plain,
    ( ( k4_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k3_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['53','66','67'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('69',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k4_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X3 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('70',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k4_xboole_0 @ X3 @ X4 ) )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X4 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 )
      | ( X1
        = ( k4_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 )
      | ( X1
        = ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k4_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,(
    ! [X19: $i] :
      ( ( k5_xboole_0 @ X19 @ X19 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('74',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X10 @ X12 ) @ ( k3_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X10 @ X11 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[t112_xboole_1])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X1 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X19: $i] :
      ( ( k5_xboole_0 @ X19 @ X19 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('77',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ~ ( r2_hidden @ X6 @ X4 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('82',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['80','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['77','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['72','85'])).

thf('87',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['68','86'])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['24','29'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X15: $i] :
      ( ( k5_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['88','93'])).

thf('95',plain,
    ( ( k5_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) )
    = ( k3_subset_1 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['87','94'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('97',plain,
    ( ( k4_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
    = ( k3_subset_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['95','96'])).

thf(t94_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('98',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_xboole_0 @ X20 @ X21 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X20 @ X21 ) @ ( k3_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t94_xboole_1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('99',plain,(
    ! [X54: $i,X55: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X54 @ X55 ) )
      = ( k2_xboole_0 @ X54 @ X55 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('100',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X16 @ X17 ) @ X18 )
      = ( k5_xboole_0 @ X16 @ ( k5_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('102',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X20 @ X21 ) )
      = ( k5_xboole_0 @ X20 @ ( k4_xboole_0 @ X21 @ X20 ) ) ) ),
    inference(demod,[status(thm)],['98','99','100','101'])).

thf('103',plain,
    ( ( k3_tarski @ ( k2_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) )
    = ( k5_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['97','102'])).

thf('104',plain,
    ( ( k3_tarski @ ( k2_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) )
    = sk_A ),
    inference('sup+',[status(thm)],['33','103'])).

thf('105',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
 != ( k2_subset_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('106',plain,(
    ! [X59: $i] :
      ( ( k2_subset_1 @ X59 )
      = X59 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('107',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
 != sk_A ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('109',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('110',plain,(
    ! [X65: $i,X66: $i,X67: $i] :
      ( ~ ( m1_subset_1 @ X65 @ ( k1_zfmisc_1 @ X66 ) )
      | ~ ( m1_subset_1 @ X67 @ ( k1_zfmisc_1 @ X66 ) )
      | ( ( k4_subset_1 @ X66 @ X65 @ X67 )
        = ( k2_xboole_0 @ X65 @ X67 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('111',plain,(
    ! [X54: $i,X55: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X54 @ X55 ) )
      = ( k2_xboole_0 @ X54 @ X55 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('112',plain,(
    ! [X65: $i,X66: $i,X67: $i] :
      ( ~ ( m1_subset_1 @ X65 @ ( k1_zfmisc_1 @ X66 ) )
      | ~ ( m1_subset_1 @ X67 @ ( k1_zfmisc_1 @ X66 ) )
      | ( ( k4_subset_1 @ X66 @ X65 @ X67 )
        = ( k3_tarski @ ( k2_tarski @ X65 @ X67 ) ) ) ) ),
    inference(demod,[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ sk_A @ sk_B @ X0 )
        = ( k3_tarski @ ( k2_tarski @ sk_B @ X0 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['109','112'])).

thf('114',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k3_tarski @ ( k2_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['108','113'])).

thf('115',plain,(
    ( k3_tarski @ ( k2_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) )
 != sk_A ),
    inference(demod,[status(thm)],['107','114'])).

thf('116',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['104','115'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.kmPqNXEMUs
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:26:14 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.61/0.82  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.61/0.82  % Solved by: fo/fo7.sh
% 0.61/0.82  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.61/0.82  % done 743 iterations in 0.371s
% 0.61/0.82  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.61/0.82  % SZS output start Refutation
% 0.61/0.82  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.61/0.82  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.61/0.82  thf(sk_B_type, type, sk_B: $i).
% 0.61/0.82  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.61/0.82  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.61/0.82  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.61/0.82  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.61/0.82  thf(sk_A_type, type, sk_A: $i).
% 0.61/0.82  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.61/0.82  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.61/0.82  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.61/0.82  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.61/0.82  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.61/0.82  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.61/0.82  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.61/0.82  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.61/0.82  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.61/0.82  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.61/0.82  thf(t25_subset_1, conjecture,
% 0.61/0.82    (![A:$i,B:$i]:
% 0.61/0.82     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.61/0.82       ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) ) =
% 0.61/0.82         ( k2_subset_1 @ A ) ) ))).
% 0.61/0.82  thf(zf_stmt_0, negated_conjecture,
% 0.61/0.82    (~( ![A:$i,B:$i]:
% 0.61/0.82        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.61/0.82          ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) ) =
% 0.61/0.82            ( k2_subset_1 @ A ) ) ) )),
% 0.61/0.82    inference('cnf.neg', [status(esa)], [t25_subset_1])).
% 0.61/0.82  thf('0', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.61/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.82  thf(d2_subset_1, axiom,
% 0.61/0.82    (![A:$i,B:$i]:
% 0.61/0.82     ( ( ( v1_xboole_0 @ A ) =>
% 0.61/0.82         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.61/0.82       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.61/0.82         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.61/0.82  thf('1', plain,
% 0.61/0.82      (![X56 : $i, X57 : $i]:
% 0.61/0.82         (~ (m1_subset_1 @ X56 @ X57)
% 0.61/0.82          | (r2_hidden @ X56 @ X57)
% 0.61/0.82          | (v1_xboole_0 @ X57))),
% 0.61/0.82      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.61/0.82  thf('2', plain,
% 0.61/0.82      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.61/0.82        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 0.61/0.82      inference('sup-', [status(thm)], ['0', '1'])).
% 0.61/0.82  thf(fc1_subset_1, axiom,
% 0.61/0.82    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.61/0.82  thf('3', plain, (![X64 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X64))),
% 0.61/0.82      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.61/0.82  thf('4', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.61/0.82      inference('clc', [status(thm)], ['2', '3'])).
% 0.61/0.82  thf(d1_zfmisc_1, axiom,
% 0.61/0.82    (![A:$i,B:$i]:
% 0.61/0.82     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.61/0.82       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.61/0.82  thf('5', plain,
% 0.61/0.82      (![X50 : $i, X51 : $i, X52 : $i]:
% 0.61/0.82         (~ (r2_hidden @ X52 @ X51)
% 0.61/0.82          | (r1_tarski @ X52 @ X50)
% 0.61/0.82          | ((X51) != (k1_zfmisc_1 @ X50)))),
% 0.61/0.82      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.61/0.82  thf('6', plain,
% 0.61/0.82      (![X50 : $i, X52 : $i]:
% 0.61/0.82         ((r1_tarski @ X52 @ X50) | ~ (r2_hidden @ X52 @ (k1_zfmisc_1 @ X50)))),
% 0.61/0.82      inference('simplify', [status(thm)], ['5'])).
% 0.61/0.82  thf('7', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.61/0.82      inference('sup-', [status(thm)], ['4', '6'])).
% 0.61/0.82  thf(t28_xboole_1, axiom,
% 0.61/0.82    (![A:$i,B:$i]:
% 0.61/0.82     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.61/0.82  thf('8', plain,
% 0.61/0.82      (![X13 : $i, X14 : $i]:
% 0.61/0.82         (((k3_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_tarski @ X13 @ X14))),
% 0.61/0.82      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.61/0.82  thf('9', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 0.61/0.82      inference('sup-', [status(thm)], ['7', '8'])).
% 0.61/0.82  thf(commutativity_k3_xboole_0, axiom,
% 0.61/0.82    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.61/0.82  thf('10', plain,
% 0.61/0.82      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.61/0.82      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.61/0.82  thf(t100_xboole_1, axiom,
% 0.61/0.82    (![A:$i,B:$i]:
% 0.61/0.82     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.61/0.82  thf('11', plain,
% 0.61/0.82      (![X8 : $i, X9 : $i]:
% 0.61/0.82         ((k4_xboole_0 @ X8 @ X9)
% 0.61/0.82           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.61/0.82      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.61/0.82  thf('12', plain,
% 0.61/0.82      (![X0 : $i, X1 : $i]:
% 0.61/0.82         ((k4_xboole_0 @ X0 @ X1)
% 0.61/0.82           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.61/0.82      inference('sup+', [status(thm)], ['10', '11'])).
% 0.61/0.82  thf('13', plain,
% 0.61/0.82      (((k4_xboole_0 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 0.61/0.82      inference('sup+', [status(thm)], ['9', '12'])).
% 0.61/0.82  thf('14', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.61/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.82  thf(d5_subset_1, axiom,
% 0.61/0.82    (![A:$i,B:$i]:
% 0.61/0.82     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.61/0.82       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.61/0.82  thf('15', plain,
% 0.61/0.82      (![X60 : $i, X61 : $i]:
% 0.61/0.82         (((k3_subset_1 @ X60 @ X61) = (k4_xboole_0 @ X60 @ X61))
% 0.61/0.82          | ~ (m1_subset_1 @ X61 @ (k1_zfmisc_1 @ X60)))),
% 0.61/0.82      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.61/0.82  thf('16', plain,
% 0.61/0.82      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.61/0.82      inference('sup-', [status(thm)], ['14', '15'])).
% 0.61/0.82  thf('17', plain,
% 0.61/0.82      (((k3_subset_1 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 0.61/0.82      inference('demod', [status(thm)], ['13', '16'])).
% 0.61/0.82  thf(t91_xboole_1, axiom,
% 0.61/0.82    (![A:$i,B:$i,C:$i]:
% 0.61/0.82     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.61/0.82       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.61/0.82  thf('18', plain,
% 0.61/0.82      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.61/0.82         ((k5_xboole_0 @ (k5_xboole_0 @ X16 @ X17) @ X18)
% 0.61/0.82           = (k5_xboole_0 @ X16 @ (k5_xboole_0 @ X17 @ X18)))),
% 0.61/0.82      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.61/0.82  thf(t92_xboole_1, axiom,
% 0.61/0.82    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.61/0.82  thf('19', plain, (![X19 : $i]: ((k5_xboole_0 @ X19 @ X19) = (k1_xboole_0))),
% 0.61/0.82      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.61/0.82  thf('20', plain,
% 0.61/0.82      (![X0 : $i, X1 : $i]:
% 0.61/0.82         ((k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))
% 0.61/0.82           = (k1_xboole_0))),
% 0.61/0.82      inference('sup+', [status(thm)], ['18', '19'])).
% 0.61/0.82  thf('21', plain,
% 0.61/0.82      (((k5_xboole_0 @ sk_A @ 
% 0.61/0.82         (k5_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))) = (k1_xboole_0))),
% 0.61/0.82      inference('sup+', [status(thm)], ['17', '20'])).
% 0.61/0.82  thf('22', plain, (![X19 : $i]: ((k5_xboole_0 @ X19 @ X19) = (k1_xboole_0))),
% 0.61/0.82      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.61/0.82  thf('23', plain,
% 0.61/0.82      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.61/0.82         ((k5_xboole_0 @ (k5_xboole_0 @ X16 @ X17) @ X18)
% 0.61/0.82           = (k5_xboole_0 @ X16 @ (k5_xboole_0 @ X17 @ X18)))),
% 0.61/0.82      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.61/0.82  thf('24', plain,
% 0.61/0.82      (![X0 : $i, X1 : $i]:
% 0.61/0.82         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.61/0.82           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.61/0.82      inference('sup+', [status(thm)], ['22', '23'])).
% 0.61/0.82  thf('25', plain, (![X19 : $i]: ((k5_xboole_0 @ X19 @ X19) = (k1_xboole_0))),
% 0.61/0.82      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.61/0.82  thf('26', plain,
% 0.61/0.82      (![X0 : $i, X1 : $i]:
% 0.61/0.82         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.61/0.82           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.61/0.82      inference('sup+', [status(thm)], ['22', '23'])).
% 0.61/0.82  thf('27', plain,
% 0.61/0.82      (![X0 : $i]:
% 0.61/0.82         ((k5_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.61/0.82      inference('sup+', [status(thm)], ['25', '26'])).
% 0.61/0.82  thf(t5_boole, axiom,
% 0.61/0.82    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.61/0.82  thf('28', plain, (![X15 : $i]: ((k5_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 0.61/0.82      inference('cnf', [status(esa)], [t5_boole])).
% 0.61/0.82  thf('29', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.61/0.82      inference('demod', [status(thm)], ['27', '28'])).
% 0.61/0.82  thf('30', plain,
% 0.61/0.82      (![X0 : $i, X1 : $i]:
% 0.61/0.82         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.61/0.82      inference('demod', [status(thm)], ['24', '29'])).
% 0.61/0.82  thf('31', plain,
% 0.61/0.82      (((k5_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 0.61/0.82         = (k5_xboole_0 @ sk_A @ k1_xboole_0))),
% 0.61/0.82      inference('sup+', [status(thm)], ['21', '30'])).
% 0.61/0.82  thf('32', plain, (![X15 : $i]: ((k5_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 0.61/0.82      inference('cnf', [status(esa)], [t5_boole])).
% 0.61/0.82  thf('33', plain,
% 0.61/0.82      (((k5_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)) = (sk_A))),
% 0.61/0.82      inference('demod', [status(thm)], ['31', '32'])).
% 0.61/0.82  thf('34', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.61/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.82  thf(dt_k3_subset_1, axiom,
% 0.61/0.82    (![A:$i,B:$i]:
% 0.61/0.82     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.61/0.82       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.61/0.82  thf('35', plain,
% 0.61/0.82      (![X62 : $i, X63 : $i]:
% 0.61/0.82         ((m1_subset_1 @ (k3_subset_1 @ X62 @ X63) @ (k1_zfmisc_1 @ X62))
% 0.61/0.82          | ~ (m1_subset_1 @ X63 @ (k1_zfmisc_1 @ X62)))),
% 0.61/0.82      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.61/0.82  thf('36', plain,
% 0.61/0.82      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.61/0.82      inference('sup-', [status(thm)], ['34', '35'])).
% 0.61/0.82  thf('37', plain,
% 0.61/0.82      (![X56 : $i, X57 : $i]:
% 0.61/0.82         (~ (m1_subset_1 @ X56 @ X57)
% 0.61/0.82          | (r2_hidden @ X56 @ X57)
% 0.61/0.82          | (v1_xboole_0 @ X57))),
% 0.61/0.82      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.61/0.82  thf('38', plain,
% 0.61/0.82      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.61/0.82        | (r2_hidden @ (k3_subset_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A)))),
% 0.61/0.82      inference('sup-', [status(thm)], ['36', '37'])).
% 0.61/0.82  thf('39', plain, (![X64 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X64))),
% 0.61/0.82      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.61/0.82  thf('40', plain,
% 0.61/0.82      ((r2_hidden @ (k3_subset_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.61/0.82      inference('clc', [status(thm)], ['38', '39'])).
% 0.61/0.82  thf('41', plain,
% 0.61/0.82      (![X50 : $i, X52 : $i]:
% 0.61/0.82         ((r1_tarski @ X52 @ X50) | ~ (r2_hidden @ X52 @ (k1_zfmisc_1 @ X50)))),
% 0.61/0.82      inference('simplify', [status(thm)], ['5'])).
% 0.61/0.82  thf('42', plain, ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_A)),
% 0.61/0.82      inference('sup-', [status(thm)], ['40', '41'])).
% 0.61/0.82  thf('43', plain,
% 0.61/0.82      (![X13 : $i, X14 : $i]:
% 0.61/0.82         (((k3_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_tarski @ X13 @ X14))),
% 0.61/0.82      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.61/0.82  thf('44', plain,
% 0.61/0.82      (((k3_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ sk_A)
% 0.61/0.82         = (k3_subset_1 @ sk_A @ sk_B))),
% 0.61/0.82      inference('sup-', [status(thm)], ['42', '43'])).
% 0.61/0.82  thf('45', plain,
% 0.61/0.82      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.61/0.82      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.61/0.82  thf('46', plain,
% 0.61/0.82      (((k3_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B))
% 0.61/0.82         = (k3_subset_1 @ sk_A @ sk_B))),
% 0.61/0.82      inference('demod', [status(thm)], ['44', '45'])).
% 0.61/0.82  thf('47', plain,
% 0.61/0.82      (![X8 : $i, X9 : $i]:
% 0.61/0.82         ((k4_xboole_0 @ X8 @ X9)
% 0.61/0.82           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.61/0.82      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.61/0.82  thf(t112_xboole_1, axiom,
% 0.61/0.82    (![A:$i,B:$i,C:$i]:
% 0.61/0.82     ( ( k5_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ B ) ) =
% 0.61/0.82       ( k3_xboole_0 @ ( k5_xboole_0 @ A @ C ) @ B ) ))).
% 0.61/0.82  thf('48', plain,
% 0.61/0.82      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.61/0.82         ((k5_xboole_0 @ (k3_xboole_0 @ X10 @ X12) @ (k3_xboole_0 @ X11 @ X12))
% 0.61/0.82           = (k3_xboole_0 @ (k5_xboole_0 @ X10 @ X11) @ X12))),
% 0.61/0.82      inference('cnf', [status(esa)], [t112_xboole_1])).
% 0.61/0.82  thf('49', plain,
% 0.61/0.82      (![X0 : $i, X1 : $i]:
% 0.61/0.82         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0)
% 0.61/0.82           = (k3_xboole_0 @ (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)) @ X0))),
% 0.61/0.82      inference('sup+', [status(thm)], ['47', '48'])).
% 0.61/0.82  thf('50', plain,
% 0.61/0.82      (![X8 : $i, X9 : $i]:
% 0.61/0.82         ((k4_xboole_0 @ X8 @ X9)
% 0.61/0.82           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.61/0.82      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.61/0.82  thf('51', plain,
% 0.61/0.82      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.61/0.82      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.61/0.82  thf('52', plain,
% 0.61/0.82      (![X0 : $i, X1 : $i]:
% 0.61/0.82         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0)
% 0.61/0.82           = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.61/0.82      inference('demod', [status(thm)], ['49', '50', '51'])).
% 0.61/0.82  thf('53', plain,
% 0.61/0.82      (((k4_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ 
% 0.61/0.82         (k3_subset_1 @ sk_A @ sk_B))
% 0.61/0.82         = (k3_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ 
% 0.61/0.82            (k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B))))),
% 0.61/0.82      inference('sup+', [status(thm)], ['46', '52'])).
% 0.61/0.82  thf('54', plain,
% 0.61/0.82      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.61/0.82      inference('sup-', [status(thm)], ['34', '35'])).
% 0.61/0.82  thf('55', plain,
% 0.61/0.82      (![X60 : $i, X61 : $i]:
% 0.61/0.82         (((k3_subset_1 @ X60 @ X61) = (k4_xboole_0 @ X60 @ X61))
% 0.61/0.82          | ~ (m1_subset_1 @ X61 @ (k1_zfmisc_1 @ X60)))),
% 0.61/0.82      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.61/0.82  thf('56', plain,
% 0.61/0.82      (((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B))
% 0.61/0.82         = (k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.61/0.82      inference('sup-', [status(thm)], ['54', '55'])).
% 0.61/0.82  thf('57', plain,
% 0.61/0.82      (((k3_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B))
% 0.61/0.82         = (k3_subset_1 @ sk_A @ sk_B))),
% 0.61/0.82      inference('demod', [status(thm)], ['44', '45'])).
% 0.61/0.82  thf('58', plain,
% 0.61/0.82      (![X8 : $i, X9 : $i]:
% 0.61/0.82         ((k4_xboole_0 @ X8 @ X9)
% 0.61/0.82           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.61/0.82      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.61/0.82  thf('59', plain,
% 0.61/0.82      (((k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B))
% 0.61/0.82         = (k5_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.61/0.82      inference('sup+', [status(thm)], ['57', '58'])).
% 0.61/0.82  thf('60', plain,
% 0.61/0.82      (((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B))
% 0.61/0.82         = (k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.61/0.82      inference('sup-', [status(thm)], ['54', '55'])).
% 0.61/0.82  thf('61', plain,
% 0.61/0.82      (((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B))
% 0.61/0.82         = (k5_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.61/0.82      inference('demod', [status(thm)], ['59', '60'])).
% 0.61/0.82  thf('62', plain,
% 0.61/0.82      (((k3_subset_1 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 0.61/0.82      inference('demod', [status(thm)], ['13', '16'])).
% 0.61/0.82  thf('63', plain,
% 0.61/0.82      (![X0 : $i, X1 : $i]:
% 0.61/0.82         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.61/0.82      inference('demod', [status(thm)], ['24', '29'])).
% 0.61/0.82  thf('64', plain,
% 0.61/0.82      (((sk_B) = (k5_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.61/0.82      inference('sup+', [status(thm)], ['62', '63'])).
% 0.61/0.82  thf('65', plain,
% 0.61/0.82      (((sk_B) = (k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.61/0.82      inference('sup+', [status(thm)], ['61', '64'])).
% 0.61/0.82  thf('66', plain,
% 0.61/0.82      (((sk_B) = (k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.61/0.82      inference('demod', [status(thm)], ['56', '65'])).
% 0.61/0.82  thf('67', plain,
% 0.61/0.82      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.61/0.82      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.61/0.82  thf('68', plain,
% 0.61/0.82      (((k4_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ 
% 0.61/0.82         (k3_subset_1 @ sk_A @ sk_B))
% 0.61/0.82         = (k3_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.61/0.82      inference('demod', [status(thm)], ['53', '66', '67'])).
% 0.61/0.82  thf(d5_xboole_0, axiom,
% 0.61/0.82    (![A:$i,B:$i,C:$i]:
% 0.61/0.82     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.61/0.82       ( ![D:$i]:
% 0.61/0.82         ( ( r2_hidden @ D @ C ) <=>
% 0.61/0.82           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.61/0.82  thf('69', plain,
% 0.61/0.82      (![X3 : $i, X4 : $i, X7 : $i]:
% 0.61/0.82         (((X7) = (k4_xboole_0 @ X3 @ X4))
% 0.61/0.82          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X3)
% 0.61/0.82          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 0.61/0.82      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.61/0.82  thf('70', plain,
% 0.61/0.82      (![X3 : $i, X4 : $i, X7 : $i]:
% 0.61/0.82         (((X7) = (k4_xboole_0 @ X3 @ X4))
% 0.61/0.82          | ~ (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X4)
% 0.61/0.82          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 0.61/0.82      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.61/0.82  thf('71', plain,
% 0.61/0.82      (![X0 : $i, X1 : $i]:
% 0.61/0.82         ((r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1)
% 0.61/0.82          | ((X1) = (k4_xboole_0 @ X0 @ X0))
% 0.61/0.82          | (r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1)
% 0.61/0.82          | ((X1) = (k4_xboole_0 @ X0 @ X0)))),
% 0.61/0.82      inference('sup-', [status(thm)], ['69', '70'])).
% 0.61/0.82  thf('72', plain,
% 0.61/0.82      (![X0 : $i, X1 : $i]:
% 0.61/0.82         (((X1) = (k4_xboole_0 @ X0 @ X0))
% 0.61/0.82          | (r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1))),
% 0.61/0.82      inference('simplify', [status(thm)], ['71'])).
% 0.61/0.82  thf('73', plain, (![X19 : $i]: ((k5_xboole_0 @ X19 @ X19) = (k1_xboole_0))),
% 0.61/0.82      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.61/0.82  thf('74', plain,
% 0.61/0.82      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.61/0.82         ((k5_xboole_0 @ (k3_xboole_0 @ X10 @ X12) @ (k3_xboole_0 @ X11 @ X12))
% 0.61/0.82           = (k3_xboole_0 @ (k5_xboole_0 @ X10 @ X11) @ X12))),
% 0.61/0.82      inference('cnf', [status(esa)], [t112_xboole_1])).
% 0.61/0.82  thf('75', plain,
% 0.61/0.82      (![X0 : $i, X1 : $i]:
% 0.61/0.82         ((k1_xboole_0) = (k3_xboole_0 @ (k5_xboole_0 @ X1 @ X1) @ X0))),
% 0.61/0.82      inference('sup+', [status(thm)], ['73', '74'])).
% 0.61/0.82  thf('76', plain, (![X19 : $i]: ((k5_xboole_0 @ X19 @ X19) = (k1_xboole_0))),
% 0.61/0.82      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.61/0.82  thf('77', plain,
% 0.61/0.82      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 0.61/0.82      inference('demod', [status(thm)], ['75', '76'])).
% 0.61/0.82  thf('78', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.61/0.82      inference('demod', [status(thm)], ['27', '28'])).
% 0.61/0.82  thf('79', plain,
% 0.61/0.82      (![X0 : $i, X1 : $i]:
% 0.61/0.82         ((k4_xboole_0 @ X0 @ X1)
% 0.61/0.82           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.61/0.82      inference('sup+', [status(thm)], ['10', '11'])).
% 0.61/0.82  thf('80', plain,
% 0.61/0.82      (![X0 : $i]:
% 0.61/0.82         ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.61/0.82      inference('sup+', [status(thm)], ['78', '79'])).
% 0.61/0.82  thf('81', plain,
% 0.61/0.82      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.61/0.82         (~ (r2_hidden @ X6 @ X5)
% 0.61/0.82          | ~ (r2_hidden @ X6 @ X4)
% 0.61/0.82          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 0.61/0.82      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.61/0.82  thf('82', plain,
% 0.61/0.82      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.61/0.82         (~ (r2_hidden @ X6 @ X4)
% 0.61/0.82          | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 0.61/0.82      inference('simplify', [status(thm)], ['81'])).
% 0.61/0.82  thf('83', plain,
% 0.61/0.82      (![X0 : $i, X1 : $i]:
% 0.61/0.82         (~ (r2_hidden @ X1 @ (k3_xboole_0 @ X0 @ k1_xboole_0))
% 0.61/0.82          | ~ (r2_hidden @ X1 @ X0))),
% 0.61/0.82      inference('sup-', [status(thm)], ['80', '82'])).
% 0.61/0.82  thf('84', plain,
% 0.61/0.82      (![X0 : $i]:
% 0.61/0.82         (~ (r2_hidden @ X0 @ k1_xboole_0) | ~ (r2_hidden @ X0 @ k1_xboole_0))),
% 0.61/0.82      inference('sup-', [status(thm)], ['77', '83'])).
% 0.61/0.82  thf('85', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.61/0.82      inference('simplify', [status(thm)], ['84'])).
% 0.61/0.82  thf('86', plain, (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X0))),
% 0.61/0.82      inference('sup-', [status(thm)], ['72', '85'])).
% 0.61/0.82  thf('87', plain,
% 0.61/0.82      (((k1_xboole_0) = (k3_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.61/0.82      inference('demod', [status(thm)], ['68', '86'])).
% 0.61/0.82  thf('88', plain,
% 0.61/0.82      (![X0 : $i, X1 : $i]:
% 0.61/0.82         ((k4_xboole_0 @ X0 @ X1)
% 0.61/0.82           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.61/0.82      inference('sup+', [status(thm)], ['10', '11'])).
% 0.61/0.82  thf('89', plain,
% 0.61/0.82      (![X0 : $i, X1 : $i]:
% 0.61/0.82         ((k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))
% 0.61/0.82           = (k1_xboole_0))),
% 0.61/0.82      inference('sup+', [status(thm)], ['18', '19'])).
% 0.61/0.82  thf('90', plain,
% 0.61/0.82      (![X0 : $i, X1 : $i]:
% 0.61/0.82         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.61/0.82      inference('demod', [status(thm)], ['24', '29'])).
% 0.61/0.82  thf('91', plain,
% 0.61/0.82      (![X0 : $i, X1 : $i]:
% 0.61/0.82         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))
% 0.61/0.82           = (k5_xboole_0 @ X1 @ k1_xboole_0))),
% 0.61/0.82      inference('sup+', [status(thm)], ['89', '90'])).
% 0.61/0.82  thf('92', plain, (![X15 : $i]: ((k5_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 0.61/0.82      inference('cnf', [status(esa)], [t5_boole])).
% 0.61/0.82  thf('93', plain,
% 0.61/0.82      (![X0 : $i, X1 : $i]:
% 0.61/0.82         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)) = (X1))),
% 0.61/0.82      inference('demod', [status(thm)], ['91', '92'])).
% 0.61/0.82  thf('94', plain,
% 0.61/0.82      (![X0 : $i, X1 : $i]:
% 0.61/0.82         ((k5_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0))
% 0.61/0.82           = (X1))),
% 0.61/0.82      inference('sup+', [status(thm)], ['88', '93'])).
% 0.61/0.82  thf('95', plain,
% 0.61/0.82      (((k5_xboole_0 @ k1_xboole_0 @ 
% 0.61/0.82         (k4_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))
% 0.61/0.82         = (k3_subset_1 @ sk_A @ sk_B))),
% 0.61/0.82      inference('sup+', [status(thm)], ['87', '94'])).
% 0.61/0.82  thf('96', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.61/0.82      inference('demod', [status(thm)], ['27', '28'])).
% 0.61/0.82  thf('97', plain,
% 0.61/0.82      (((k4_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)
% 0.61/0.82         = (k3_subset_1 @ sk_A @ sk_B))),
% 0.61/0.82      inference('demod', [status(thm)], ['95', '96'])).
% 0.61/0.82  thf(t94_xboole_1, axiom,
% 0.61/0.82    (![A:$i,B:$i]:
% 0.61/0.82     ( ( k2_xboole_0 @ A @ B ) =
% 0.61/0.82       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.61/0.82  thf('98', plain,
% 0.61/0.82      (![X20 : $i, X21 : $i]:
% 0.61/0.82         ((k2_xboole_0 @ X20 @ X21)
% 0.61/0.82           = (k5_xboole_0 @ (k5_xboole_0 @ X20 @ X21) @ 
% 0.61/0.82              (k3_xboole_0 @ X20 @ X21)))),
% 0.61/0.82      inference('cnf', [status(esa)], [t94_xboole_1])).
% 0.61/0.82  thf(l51_zfmisc_1, axiom,
% 0.61/0.82    (![A:$i,B:$i]:
% 0.61/0.82     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.61/0.82  thf('99', plain,
% 0.61/0.82      (![X54 : $i, X55 : $i]:
% 0.61/0.82         ((k3_tarski @ (k2_tarski @ X54 @ X55)) = (k2_xboole_0 @ X54 @ X55))),
% 0.61/0.82      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.61/0.82  thf('100', plain,
% 0.61/0.82      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.61/0.82         ((k5_xboole_0 @ (k5_xboole_0 @ X16 @ X17) @ X18)
% 0.61/0.82           = (k5_xboole_0 @ X16 @ (k5_xboole_0 @ X17 @ X18)))),
% 0.61/0.82      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.61/0.82  thf('101', plain,
% 0.61/0.82      (![X0 : $i, X1 : $i]:
% 0.61/0.82         ((k4_xboole_0 @ X0 @ X1)
% 0.61/0.82           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.61/0.82      inference('sup+', [status(thm)], ['10', '11'])).
% 0.61/0.82  thf('102', plain,
% 0.61/0.82      (![X20 : $i, X21 : $i]:
% 0.61/0.82         ((k3_tarski @ (k2_tarski @ X20 @ X21))
% 0.61/0.82           = (k5_xboole_0 @ X20 @ (k4_xboole_0 @ X21 @ X20)))),
% 0.61/0.82      inference('demod', [status(thm)], ['98', '99', '100', '101'])).
% 0.61/0.82  thf('103', plain,
% 0.61/0.82      (((k3_tarski @ (k2_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))
% 0.61/0.82         = (k5_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.61/0.82      inference('sup+', [status(thm)], ['97', '102'])).
% 0.61/0.82  thf('104', plain,
% 0.61/0.82      (((k3_tarski @ (k2_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))) = (sk_A))),
% 0.61/0.82      inference('sup+', [status(thm)], ['33', '103'])).
% 0.61/0.82  thf('105', plain,
% 0.61/0.82      (((k4_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 0.61/0.82         != (k2_subset_1 @ sk_A))),
% 0.61/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.82  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.61/0.82  thf('106', plain, (![X59 : $i]: ((k2_subset_1 @ X59) = (X59))),
% 0.61/0.82      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.61/0.82  thf('107', plain,
% 0.61/0.82      (((k4_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)) != (sk_A))),
% 0.61/0.82      inference('demod', [status(thm)], ['105', '106'])).
% 0.61/0.82  thf('108', plain,
% 0.61/0.82      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.61/0.82      inference('sup-', [status(thm)], ['34', '35'])).
% 0.61/0.82  thf('109', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.61/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.82  thf(redefinition_k4_subset_1, axiom,
% 0.61/0.82    (![A:$i,B:$i,C:$i]:
% 0.61/0.82     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.61/0.82         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.61/0.82       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.61/0.82  thf('110', plain,
% 0.61/0.82      (![X65 : $i, X66 : $i, X67 : $i]:
% 0.61/0.82         (~ (m1_subset_1 @ X65 @ (k1_zfmisc_1 @ X66))
% 0.61/0.82          | ~ (m1_subset_1 @ X67 @ (k1_zfmisc_1 @ X66))
% 0.61/0.82          | ((k4_subset_1 @ X66 @ X65 @ X67) = (k2_xboole_0 @ X65 @ X67)))),
% 0.61/0.82      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.61/0.82  thf('111', plain,
% 0.61/0.82      (![X54 : $i, X55 : $i]:
% 0.61/0.82         ((k3_tarski @ (k2_tarski @ X54 @ X55)) = (k2_xboole_0 @ X54 @ X55))),
% 0.61/0.82      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.61/0.82  thf('112', plain,
% 0.61/0.82      (![X65 : $i, X66 : $i, X67 : $i]:
% 0.61/0.82         (~ (m1_subset_1 @ X65 @ (k1_zfmisc_1 @ X66))
% 0.61/0.82          | ~ (m1_subset_1 @ X67 @ (k1_zfmisc_1 @ X66))
% 0.61/0.82          | ((k4_subset_1 @ X66 @ X65 @ X67)
% 0.61/0.82              = (k3_tarski @ (k2_tarski @ X65 @ X67))))),
% 0.61/0.82      inference('demod', [status(thm)], ['110', '111'])).
% 0.61/0.82  thf('113', plain,
% 0.61/0.82      (![X0 : $i]:
% 0.61/0.82         (((k4_subset_1 @ sk_A @ sk_B @ X0)
% 0.61/0.82            = (k3_tarski @ (k2_tarski @ sk_B @ X0)))
% 0.61/0.82          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 0.61/0.82      inference('sup-', [status(thm)], ['109', '112'])).
% 0.61/0.82  thf('114', plain,
% 0.61/0.82      (((k4_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 0.61/0.82         = (k3_tarski @ (k2_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))))),
% 0.61/0.82      inference('sup-', [status(thm)], ['108', '113'])).
% 0.61/0.82  thf('115', plain,
% 0.61/0.82      (((k3_tarski @ (k2_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))
% 0.61/0.82         != (sk_A))),
% 0.61/0.82      inference('demod', [status(thm)], ['107', '114'])).
% 0.61/0.82  thf('116', plain, ($false),
% 0.61/0.82      inference('simplify_reflect-', [status(thm)], ['104', '115'])).
% 0.61/0.82  
% 0.61/0.82  % SZS output end Refutation
% 0.61/0.82  
% 0.61/0.83  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
