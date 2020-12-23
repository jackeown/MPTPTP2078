%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gbq1qbKvXD

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:50 EST 2020

% Result     : Theorem 0.78s
% Output     : Refutation 0.78s
% Verified   : 
% Statistics : Number of formulae       :  155 ( 249 expanded)
%              Number of leaves         :   38 (  93 expanded)
%              Depth                    :   15
%              Number of atoms          : 1107 (1894 expanded)
%              Number of equality atoms :  112 ( 197 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X64: $i,X65: $i] :
      ( ( ( k3_subset_1 @ X64 @ X65 )
        = ( k4_xboole_0 @ X64 @ X65 ) )
      | ~ ( m1_subset_1 @ X65 @ ( k1_zfmisc_1 @ X64 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('2',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B_1 )
    = ( k4_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('4',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
    = ( k3_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('6',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
    = ( k3_xboole_0 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('7',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X16 @ X17 ) @ X16 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('8',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_B_1 @ sk_A ) @ sk_A ),
    inference('sup+',[status(thm)],['6','7'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('9',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('10',plain,
    ( ( k3_xboole_0 @ ( k3_xboole_0 @ sk_B_1 @ sk_A ) @ sk_A )
    = ( k3_xboole_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('12',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B_1 @ sk_A ) )
    = ( k3_xboole_0 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['10','11'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('13',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('14',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B_1 @ sk_A ) )
    = ( k5_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
    = ( k3_xboole_0 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('16',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('17',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B_1 @ sk_A ) )
    = ( k3_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B_1 )
    = ( k4_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('19',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X16 @ X17 ) @ X16 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('20',plain,(
    r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B_1 ) @ sk_A ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('22',plain,
    ( ( k3_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) @ sk_A )
    = ( k3_subset_1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('24',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
    = ( k3_subset_1 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B_1 @ sk_A ) )
    = ( k3_subset_1 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['17','24'])).

thf('26',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B_1 )
    = ( k5_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['14','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('28',plain,(
    ! [X60: $i,X61: $i] :
      ( ~ ( m1_subset_1 @ X60 @ X61 )
      | ( r2_hidden @ X60 @ X61 )
      | ( v1_xboole_0 @ X61 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('29',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('30',plain,(
    ! [X66: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X66 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('31',plain,(
    r2_hidden @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['29','30'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('32',plain,(
    ! [X54: $i,X55: $i,X56: $i] :
      ( ~ ( r2_hidden @ X56 @ X55 )
      | ( r1_tarski @ X56 @ X54 )
      | ( X55
       != ( k1_zfmisc_1 @ X54 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('33',plain,(
    ! [X54: $i,X56: $i] :
      ( ( r1_tarski @ X56 @ X54 )
      | ~ ( r2_hidden @ X56 @ ( k1_zfmisc_1 @ X54 ) ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    r1_tarski @ sk_B_1 @ sk_A ),
    inference('sup-',[status(thm)],['31','33'])).

thf('35',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('36',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ sk_A )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['34','35'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('37',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('38',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B_1 )
    = ( k5_xboole_0 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['26','36','37'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('39',plain,(
    ! [X7: $i] :
      ( ( k3_xboole_0 @ X7 @ X7 )
      = X7 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('40',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('42',plain,(
    ! [X15: $i] :
      ( ( k3_xboole_0 @ X15 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('43',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
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
    ! [X20: $i] :
      ( ( k5_xboole_0 @ X20 @ k1_xboole_0 )
      = X20 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X15: $i] :
      ( ( k3_xboole_0 @ X15 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['41','50'])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('52',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X21 @ X22 ) @ X23 )
      = ( k5_xboole_0 @ X21 @ ( k5_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('55',plain,(
    ! [X20: $i] :
      ( ( k5_xboole_0 @ X20 @ k1_xboole_0 )
      = X20 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['53','56'])).

thf('58',plain,
    ( sk_A
    = ( k5_xboole_0 @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['38','57'])).

thf('59',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B_1 )
    = ( k4_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('60',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t112_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ B ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ A @ C ) @ B ) ) )).

thf('62',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X10 @ X12 ) @ ( k3_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X10 @ X11 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[t112_xboole_1])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X2 @ X1 ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X0 @ X2 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['60','63'])).

thf('65',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('66',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X16 @ X17 ) @ X16 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('67',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('72',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['70','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['41','50'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['65','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['64','77','78','79'])).

thf('81',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['59','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('83',plain,
    ( ( k4_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) @ sk_B_1 )
    = ( k5_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('86',plain,
    ( ( k4_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) @ sk_B_1 )
    = ( k3_subset_1 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['83','84','85'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t94_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('88',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k2_xboole_0 @ X24 @ X25 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X24 @ X25 ) @ ( k3_xboole_0 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t94_xboole_1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('89',plain,(
    ! [X58: $i,X59: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X58 @ X59 ) )
      = ( k2_xboole_0 @ X58 @ X59 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('90',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X21 @ X22 ) @ X23 )
      = ( k5_xboole_0 @ X21 @ ( k5_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('91',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X24 @ X25 ) )
      = ( k5_xboole_0 @ X24 @ ( k5_xboole_0 @ X25 @ ( k3_xboole_0 @ X24 @ X25 ) ) ) ) ),
    inference(demod,[status(thm)],['88','89','90'])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X0 @ X1 ) )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['87','91'])).

thf('93',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X0 @ X1 ) )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,
    ( ( k3_tarski @ ( k2_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) )
    = ( k5_xboole_0 @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['86','94'])).

thf('96',plain,
    ( ( k3_tarski @ ( k2_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) )
    = sk_A ),
    inference('sup+',[status(thm)],['58','95'])).

thf('97',plain,(
    ( k4_subset_1 @ sk_A @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
 != ( k2_subset_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('98',plain,(
    ! [X63: $i] :
      ( ( k2_subset_1 @ X63 )
      = X63 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('99',plain,(
    ( k4_subset_1 @ sk_A @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
 != sk_A ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,(
    r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B_1 ) @ sk_A ),
    inference('sup+',[status(thm)],['18','19'])).

thf('101',plain,(
    ! [X53: $i,X54: $i,X55: $i] :
      ( ~ ( r1_tarski @ X53 @ X54 )
      | ( r2_hidden @ X53 @ X55 )
      | ( X55
       != ( k1_zfmisc_1 @ X54 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('102',plain,(
    ! [X53: $i,X54: $i] :
      ( ( r2_hidden @ X53 @ ( k1_zfmisc_1 @ X54 ) )
      | ~ ( r1_tarski @ X53 @ X54 ) ) ),
    inference(simplify,[status(thm)],['101'])).

thf('103',plain,(
    r2_hidden @ ( k3_subset_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['100','102'])).

thf('104',plain,(
    ! [X60: $i,X61: $i] :
      ( ~ ( r2_hidden @ X60 @ X61 )
      | ( m1_subset_1 @ X60 @ X61 )
      | ( v1_xboole_0 @ X61 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('105',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ~ ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('106',plain,(
    ! [X60: $i,X61: $i] :
      ( ( m1_subset_1 @ X60 @ X61 )
      | ~ ( r2_hidden @ X60 @ X61 ) ) ),
    inference(clc,[status(thm)],['104','105'])).

thf('107',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['103','106'])).

thf('108',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('109',plain,(
    ! [X67: $i,X68: $i,X69: $i] :
      ( ~ ( m1_subset_1 @ X67 @ ( k1_zfmisc_1 @ X68 ) )
      | ~ ( m1_subset_1 @ X69 @ ( k1_zfmisc_1 @ X68 ) )
      | ( ( k4_subset_1 @ X68 @ X67 @ X69 )
        = ( k2_xboole_0 @ X67 @ X69 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('110',plain,(
    ! [X58: $i,X59: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X58 @ X59 ) )
      = ( k2_xboole_0 @ X58 @ X59 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('111',plain,(
    ! [X67: $i,X68: $i,X69: $i] :
      ( ~ ( m1_subset_1 @ X67 @ ( k1_zfmisc_1 @ X68 ) )
      | ~ ( m1_subset_1 @ X69 @ ( k1_zfmisc_1 @ X68 ) )
      | ( ( k4_subset_1 @ X68 @ X67 @ X69 )
        = ( k3_tarski @ ( k2_tarski @ X67 @ X69 ) ) ) ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ sk_A @ sk_B_1 @ X0 )
        = ( k3_tarski @ ( k2_tarski @ sk_B_1 @ X0 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['108','111'])).

thf('113',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
    = ( k3_tarski @ ( k2_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['107','112'])).

thf('114',plain,(
    ( k3_tarski @ ( k2_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) )
 != sk_A ),
    inference(demod,[status(thm)],['99','113'])).

thf('115',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['96','114'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gbq1qbKvXD
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:03:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.78/0.97  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.78/0.97  % Solved by: fo/fo7.sh
% 0.78/0.97  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.78/0.97  % done 1069 iterations in 0.523s
% 0.78/0.97  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.78/0.97  % SZS output start Refutation
% 0.78/0.97  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.78/0.97  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.78/0.97  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.78/0.97  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.78/0.97  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.78/0.97  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.78/0.97  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.78/0.97  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.78/0.97  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.78/0.97  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.78/0.97  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.78/0.97  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.78/0.97  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.78/0.97  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.78/0.97  thf(sk_A_type, type, sk_A: $i).
% 0.78/0.97  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.78/0.97  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.78/0.97  thf(t25_subset_1, conjecture,
% 0.78/0.97    (![A:$i,B:$i]:
% 0.78/0.97     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.78/0.97       ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) ) =
% 0.78/0.97         ( k2_subset_1 @ A ) ) ))).
% 0.78/0.97  thf(zf_stmt_0, negated_conjecture,
% 0.78/0.97    (~( ![A:$i,B:$i]:
% 0.78/0.97        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.78/0.97          ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) ) =
% 0.78/0.97            ( k2_subset_1 @ A ) ) ) )),
% 0.78/0.97    inference('cnf.neg', [status(esa)], [t25_subset_1])).
% 0.78/0.97  thf('0', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.78/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.97  thf(d5_subset_1, axiom,
% 0.78/0.97    (![A:$i,B:$i]:
% 0.78/0.97     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.78/0.97       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.78/0.97  thf('1', plain,
% 0.78/0.97      (![X64 : $i, X65 : $i]:
% 0.78/0.97         (((k3_subset_1 @ X64 @ X65) = (k4_xboole_0 @ X64 @ X65))
% 0.78/0.97          | ~ (m1_subset_1 @ X65 @ (k1_zfmisc_1 @ X64)))),
% 0.78/0.97      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.78/0.97  thf('2', plain,
% 0.78/0.97      (((k3_subset_1 @ sk_A @ sk_B_1) = (k4_xboole_0 @ sk_A @ sk_B_1))),
% 0.78/0.97      inference('sup-', [status(thm)], ['0', '1'])).
% 0.78/0.97  thf(t48_xboole_1, axiom,
% 0.78/0.97    (![A:$i,B:$i]:
% 0.78/0.97     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.78/0.97  thf('3', plain,
% 0.78/0.97      (![X18 : $i, X19 : $i]:
% 0.78/0.97         ((k4_xboole_0 @ X18 @ (k4_xboole_0 @ X18 @ X19))
% 0.78/0.97           = (k3_xboole_0 @ X18 @ X19))),
% 0.78/0.97      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.78/0.97  thf('4', plain,
% 0.78/0.97      (((k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B_1))
% 0.78/0.97         = (k3_xboole_0 @ sk_A @ sk_B_1))),
% 0.78/0.97      inference('sup+', [status(thm)], ['2', '3'])).
% 0.78/0.97  thf(commutativity_k3_xboole_0, axiom,
% 0.78/0.97    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.78/0.97  thf('5', plain,
% 0.78/0.97      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.78/0.97      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.78/0.97  thf('6', plain,
% 0.78/0.97      (((k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B_1))
% 0.78/0.97         = (k3_xboole_0 @ sk_B_1 @ sk_A))),
% 0.78/0.97      inference('demod', [status(thm)], ['4', '5'])).
% 0.78/0.97  thf(t36_xboole_1, axiom,
% 0.78/0.97    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.78/0.97  thf('7', plain,
% 0.78/0.97      (![X16 : $i, X17 : $i]: (r1_tarski @ (k4_xboole_0 @ X16 @ X17) @ X16)),
% 0.78/0.97      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.78/0.97  thf('8', plain, ((r1_tarski @ (k3_xboole_0 @ sk_B_1 @ sk_A) @ sk_A)),
% 0.78/0.97      inference('sup+', [status(thm)], ['6', '7'])).
% 0.78/0.97  thf(t28_xboole_1, axiom,
% 0.78/0.97    (![A:$i,B:$i]:
% 0.78/0.97     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.78/0.97  thf('9', plain,
% 0.78/0.97      (![X13 : $i, X14 : $i]:
% 0.78/0.97         (((k3_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_tarski @ X13 @ X14))),
% 0.78/0.97      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.78/0.97  thf('10', plain,
% 0.78/0.97      (((k3_xboole_0 @ (k3_xboole_0 @ sk_B_1 @ sk_A) @ sk_A)
% 0.78/0.97         = (k3_xboole_0 @ sk_B_1 @ sk_A))),
% 0.78/0.97      inference('sup-', [status(thm)], ['8', '9'])).
% 0.78/0.97  thf('11', plain,
% 0.78/0.97      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.78/0.97      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.78/0.97  thf('12', plain,
% 0.78/0.97      (((k3_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B_1 @ sk_A))
% 0.78/0.97         = (k3_xboole_0 @ sk_B_1 @ sk_A))),
% 0.78/0.97      inference('demod', [status(thm)], ['10', '11'])).
% 0.78/0.97  thf(t100_xboole_1, axiom,
% 0.78/0.97    (![A:$i,B:$i]:
% 0.78/0.97     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.78/0.97  thf('13', plain,
% 0.78/0.97      (![X8 : $i, X9 : $i]:
% 0.78/0.97         ((k4_xboole_0 @ X8 @ X9)
% 0.78/0.97           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.78/0.97      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.78/0.97  thf('14', plain,
% 0.78/0.97      (((k4_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B_1 @ sk_A))
% 0.78/0.97         = (k5_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B_1 @ sk_A)))),
% 0.78/0.97      inference('sup+', [status(thm)], ['12', '13'])).
% 0.78/0.97  thf('15', plain,
% 0.78/0.97      (((k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B_1))
% 0.78/0.97         = (k3_xboole_0 @ sk_B_1 @ sk_A))),
% 0.78/0.97      inference('demod', [status(thm)], ['4', '5'])).
% 0.78/0.97  thf('16', plain,
% 0.78/0.97      (![X18 : $i, X19 : $i]:
% 0.78/0.97         ((k4_xboole_0 @ X18 @ (k4_xboole_0 @ X18 @ X19))
% 0.78/0.97           = (k3_xboole_0 @ X18 @ X19))),
% 0.78/0.98      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.78/0.98  thf('17', plain,
% 0.78/0.98      (((k4_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B_1 @ sk_A))
% 0.78/0.98         = (k3_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B_1)))),
% 0.78/0.98      inference('sup+', [status(thm)], ['15', '16'])).
% 0.78/0.98  thf('18', plain,
% 0.78/0.98      (((k3_subset_1 @ sk_A @ sk_B_1) = (k4_xboole_0 @ sk_A @ sk_B_1))),
% 0.78/0.98      inference('sup-', [status(thm)], ['0', '1'])).
% 0.78/0.98  thf('19', plain,
% 0.78/0.98      (![X16 : $i, X17 : $i]: (r1_tarski @ (k4_xboole_0 @ X16 @ X17) @ X16)),
% 0.78/0.98      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.78/0.98  thf('20', plain, ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B_1) @ sk_A)),
% 0.78/0.98      inference('sup+', [status(thm)], ['18', '19'])).
% 0.78/0.98  thf('21', plain,
% 0.78/0.98      (![X13 : $i, X14 : $i]:
% 0.78/0.98         (((k3_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_tarski @ X13 @ X14))),
% 0.78/0.98      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.78/0.98  thf('22', plain,
% 0.78/0.98      (((k3_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B_1) @ sk_A)
% 0.78/0.98         = (k3_subset_1 @ sk_A @ sk_B_1))),
% 0.78/0.98      inference('sup-', [status(thm)], ['20', '21'])).
% 0.78/0.98  thf('23', plain,
% 0.78/0.98      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.78/0.98      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.78/0.98  thf('24', plain,
% 0.78/0.98      (((k3_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B_1))
% 0.78/0.98         = (k3_subset_1 @ sk_A @ sk_B_1))),
% 0.78/0.98      inference('demod', [status(thm)], ['22', '23'])).
% 0.78/0.98  thf('25', plain,
% 0.78/0.98      (((k4_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B_1 @ sk_A))
% 0.78/0.98         = (k3_subset_1 @ sk_A @ sk_B_1))),
% 0.78/0.98      inference('demod', [status(thm)], ['17', '24'])).
% 0.78/0.98  thf('26', plain,
% 0.78/0.98      (((k3_subset_1 @ sk_A @ sk_B_1)
% 0.78/0.98         = (k5_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B_1 @ sk_A)))),
% 0.78/0.98      inference('demod', [status(thm)], ['14', '25'])).
% 0.78/0.98  thf('27', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.78/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.98  thf(d2_subset_1, axiom,
% 0.78/0.98    (![A:$i,B:$i]:
% 0.78/0.98     ( ( ( v1_xboole_0 @ A ) =>
% 0.78/0.98         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.78/0.98       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.78/0.98         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.78/0.98  thf('28', plain,
% 0.78/0.98      (![X60 : $i, X61 : $i]:
% 0.78/0.98         (~ (m1_subset_1 @ X60 @ X61)
% 0.78/0.98          | (r2_hidden @ X60 @ X61)
% 0.78/0.98          | (v1_xboole_0 @ X61))),
% 0.78/0.98      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.78/0.98  thf('29', plain,
% 0.78/0.98      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.78/0.98        | (r2_hidden @ sk_B_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.78/0.98      inference('sup-', [status(thm)], ['27', '28'])).
% 0.78/0.98  thf(fc1_subset_1, axiom,
% 0.78/0.98    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.78/0.98  thf('30', plain, (![X66 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X66))),
% 0.78/0.98      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.78/0.98  thf('31', plain, ((r2_hidden @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.78/0.98      inference('clc', [status(thm)], ['29', '30'])).
% 0.78/0.98  thf(d1_zfmisc_1, axiom,
% 0.78/0.98    (![A:$i,B:$i]:
% 0.78/0.98     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.78/0.98       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.78/0.98  thf('32', plain,
% 0.78/0.98      (![X54 : $i, X55 : $i, X56 : $i]:
% 0.78/0.98         (~ (r2_hidden @ X56 @ X55)
% 0.78/0.98          | (r1_tarski @ X56 @ X54)
% 0.78/0.98          | ((X55) != (k1_zfmisc_1 @ X54)))),
% 0.78/0.98      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.78/0.98  thf('33', plain,
% 0.78/0.98      (![X54 : $i, X56 : $i]:
% 0.78/0.98         ((r1_tarski @ X56 @ X54) | ~ (r2_hidden @ X56 @ (k1_zfmisc_1 @ X54)))),
% 0.78/0.98      inference('simplify', [status(thm)], ['32'])).
% 0.78/0.98  thf('34', plain, ((r1_tarski @ sk_B_1 @ sk_A)),
% 0.78/0.98      inference('sup-', [status(thm)], ['31', '33'])).
% 0.78/0.98  thf('35', plain,
% 0.78/0.98      (![X13 : $i, X14 : $i]:
% 0.78/0.98         (((k3_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_tarski @ X13 @ X14))),
% 0.78/0.98      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.78/0.98  thf('36', plain, (((k3_xboole_0 @ sk_B_1 @ sk_A) = (sk_B_1))),
% 0.78/0.98      inference('sup-', [status(thm)], ['34', '35'])).
% 0.78/0.98  thf(commutativity_k5_xboole_0, axiom,
% 0.78/0.98    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.78/0.98  thf('37', plain,
% 0.78/0.98      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.78/0.98      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.78/0.98  thf('38', plain,
% 0.78/0.98      (((k3_subset_1 @ sk_A @ sk_B_1) = (k5_xboole_0 @ sk_B_1 @ sk_A))),
% 0.78/0.98      inference('demod', [status(thm)], ['26', '36', '37'])).
% 0.78/0.98  thf(idempotence_k3_xboole_0, axiom,
% 0.78/0.98    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.78/0.98  thf('39', plain, (![X7 : $i]: ((k3_xboole_0 @ X7 @ X7) = (X7))),
% 0.78/0.98      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.78/0.98  thf('40', plain,
% 0.78/0.98      (![X8 : $i, X9 : $i]:
% 0.78/0.98         ((k4_xboole_0 @ X8 @ X9)
% 0.78/0.98           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.78/0.98      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.78/0.98  thf('41', plain,
% 0.78/0.98      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.78/0.98      inference('sup+', [status(thm)], ['39', '40'])).
% 0.78/0.98  thf(t2_boole, axiom,
% 0.78/0.98    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.78/0.98  thf('42', plain,
% 0.78/0.98      (![X15 : $i]: ((k3_xboole_0 @ X15 @ k1_xboole_0) = (k1_xboole_0))),
% 0.78/0.98      inference('cnf', [status(esa)], [t2_boole])).
% 0.78/0.98  thf('43', plain,
% 0.78/0.98      (![X8 : $i, X9 : $i]:
% 0.78/0.98         ((k4_xboole_0 @ X8 @ X9)
% 0.78/0.98           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.78/0.98      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.78/0.98  thf('44', plain,
% 0.78/0.98      (![X0 : $i]:
% 0.78/0.98         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.78/0.98      inference('sup+', [status(thm)], ['42', '43'])).
% 0.78/0.98  thf(t5_boole, axiom,
% 0.78/0.98    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.78/0.98  thf('45', plain, (![X20 : $i]: ((k5_xboole_0 @ X20 @ k1_xboole_0) = (X20))),
% 0.78/0.98      inference('cnf', [status(esa)], [t5_boole])).
% 0.78/0.98  thf('46', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.78/0.98      inference('sup+', [status(thm)], ['44', '45'])).
% 0.78/0.98  thf('47', plain,
% 0.78/0.98      (![X18 : $i, X19 : $i]:
% 0.78/0.98         ((k4_xboole_0 @ X18 @ (k4_xboole_0 @ X18 @ X19))
% 0.78/0.98           = (k3_xboole_0 @ X18 @ X19))),
% 0.78/0.98      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.78/0.98  thf('48', plain,
% 0.78/0.98      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.78/0.98      inference('sup+', [status(thm)], ['46', '47'])).
% 0.78/0.98  thf('49', plain,
% 0.78/0.98      (![X15 : $i]: ((k3_xboole_0 @ X15 @ k1_xboole_0) = (k1_xboole_0))),
% 0.78/0.98      inference('cnf', [status(esa)], [t2_boole])).
% 0.78/0.98  thf('50', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.78/0.98      inference('demod', [status(thm)], ['48', '49'])).
% 0.78/0.98  thf('51', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 0.78/0.98      inference('demod', [status(thm)], ['41', '50'])).
% 0.78/0.98  thf(t91_xboole_1, axiom,
% 0.78/0.98    (![A:$i,B:$i,C:$i]:
% 0.78/0.98     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.78/0.98       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.78/0.98  thf('52', plain,
% 0.78/0.98      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.78/0.98         ((k5_xboole_0 @ (k5_xboole_0 @ X21 @ X22) @ X23)
% 0.78/0.98           = (k5_xboole_0 @ X21 @ (k5_xboole_0 @ X22 @ X23)))),
% 0.78/0.98      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.78/0.98  thf('53', plain,
% 0.78/0.98      (![X0 : $i, X1 : $i]:
% 0.78/0.98         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.78/0.98           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.78/0.98      inference('sup+', [status(thm)], ['51', '52'])).
% 0.78/0.98  thf('54', plain,
% 0.78/0.98      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.78/0.98      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.78/0.98  thf('55', plain, (![X20 : $i]: ((k5_xboole_0 @ X20 @ k1_xboole_0) = (X20))),
% 0.78/0.98      inference('cnf', [status(esa)], [t5_boole])).
% 0.78/0.98  thf('56', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.78/0.98      inference('sup+', [status(thm)], ['54', '55'])).
% 0.78/0.98  thf('57', plain,
% 0.78/0.98      (![X0 : $i, X1 : $i]:
% 0.78/0.98         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.78/0.98      inference('demod', [status(thm)], ['53', '56'])).
% 0.78/0.98  thf('58', plain,
% 0.78/0.98      (((sk_A) = (k5_xboole_0 @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))),
% 0.78/0.98      inference('sup+', [status(thm)], ['38', '57'])).
% 0.78/0.98  thf('59', plain,
% 0.78/0.98      (((k3_subset_1 @ sk_A @ sk_B_1) = (k4_xboole_0 @ sk_A @ sk_B_1))),
% 0.78/0.98      inference('sup-', [status(thm)], ['0', '1'])).
% 0.78/0.98  thf('60', plain,
% 0.78/0.98      (![X8 : $i, X9 : $i]:
% 0.78/0.98         ((k4_xboole_0 @ X8 @ X9)
% 0.78/0.98           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.78/0.98      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.78/0.98  thf('61', plain,
% 0.78/0.98      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.78/0.98      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.78/0.98  thf(t112_xboole_1, axiom,
% 0.78/0.98    (![A:$i,B:$i,C:$i]:
% 0.78/0.98     ( ( k5_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ B ) ) =
% 0.78/0.98       ( k3_xboole_0 @ ( k5_xboole_0 @ A @ C ) @ B ) ))).
% 0.78/0.98  thf('62', plain,
% 0.78/0.98      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.78/0.98         ((k5_xboole_0 @ (k3_xboole_0 @ X10 @ X12) @ (k3_xboole_0 @ X11 @ X12))
% 0.78/0.98           = (k3_xboole_0 @ (k5_xboole_0 @ X10 @ X11) @ X12))),
% 0.78/0.98      inference('cnf', [status(esa)], [t112_xboole_1])).
% 0.78/0.98  thf('63', plain,
% 0.78/0.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.78/0.98         ((k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X2 @ X1))
% 0.78/0.98           = (k3_xboole_0 @ (k5_xboole_0 @ X0 @ X2) @ X1))),
% 0.78/0.98      inference('sup+', [status(thm)], ['61', '62'])).
% 0.78/0.98  thf('64', plain,
% 0.78/0.98      (![X0 : $i, X1 : $i]:
% 0.78/0.98         ((k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0)
% 0.78/0.98           = (k3_xboole_0 @ (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X1)) @ X0))),
% 0.78/0.98      inference('sup+', [status(thm)], ['60', '63'])).
% 0.78/0.98  thf('65', plain,
% 0.78/0.98      (![X18 : $i, X19 : $i]:
% 0.78/0.98         ((k4_xboole_0 @ X18 @ (k4_xboole_0 @ X18 @ X19))
% 0.78/0.98           = (k3_xboole_0 @ X18 @ X19))),
% 0.78/0.98      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.78/0.98  thf('66', plain,
% 0.78/0.98      (![X16 : $i, X17 : $i]: (r1_tarski @ (k4_xboole_0 @ X16 @ X17) @ X16)),
% 0.78/0.98      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.78/0.98  thf('67', plain,
% 0.78/0.98      (![X13 : $i, X14 : $i]:
% 0.78/0.98         (((k3_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_tarski @ X13 @ X14))),
% 0.78/0.98      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.78/0.98  thf('68', plain,
% 0.78/0.98      (![X0 : $i, X1 : $i]:
% 0.78/0.98         ((k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0)
% 0.78/0.98           = (k4_xboole_0 @ X0 @ X1))),
% 0.78/0.98      inference('sup-', [status(thm)], ['66', '67'])).
% 0.78/0.98  thf('69', plain,
% 0.78/0.98      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.78/0.98      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.78/0.98  thf('70', plain,
% 0.78/0.98      (![X0 : $i, X1 : $i]:
% 0.78/0.98         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.78/0.98           = (k4_xboole_0 @ X0 @ X1))),
% 0.78/0.98      inference('demod', [status(thm)], ['68', '69'])).
% 0.78/0.98  thf('71', plain,
% 0.78/0.98      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.78/0.98      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.78/0.98  thf('72', plain,
% 0.78/0.98      (![X8 : $i, X9 : $i]:
% 0.78/0.98         ((k4_xboole_0 @ X8 @ X9)
% 0.78/0.98           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.78/0.98      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.78/0.98  thf('73', plain,
% 0.78/0.98      (![X0 : $i, X1 : $i]:
% 0.78/0.98         ((k4_xboole_0 @ X0 @ X1)
% 0.78/0.98           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.78/0.98      inference('sup+', [status(thm)], ['71', '72'])).
% 0.78/0.98  thf('74', plain,
% 0.78/0.98      (![X0 : $i, X1 : $i]:
% 0.78/0.98         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1)
% 0.78/0.98           = (k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0)))),
% 0.78/0.98      inference('sup+', [status(thm)], ['70', '73'])).
% 0.78/0.98  thf('75', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 0.78/0.98      inference('demod', [status(thm)], ['41', '50'])).
% 0.78/0.98  thf('76', plain,
% 0.78/0.98      (![X0 : $i, X1 : $i]:
% 0.78/0.98         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1) = (k1_xboole_0))),
% 0.78/0.98      inference('demod', [status(thm)], ['74', '75'])).
% 0.78/0.98  thf('77', plain,
% 0.78/0.98      (![X0 : $i, X1 : $i]:
% 0.78/0.98         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1) = (k1_xboole_0))),
% 0.78/0.98      inference('sup+', [status(thm)], ['65', '76'])).
% 0.78/0.98  thf('78', plain,
% 0.78/0.98      (![X0 : $i, X1 : $i]:
% 0.78/0.98         ((k4_xboole_0 @ X0 @ X1)
% 0.78/0.98           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.78/0.98      inference('sup+', [status(thm)], ['71', '72'])).
% 0.78/0.98  thf('79', plain,
% 0.78/0.98      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.78/0.98      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.78/0.98  thf('80', plain,
% 0.78/0.98      (![X0 : $i, X1 : $i]:
% 0.78/0.98         ((k1_xboole_0) = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.78/0.98      inference('demod', [status(thm)], ['64', '77', '78', '79'])).
% 0.78/0.98  thf('81', plain,
% 0.78/0.98      (((k1_xboole_0) = (k3_xboole_0 @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))),
% 0.78/0.98      inference('sup+', [status(thm)], ['59', '80'])).
% 0.78/0.98  thf('82', plain,
% 0.78/0.98      (![X0 : $i, X1 : $i]:
% 0.78/0.98         ((k4_xboole_0 @ X0 @ X1)
% 0.78/0.98           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.78/0.98      inference('sup+', [status(thm)], ['71', '72'])).
% 0.78/0.98  thf('83', plain,
% 0.78/0.98      (((k4_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B_1) @ sk_B_1)
% 0.78/0.98         = (k5_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B_1) @ k1_xboole_0))),
% 0.78/0.98      inference('sup+', [status(thm)], ['81', '82'])).
% 0.78/0.98  thf('84', plain,
% 0.78/0.98      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.78/0.98      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.78/0.98  thf('85', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.78/0.98      inference('sup+', [status(thm)], ['54', '55'])).
% 0.78/0.98  thf('86', plain,
% 0.78/0.98      (((k4_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B_1) @ sk_B_1)
% 0.78/0.98         = (k3_subset_1 @ sk_A @ sk_B_1))),
% 0.78/0.98      inference('demod', [status(thm)], ['83', '84', '85'])).
% 0.78/0.98  thf('87', plain,
% 0.78/0.98      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.78/0.98      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.78/0.98  thf(t94_xboole_1, axiom,
% 0.78/0.98    (![A:$i,B:$i]:
% 0.78/0.98     ( ( k2_xboole_0 @ A @ B ) =
% 0.78/0.98       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.78/0.98  thf('88', plain,
% 0.78/0.98      (![X24 : $i, X25 : $i]:
% 0.78/0.98         ((k2_xboole_0 @ X24 @ X25)
% 0.78/0.98           = (k5_xboole_0 @ (k5_xboole_0 @ X24 @ X25) @ 
% 0.78/0.98              (k3_xboole_0 @ X24 @ X25)))),
% 0.78/0.98      inference('cnf', [status(esa)], [t94_xboole_1])).
% 0.78/0.98  thf(l51_zfmisc_1, axiom,
% 0.78/0.98    (![A:$i,B:$i]:
% 0.78/0.98     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.78/0.98  thf('89', plain,
% 0.78/0.98      (![X58 : $i, X59 : $i]:
% 0.78/0.98         ((k3_tarski @ (k2_tarski @ X58 @ X59)) = (k2_xboole_0 @ X58 @ X59))),
% 0.78/0.98      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.78/0.98  thf('90', plain,
% 0.78/0.98      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.78/0.98         ((k5_xboole_0 @ (k5_xboole_0 @ X21 @ X22) @ X23)
% 0.78/0.98           = (k5_xboole_0 @ X21 @ (k5_xboole_0 @ X22 @ X23)))),
% 0.78/0.98      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.78/0.98  thf('91', plain,
% 0.78/0.98      (![X24 : $i, X25 : $i]:
% 0.78/0.98         ((k3_tarski @ (k2_tarski @ X24 @ X25))
% 0.78/0.98           = (k5_xboole_0 @ X24 @ 
% 0.78/0.98              (k5_xboole_0 @ X25 @ (k3_xboole_0 @ X24 @ X25))))),
% 0.78/0.98      inference('demod', [status(thm)], ['88', '89', '90'])).
% 0.78/0.98  thf('92', plain,
% 0.78/0.98      (![X0 : $i, X1 : $i]:
% 0.78/0.98         ((k3_tarski @ (k2_tarski @ X0 @ X1))
% 0.78/0.98           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))))),
% 0.78/0.98      inference('sup+', [status(thm)], ['87', '91'])).
% 0.78/0.98  thf('93', plain,
% 0.78/0.98      (![X8 : $i, X9 : $i]:
% 0.78/0.98         ((k4_xboole_0 @ X8 @ X9)
% 0.78/0.98           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.78/0.98      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.78/0.98  thf('94', plain,
% 0.78/0.98      (![X0 : $i, X1 : $i]:
% 0.78/0.98         ((k3_tarski @ (k2_tarski @ X0 @ X1))
% 0.78/0.98           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.78/0.98      inference('demod', [status(thm)], ['92', '93'])).
% 0.78/0.98  thf('95', plain,
% 0.78/0.98      (((k3_tarski @ (k2_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))
% 0.78/0.98         = (k5_xboole_0 @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))),
% 0.78/0.98      inference('sup+', [status(thm)], ['86', '94'])).
% 0.78/0.98  thf('96', plain,
% 0.78/0.98      (((k3_tarski @ (k2_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))
% 0.78/0.98         = (sk_A))),
% 0.78/0.98      inference('sup+', [status(thm)], ['58', '95'])).
% 0.78/0.98  thf('97', plain,
% 0.78/0.98      (((k4_subset_1 @ sk_A @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))
% 0.78/0.98         != (k2_subset_1 @ sk_A))),
% 0.78/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.98  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.78/0.98  thf('98', plain, (![X63 : $i]: ((k2_subset_1 @ X63) = (X63))),
% 0.78/0.98      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.78/0.98  thf('99', plain,
% 0.78/0.98      (((k4_subset_1 @ sk_A @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)) != (sk_A))),
% 0.78/0.98      inference('demod', [status(thm)], ['97', '98'])).
% 0.78/0.98  thf('100', plain, ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B_1) @ sk_A)),
% 0.78/0.98      inference('sup+', [status(thm)], ['18', '19'])).
% 0.78/0.98  thf('101', plain,
% 0.78/0.98      (![X53 : $i, X54 : $i, X55 : $i]:
% 0.78/0.98         (~ (r1_tarski @ X53 @ X54)
% 0.78/0.98          | (r2_hidden @ X53 @ X55)
% 0.78/0.98          | ((X55) != (k1_zfmisc_1 @ X54)))),
% 0.78/0.98      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.78/0.98  thf('102', plain,
% 0.78/0.98      (![X53 : $i, X54 : $i]:
% 0.78/0.98         ((r2_hidden @ X53 @ (k1_zfmisc_1 @ X54)) | ~ (r1_tarski @ X53 @ X54))),
% 0.78/0.98      inference('simplify', [status(thm)], ['101'])).
% 0.78/0.98  thf('103', plain,
% 0.78/0.98      ((r2_hidden @ (k3_subset_1 @ sk_A @ sk_B_1) @ (k1_zfmisc_1 @ sk_A))),
% 0.78/0.98      inference('sup-', [status(thm)], ['100', '102'])).
% 0.78/0.98  thf('104', plain,
% 0.78/0.98      (![X60 : $i, X61 : $i]:
% 0.78/0.98         (~ (r2_hidden @ X60 @ X61)
% 0.78/0.98          | (m1_subset_1 @ X60 @ X61)
% 0.78/0.98          | (v1_xboole_0 @ X61))),
% 0.78/0.98      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.78/0.98  thf(d1_xboole_0, axiom,
% 0.78/0.98    (![A:$i]:
% 0.78/0.98     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.78/0.98  thf('105', plain,
% 0.78/0.98      (![X4 : $i, X5 : $i]: (~ (r2_hidden @ X4 @ X5) | ~ (v1_xboole_0 @ X5))),
% 0.78/0.98      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.78/0.98  thf('106', plain,
% 0.78/0.98      (![X60 : $i, X61 : $i]:
% 0.78/0.98         ((m1_subset_1 @ X60 @ X61) | ~ (r2_hidden @ X60 @ X61))),
% 0.78/0.98      inference('clc', [status(thm)], ['104', '105'])).
% 0.78/0.98  thf('107', plain,
% 0.78/0.98      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_B_1) @ (k1_zfmisc_1 @ sk_A))),
% 0.78/0.98      inference('sup-', [status(thm)], ['103', '106'])).
% 0.78/0.98  thf('108', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.78/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.98  thf(redefinition_k4_subset_1, axiom,
% 0.78/0.98    (![A:$i,B:$i,C:$i]:
% 0.78/0.98     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.78/0.98         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.78/0.98       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.78/0.98  thf('109', plain,
% 0.78/0.98      (![X67 : $i, X68 : $i, X69 : $i]:
% 0.78/0.98         (~ (m1_subset_1 @ X67 @ (k1_zfmisc_1 @ X68))
% 0.78/0.98          | ~ (m1_subset_1 @ X69 @ (k1_zfmisc_1 @ X68))
% 0.78/0.98          | ((k4_subset_1 @ X68 @ X67 @ X69) = (k2_xboole_0 @ X67 @ X69)))),
% 0.78/0.98      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.78/0.98  thf('110', plain,
% 0.78/0.98      (![X58 : $i, X59 : $i]:
% 0.78/0.98         ((k3_tarski @ (k2_tarski @ X58 @ X59)) = (k2_xboole_0 @ X58 @ X59))),
% 0.78/0.98      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.78/0.98  thf('111', plain,
% 0.78/0.98      (![X67 : $i, X68 : $i, X69 : $i]:
% 0.78/0.98         (~ (m1_subset_1 @ X67 @ (k1_zfmisc_1 @ X68))
% 0.78/0.98          | ~ (m1_subset_1 @ X69 @ (k1_zfmisc_1 @ X68))
% 0.78/0.98          | ((k4_subset_1 @ X68 @ X67 @ X69)
% 0.78/0.98              = (k3_tarski @ (k2_tarski @ X67 @ X69))))),
% 0.78/0.98      inference('demod', [status(thm)], ['109', '110'])).
% 0.78/0.98  thf('112', plain,
% 0.78/0.98      (![X0 : $i]:
% 0.78/0.98         (((k4_subset_1 @ sk_A @ sk_B_1 @ X0)
% 0.78/0.98            = (k3_tarski @ (k2_tarski @ sk_B_1 @ X0)))
% 0.78/0.98          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 0.78/0.98      inference('sup-', [status(thm)], ['108', '111'])).
% 0.78/0.98  thf('113', plain,
% 0.78/0.98      (((k4_subset_1 @ sk_A @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))
% 0.78/0.98         = (k3_tarski @ (k2_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))))),
% 0.78/0.98      inference('sup-', [status(thm)], ['107', '112'])).
% 0.78/0.98  thf('114', plain,
% 0.78/0.98      (((k3_tarski @ (k2_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))
% 0.78/0.98         != (sk_A))),
% 0.78/0.98      inference('demod', [status(thm)], ['99', '113'])).
% 0.78/0.98  thf('115', plain, ($false),
% 0.78/0.98      inference('simplify_reflect-', [status(thm)], ['96', '114'])).
% 0.78/0.98  
% 0.78/0.98  % SZS output end Refutation
% 0.78/0.98  
% 0.78/0.98  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
