%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.kq3RBWViNH

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:50 EST 2020

% Result     : Theorem 0.50s
% Output     : Refutation 0.50s
% Verified   : 
% Statistics : Number of formulae       :  158 ( 957 expanded)
%              Number of leaves         :   33 ( 325 expanded)
%              Depth                    :   22
%              Number of atoms          : 1116 (6798 expanded)
%              Number of equality atoms :  119 ( 882 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

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

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X39: $i,X40: $i] :
      ( ( ( k3_subset_1 @ X39 @ X40 )
        = ( k4_xboole_0 @ X39 @ X40 ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('2',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('3',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ X18 @ X19 )
      = ( k5_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('4',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = ( k5_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
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

thf('6',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X35 @ X36 )
      | ( r2_hidden @ X35 @ X36 )
      | ( v1_xboole_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('7',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('8',plain,(
    ! [X43: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('9',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['7','8'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('10',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( r2_hidden @ X28 @ X27 )
      | ( r1_tarski @ X28 @ X26 )
      | ( X27
       != ( k1_zfmisc_1 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('11',plain,(
    ! [X26: $i,X28: $i] :
      ( ( r1_tarski @ X28 @ X26 )
      | ~ ( r2_hidden @ X28 @ ( k1_zfmisc_1 @ X26 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['9','11'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('13',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('14',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['12','13'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('16',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['14','17'])).

thf('19',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('20',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['18','19'])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('21',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X15 @ X16 ) @ X17 )
      = ( k5_xboole_0 @ X15 @ ( k5_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('22',plain,(
    ! [X2: $i] :
      ( ( k3_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('23',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X2: $i] :
      ( ( k3_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = A ) )).

thf('26',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k2_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) )
      = X8 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('28',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k2_xboole_0 @ X12 @ X13 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['24','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['21','30'])).

thf('32',plain,
    ( k1_xboole_0
    = ( k5_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['20','31'])).

thf('33',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = ( k5_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('34',plain,
    ( k1_xboole_0
    = ( k5_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['24','29'])).

thf('36',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X15 @ X16 ) @ X17 )
      = ( k5_xboole_0 @ X15 @ ( k5_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['24','29'])).

thf(t112_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ B ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ A @ C ) @ B ) ) )).

thf('39',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X5 @ X7 ) @ ( k3_xboole_0 @ X6 @ X7 ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X5 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t112_xboole_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X1 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['24','29'])).

thf('42',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

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
    ! [X14: $i] :
      ( ( k5_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ X18 @ X19 )
      = ( k5_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['37','48'])).

thf('50',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_A ) )
    = ( k5_xboole_0 @ sk_A @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['34','49'])).

thf('51',plain,(
    ! [X14: $i] :
      ( ( k5_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('52',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_A ) )
    = sk_A ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['24','29'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['37','48'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X14: $i] :
      ( ( k5_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = sk_A ),
    inference(demod,[status(thm)],['52','57'])).

thf('59',plain,
    ( sk_A
    = ( k5_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','58'])).

thf('60',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('61',plain,(
    ! [X41: $i,X42: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X41 @ X42 ) @ ( k1_zfmisc_1 @ X41 ) )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('62',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X35 @ X36 )
      | ( r2_hidden @ X35 @ X36 )
      | ( v1_xboole_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('64',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X43: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('66',plain,(
    r2_hidden @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X26: $i,X28: $i] :
      ( ( r1_tarski @ X28 @ X26 )
      | ~ ( r2_hidden @ X28 @ ( k1_zfmisc_1 @ X26 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('68',plain,(
    r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_A ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('70',plain,
    ( ( k3_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_A )
    = ( k3_subset_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('72',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k3_subset_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('74',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X5 @ X7 ) @ ( k3_xboole_0 @ X6 @ X7 ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X5 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t112_xboole_1])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['75','76','77'])).

thf('79',plain,
    ( ( k4_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k3_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['72','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('81',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('82',plain,(
    ! [X39: $i,X40: $i] :
      ( ( ( k3_subset_1 @ X39 @ X40 )
        = ( k4_xboole_0 @ X39 @ X40 ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('83',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['37','48'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,
    ( sk_B
    = ( k5_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['84','87'])).

thf('89',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k3_subset_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('90',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('91',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k5_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['89','90'])).

thf('92',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('93',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k5_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference('sup+',[status(thm)],['88','93'])).

thf('95',plain,
    ( sk_B
    = ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['83','94'])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('97',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['79','80','95','96'])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('99',plain,
    ( ( k4_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
    = ( k5_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['21','30'])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X14: $i] :
      ( ( k5_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('109',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('110',plain,
    ( ( k4_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
    = ( k3_subset_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['99','106','109'])).

thf('111',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ X18 @ X19 )
      = ( k5_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('112',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k5_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['110','111'])).

thf('113',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = sk_A ),
    inference('sup+',[status(thm)],['59','112'])).

thf('114',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
 != ( k2_subset_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('115',plain,(
    ! [X38: $i] :
      ( ( k2_subset_1 @ X38 )
      = X38 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('116',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
 != sk_A ),
    inference(demod,[status(thm)],['114','115'])).

thf('117',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('118',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('119',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ X45 ) )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ X45 ) )
      | ( ( k4_subset_1 @ X45 @ X44 @ X46 )
        = ( k2_xboole_0 @ X44 @ X46 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('120',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ sk_A @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['117','120'])).

thf('122',plain,(
    ( k2_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
 != sk_A ),
    inference(demod,[status(thm)],['116','121'])).

thf('123',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['113','122'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.kq3RBWViNH
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:52:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.50/0.68  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.50/0.68  % Solved by: fo/fo7.sh
% 0.50/0.68  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.50/0.68  % done 344 iterations in 0.183s
% 0.50/0.68  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.50/0.68  % SZS output start Refutation
% 0.50/0.68  thf(sk_A_type, type, sk_A: $i).
% 0.50/0.68  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.50/0.68  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.50/0.68  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.50/0.68  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.50/0.68  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.50/0.68  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.50/0.68  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.50/0.68  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.50/0.68  thf(sk_B_type, type, sk_B: $i).
% 0.50/0.68  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.50/0.68  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.50/0.68  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.50/0.68  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.50/0.68  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.50/0.68  thf(t25_subset_1, conjecture,
% 0.50/0.68    (![A:$i,B:$i]:
% 0.50/0.68     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.50/0.68       ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) ) =
% 0.50/0.68         ( k2_subset_1 @ A ) ) ))).
% 0.50/0.68  thf(zf_stmt_0, negated_conjecture,
% 0.50/0.68    (~( ![A:$i,B:$i]:
% 0.50/0.68        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.50/0.68          ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) ) =
% 0.50/0.68            ( k2_subset_1 @ A ) ) ) )),
% 0.50/0.68    inference('cnf.neg', [status(esa)], [t25_subset_1])).
% 0.50/0.68  thf('0', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.50/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.68  thf(d5_subset_1, axiom,
% 0.50/0.68    (![A:$i,B:$i]:
% 0.50/0.68     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.50/0.68       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.50/0.68  thf('1', plain,
% 0.50/0.68      (![X39 : $i, X40 : $i]:
% 0.50/0.68         (((k3_subset_1 @ X39 @ X40) = (k4_xboole_0 @ X39 @ X40))
% 0.50/0.68          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ X39)))),
% 0.50/0.68      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.50/0.68  thf('2', plain,
% 0.50/0.68      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.50/0.68      inference('sup-', [status(thm)], ['0', '1'])).
% 0.50/0.68  thf(t98_xboole_1, axiom,
% 0.50/0.68    (![A:$i,B:$i]:
% 0.50/0.68     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.50/0.68  thf('3', plain,
% 0.50/0.68      (![X18 : $i, X19 : $i]:
% 0.50/0.68         ((k2_xboole_0 @ X18 @ X19)
% 0.50/0.68           = (k5_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X18)))),
% 0.50/0.68      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.50/0.68  thf('4', plain,
% 0.50/0.68      (((k2_xboole_0 @ sk_B @ sk_A)
% 0.50/0.68         = (k5_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.50/0.68      inference('sup+', [status(thm)], ['2', '3'])).
% 0.50/0.68  thf('5', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.50/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.68  thf(d2_subset_1, axiom,
% 0.50/0.68    (![A:$i,B:$i]:
% 0.50/0.68     ( ( ( v1_xboole_0 @ A ) =>
% 0.50/0.68         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.50/0.68       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.50/0.68         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.50/0.68  thf('6', plain,
% 0.50/0.68      (![X35 : $i, X36 : $i]:
% 0.50/0.68         (~ (m1_subset_1 @ X35 @ X36)
% 0.50/0.68          | (r2_hidden @ X35 @ X36)
% 0.50/0.68          | (v1_xboole_0 @ X36))),
% 0.50/0.68      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.50/0.68  thf('7', plain,
% 0.50/0.68      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.50/0.68        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 0.50/0.68      inference('sup-', [status(thm)], ['5', '6'])).
% 0.50/0.68  thf(fc1_subset_1, axiom,
% 0.50/0.68    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.50/0.68  thf('8', plain, (![X43 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X43))),
% 0.50/0.68      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.50/0.68  thf('9', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.50/0.68      inference('clc', [status(thm)], ['7', '8'])).
% 0.50/0.68  thf(d1_zfmisc_1, axiom,
% 0.50/0.68    (![A:$i,B:$i]:
% 0.50/0.68     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.50/0.68       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.50/0.68  thf('10', plain,
% 0.50/0.68      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.50/0.68         (~ (r2_hidden @ X28 @ X27)
% 0.50/0.68          | (r1_tarski @ X28 @ X26)
% 0.50/0.68          | ((X27) != (k1_zfmisc_1 @ X26)))),
% 0.50/0.68      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.50/0.68  thf('11', plain,
% 0.50/0.68      (![X26 : $i, X28 : $i]:
% 0.50/0.68         ((r1_tarski @ X28 @ X26) | ~ (r2_hidden @ X28 @ (k1_zfmisc_1 @ X26)))),
% 0.50/0.68      inference('simplify', [status(thm)], ['10'])).
% 0.50/0.68  thf('12', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.50/0.68      inference('sup-', [status(thm)], ['9', '11'])).
% 0.50/0.68  thf(t28_xboole_1, axiom,
% 0.50/0.68    (![A:$i,B:$i]:
% 0.50/0.68     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.50/0.68  thf('13', plain,
% 0.50/0.68      (![X10 : $i, X11 : $i]:
% 0.50/0.68         (((k3_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_tarski @ X10 @ X11))),
% 0.50/0.68      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.50/0.68  thf('14', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 0.50/0.68      inference('sup-', [status(thm)], ['12', '13'])).
% 0.50/0.68  thf(commutativity_k3_xboole_0, axiom,
% 0.50/0.68    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.50/0.68  thf('15', plain,
% 0.50/0.68      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.50/0.68      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.50/0.68  thf(t100_xboole_1, axiom,
% 0.50/0.68    (![A:$i,B:$i]:
% 0.50/0.68     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.50/0.68  thf('16', plain,
% 0.50/0.68      (![X3 : $i, X4 : $i]:
% 0.50/0.68         ((k4_xboole_0 @ X3 @ X4)
% 0.50/0.68           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.50/0.68      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.50/0.68  thf('17', plain,
% 0.50/0.68      (![X0 : $i, X1 : $i]:
% 0.50/0.68         ((k4_xboole_0 @ X0 @ X1)
% 0.50/0.68           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.50/0.68      inference('sup+', [status(thm)], ['15', '16'])).
% 0.50/0.68  thf('18', plain,
% 0.50/0.68      (((k4_xboole_0 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 0.50/0.68      inference('sup+', [status(thm)], ['14', '17'])).
% 0.50/0.68  thf('19', plain,
% 0.50/0.68      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.50/0.68      inference('sup-', [status(thm)], ['0', '1'])).
% 0.50/0.68  thf('20', plain,
% 0.50/0.68      (((k3_subset_1 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 0.50/0.68      inference('demod', [status(thm)], ['18', '19'])).
% 0.50/0.68  thf(t91_xboole_1, axiom,
% 0.50/0.68    (![A:$i,B:$i,C:$i]:
% 0.50/0.68     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.50/0.68       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.50/0.68  thf('21', plain,
% 0.50/0.68      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.50/0.68         ((k5_xboole_0 @ (k5_xboole_0 @ X15 @ X16) @ X17)
% 0.50/0.68           = (k5_xboole_0 @ X15 @ (k5_xboole_0 @ X16 @ X17)))),
% 0.50/0.68      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.50/0.68  thf(idempotence_k3_xboole_0, axiom,
% 0.50/0.68    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.50/0.68  thf('22', plain, (![X2 : $i]: ((k3_xboole_0 @ X2 @ X2) = (X2))),
% 0.50/0.68      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.50/0.68  thf('23', plain,
% 0.50/0.68      (![X3 : $i, X4 : $i]:
% 0.50/0.68         ((k4_xboole_0 @ X3 @ X4)
% 0.50/0.68           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.50/0.68      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.50/0.68  thf('24', plain,
% 0.50/0.68      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.50/0.68      inference('sup+', [status(thm)], ['22', '23'])).
% 0.50/0.68  thf('25', plain, (![X2 : $i]: ((k3_xboole_0 @ X2 @ X2) = (X2))),
% 0.50/0.68      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.50/0.68  thf(t22_xboole_1, axiom,
% 0.50/0.68    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.50/0.68  thf('26', plain,
% 0.50/0.68      (![X8 : $i, X9 : $i]:
% 0.50/0.68         ((k2_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)) = (X8))),
% 0.50/0.68      inference('cnf', [status(esa)], [t22_xboole_1])).
% 0.50/0.68  thf('27', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.50/0.68      inference('sup+', [status(thm)], ['25', '26'])).
% 0.50/0.68  thf(t46_xboole_1, axiom,
% 0.50/0.68    (![A:$i,B:$i]:
% 0.50/0.68     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.50/0.68  thf('28', plain,
% 0.50/0.68      (![X12 : $i, X13 : $i]:
% 0.50/0.68         ((k4_xboole_0 @ X12 @ (k2_xboole_0 @ X12 @ X13)) = (k1_xboole_0))),
% 0.50/0.68      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.50/0.68  thf('29', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.50/0.68      inference('sup+', [status(thm)], ['27', '28'])).
% 0.50/0.68  thf('30', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 0.50/0.68      inference('demod', [status(thm)], ['24', '29'])).
% 0.50/0.68  thf('31', plain,
% 0.50/0.68      (![X0 : $i, X1 : $i]:
% 0.50/0.68         ((k1_xboole_0)
% 0.50/0.68           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))))),
% 0.50/0.68      inference('sup+', [status(thm)], ['21', '30'])).
% 0.50/0.68  thf('32', plain,
% 0.50/0.68      (((k1_xboole_0)
% 0.50/0.68         = (k5_xboole_0 @ sk_A @ 
% 0.50/0.68            (k5_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))))),
% 0.50/0.68      inference('sup+', [status(thm)], ['20', '31'])).
% 0.50/0.68  thf('33', plain,
% 0.50/0.68      (((k2_xboole_0 @ sk_B @ sk_A)
% 0.50/0.68         = (k5_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.50/0.68      inference('sup+', [status(thm)], ['2', '3'])).
% 0.50/0.68  thf('34', plain,
% 0.50/0.68      (((k1_xboole_0) = (k5_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_A)))),
% 0.50/0.68      inference('demod', [status(thm)], ['32', '33'])).
% 0.50/0.68  thf('35', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 0.50/0.68      inference('demod', [status(thm)], ['24', '29'])).
% 0.50/0.68  thf('36', plain,
% 0.50/0.68      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.50/0.68         ((k5_xboole_0 @ (k5_xboole_0 @ X15 @ X16) @ X17)
% 0.50/0.68           = (k5_xboole_0 @ X15 @ (k5_xboole_0 @ X16 @ X17)))),
% 0.50/0.68      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.50/0.68  thf('37', plain,
% 0.50/0.68      (![X0 : $i, X1 : $i]:
% 0.50/0.68         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.50/0.68           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.50/0.68      inference('sup+', [status(thm)], ['35', '36'])).
% 0.50/0.68  thf('38', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 0.50/0.68      inference('demod', [status(thm)], ['24', '29'])).
% 0.50/0.68  thf(t112_xboole_1, axiom,
% 0.50/0.68    (![A:$i,B:$i,C:$i]:
% 0.50/0.68     ( ( k5_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ B ) ) =
% 0.50/0.68       ( k3_xboole_0 @ ( k5_xboole_0 @ A @ C ) @ B ) ))).
% 0.50/0.68  thf('39', plain,
% 0.50/0.68      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.50/0.68         ((k5_xboole_0 @ (k3_xboole_0 @ X5 @ X7) @ (k3_xboole_0 @ X6 @ X7))
% 0.50/0.68           = (k3_xboole_0 @ (k5_xboole_0 @ X5 @ X6) @ X7))),
% 0.50/0.68      inference('cnf', [status(esa)], [t112_xboole_1])).
% 0.50/0.68  thf('40', plain,
% 0.50/0.68      (![X0 : $i, X1 : $i]:
% 0.50/0.68         ((k1_xboole_0) = (k3_xboole_0 @ (k5_xboole_0 @ X1 @ X1) @ X0))),
% 0.50/0.68      inference('sup+', [status(thm)], ['38', '39'])).
% 0.50/0.68  thf('41', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 0.50/0.68      inference('demod', [status(thm)], ['24', '29'])).
% 0.50/0.68  thf('42', plain,
% 0.50/0.68      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 0.50/0.68      inference('demod', [status(thm)], ['40', '41'])).
% 0.50/0.68  thf('43', plain,
% 0.50/0.68      (![X0 : $i, X1 : $i]:
% 0.50/0.68         ((k4_xboole_0 @ X0 @ X1)
% 0.50/0.68           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.50/0.68      inference('sup+', [status(thm)], ['15', '16'])).
% 0.50/0.68  thf('44', plain,
% 0.50/0.68      (![X0 : $i]:
% 0.50/0.68         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.50/0.68      inference('sup+', [status(thm)], ['42', '43'])).
% 0.50/0.68  thf(t5_boole, axiom,
% 0.50/0.68    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.50/0.68  thf('45', plain, (![X14 : $i]: ((k5_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.50/0.68      inference('cnf', [status(esa)], [t5_boole])).
% 0.50/0.68  thf('46', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.50/0.68      inference('sup+', [status(thm)], ['44', '45'])).
% 0.50/0.68  thf('47', plain,
% 0.50/0.68      (![X18 : $i, X19 : $i]:
% 0.50/0.68         ((k2_xboole_0 @ X18 @ X19)
% 0.50/0.68           = (k5_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X18)))),
% 0.50/0.68      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.50/0.68  thf('48', plain,
% 0.50/0.68      (![X0 : $i]:
% 0.50/0.68         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 0.50/0.68      inference('sup+', [status(thm)], ['46', '47'])).
% 0.50/0.68  thf('49', plain,
% 0.50/0.68      (![X0 : $i, X1 : $i]:
% 0.50/0.68         ((k2_xboole_0 @ k1_xboole_0 @ X0)
% 0.50/0.68           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.50/0.68      inference('demod', [status(thm)], ['37', '48'])).
% 0.50/0.68  thf('50', plain,
% 0.50/0.68      (((k2_xboole_0 @ k1_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_A))
% 0.50/0.68         = (k5_xboole_0 @ sk_A @ k1_xboole_0))),
% 0.50/0.68      inference('sup+', [status(thm)], ['34', '49'])).
% 0.50/0.68  thf('51', plain, (![X14 : $i]: ((k5_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.50/0.68      inference('cnf', [status(esa)], [t5_boole])).
% 0.50/0.68  thf('52', plain,
% 0.50/0.68      (((k2_xboole_0 @ k1_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_A)) = (sk_A))),
% 0.50/0.68      inference('demod', [status(thm)], ['50', '51'])).
% 0.50/0.68  thf('53', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 0.50/0.68      inference('demod', [status(thm)], ['24', '29'])).
% 0.50/0.68  thf('54', plain,
% 0.50/0.68      (![X0 : $i, X1 : $i]:
% 0.50/0.68         ((k2_xboole_0 @ k1_xboole_0 @ X0)
% 0.50/0.68           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.50/0.68      inference('demod', [status(thm)], ['37', '48'])).
% 0.50/0.68  thf('55', plain,
% 0.50/0.68      (![X0 : $i]:
% 0.50/0.68         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.50/0.68      inference('sup+', [status(thm)], ['53', '54'])).
% 0.50/0.68  thf('56', plain, (![X14 : $i]: ((k5_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.50/0.68      inference('cnf', [status(esa)], [t5_boole])).
% 0.50/0.68  thf('57', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.50/0.68      inference('sup+', [status(thm)], ['55', '56'])).
% 0.50/0.68  thf('58', plain, (((k2_xboole_0 @ sk_B @ sk_A) = (sk_A))),
% 0.50/0.68      inference('demod', [status(thm)], ['52', '57'])).
% 0.50/0.68  thf('59', plain,
% 0.50/0.68      (((sk_A) = (k5_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.50/0.68      inference('demod', [status(thm)], ['4', '58'])).
% 0.50/0.68  thf('60', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.50/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.68  thf(dt_k3_subset_1, axiom,
% 0.50/0.68    (![A:$i,B:$i]:
% 0.50/0.68     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.50/0.68       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.50/0.68  thf('61', plain,
% 0.50/0.68      (![X41 : $i, X42 : $i]:
% 0.50/0.68         ((m1_subset_1 @ (k3_subset_1 @ X41 @ X42) @ (k1_zfmisc_1 @ X41))
% 0.50/0.68          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ X41)))),
% 0.50/0.68      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.50/0.68  thf('62', plain,
% 0.50/0.68      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.50/0.68      inference('sup-', [status(thm)], ['60', '61'])).
% 0.50/0.68  thf('63', plain,
% 0.50/0.68      (![X35 : $i, X36 : $i]:
% 0.50/0.68         (~ (m1_subset_1 @ X35 @ X36)
% 0.50/0.68          | (r2_hidden @ X35 @ X36)
% 0.50/0.68          | (v1_xboole_0 @ X36))),
% 0.50/0.68      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.50/0.68  thf('64', plain,
% 0.50/0.68      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.50/0.68        | (r2_hidden @ (k3_subset_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A)))),
% 0.50/0.68      inference('sup-', [status(thm)], ['62', '63'])).
% 0.50/0.68  thf('65', plain, (![X43 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X43))),
% 0.50/0.68      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.50/0.68  thf('66', plain,
% 0.50/0.68      ((r2_hidden @ (k3_subset_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.50/0.68      inference('clc', [status(thm)], ['64', '65'])).
% 0.50/0.68  thf('67', plain,
% 0.50/0.68      (![X26 : $i, X28 : $i]:
% 0.50/0.68         ((r1_tarski @ X28 @ X26) | ~ (r2_hidden @ X28 @ (k1_zfmisc_1 @ X26)))),
% 0.50/0.68      inference('simplify', [status(thm)], ['10'])).
% 0.50/0.68  thf('68', plain, ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_A)),
% 0.50/0.68      inference('sup-', [status(thm)], ['66', '67'])).
% 0.50/0.68  thf('69', plain,
% 0.50/0.68      (![X10 : $i, X11 : $i]:
% 0.50/0.68         (((k3_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_tarski @ X10 @ X11))),
% 0.50/0.68      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.50/0.68  thf('70', plain,
% 0.50/0.68      (((k3_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ sk_A)
% 0.50/0.68         = (k3_subset_1 @ sk_A @ sk_B))),
% 0.50/0.68      inference('sup-', [status(thm)], ['68', '69'])).
% 0.50/0.68  thf('71', plain,
% 0.50/0.68      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.50/0.68      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.50/0.68  thf('72', plain,
% 0.50/0.68      (((k3_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B))
% 0.50/0.68         = (k3_subset_1 @ sk_A @ sk_B))),
% 0.50/0.68      inference('demod', [status(thm)], ['70', '71'])).
% 0.50/0.68  thf('73', plain,
% 0.50/0.68      (![X3 : $i, X4 : $i]:
% 0.50/0.68         ((k4_xboole_0 @ X3 @ X4)
% 0.50/0.68           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.50/0.68      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.50/0.68  thf('74', plain,
% 0.50/0.68      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.50/0.68         ((k5_xboole_0 @ (k3_xboole_0 @ X5 @ X7) @ (k3_xboole_0 @ X6 @ X7))
% 0.50/0.68           = (k3_xboole_0 @ (k5_xboole_0 @ X5 @ X6) @ X7))),
% 0.50/0.68      inference('cnf', [status(esa)], [t112_xboole_1])).
% 0.50/0.68  thf('75', plain,
% 0.50/0.68      (![X0 : $i, X1 : $i]:
% 0.50/0.68         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0)
% 0.50/0.68           = (k3_xboole_0 @ (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)) @ X0))),
% 0.50/0.68      inference('sup+', [status(thm)], ['73', '74'])).
% 0.50/0.68  thf('76', plain,
% 0.50/0.68      (![X3 : $i, X4 : $i]:
% 0.50/0.68         ((k4_xboole_0 @ X3 @ X4)
% 0.50/0.68           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.50/0.68      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.50/0.68  thf('77', plain,
% 0.50/0.68      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.50/0.68      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.50/0.68  thf('78', plain,
% 0.50/0.68      (![X0 : $i, X1 : $i]:
% 0.50/0.68         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0)
% 0.50/0.68           = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.50/0.68      inference('demod', [status(thm)], ['75', '76', '77'])).
% 0.50/0.68  thf('79', plain,
% 0.50/0.68      (((k4_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ 
% 0.50/0.68         (k3_subset_1 @ sk_A @ sk_B))
% 0.50/0.68         = (k3_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ 
% 0.50/0.68            (k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B))))),
% 0.50/0.68      inference('sup+', [status(thm)], ['72', '78'])).
% 0.50/0.68  thf('80', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.50/0.68      inference('sup+', [status(thm)], ['27', '28'])).
% 0.50/0.68  thf('81', plain,
% 0.50/0.68      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.50/0.68      inference('sup-', [status(thm)], ['60', '61'])).
% 0.50/0.68  thf('82', plain,
% 0.50/0.68      (![X39 : $i, X40 : $i]:
% 0.50/0.68         (((k3_subset_1 @ X39 @ X40) = (k4_xboole_0 @ X39 @ X40))
% 0.50/0.68          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ X39)))),
% 0.50/0.68      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.50/0.68  thf('83', plain,
% 0.50/0.68      (((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B))
% 0.50/0.68         = (k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.50/0.68      inference('sup-', [status(thm)], ['81', '82'])).
% 0.50/0.68  thf('84', plain,
% 0.50/0.68      (((k3_subset_1 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 0.50/0.68      inference('demod', [status(thm)], ['18', '19'])).
% 0.50/0.68  thf('85', plain,
% 0.50/0.68      (![X0 : $i, X1 : $i]:
% 0.50/0.68         ((k2_xboole_0 @ k1_xboole_0 @ X0)
% 0.50/0.68           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.50/0.68      inference('demod', [status(thm)], ['37', '48'])).
% 0.50/0.68  thf('86', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.50/0.68      inference('sup+', [status(thm)], ['55', '56'])).
% 0.50/0.68  thf('87', plain,
% 0.50/0.68      (![X0 : $i, X1 : $i]:
% 0.50/0.68         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.50/0.68      inference('demod', [status(thm)], ['85', '86'])).
% 0.50/0.68  thf('88', plain,
% 0.50/0.68      (((sk_B) = (k5_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.50/0.68      inference('sup+', [status(thm)], ['84', '87'])).
% 0.50/0.68  thf('89', plain,
% 0.50/0.68      (((k3_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B))
% 0.50/0.68         = (k3_subset_1 @ sk_A @ sk_B))),
% 0.50/0.68      inference('demod', [status(thm)], ['70', '71'])).
% 0.50/0.68  thf('90', plain,
% 0.50/0.68      (![X3 : $i, X4 : $i]:
% 0.50/0.68         ((k4_xboole_0 @ X3 @ X4)
% 0.50/0.68           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.50/0.68      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.50/0.68  thf('91', plain,
% 0.50/0.68      (((k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B))
% 0.50/0.68         = (k5_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.50/0.68      inference('sup+', [status(thm)], ['89', '90'])).
% 0.50/0.68  thf('92', plain,
% 0.50/0.68      (((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B))
% 0.50/0.68         = (k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.50/0.68      inference('sup-', [status(thm)], ['81', '82'])).
% 0.50/0.68  thf('93', plain,
% 0.50/0.68      (((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B))
% 0.50/0.68         = (k5_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.50/0.68      inference('demod', [status(thm)], ['91', '92'])).
% 0.50/0.68  thf('94', plain,
% 0.50/0.68      (((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)) = (sk_B))),
% 0.50/0.68      inference('sup+', [status(thm)], ['88', '93'])).
% 0.50/0.68  thf('95', plain,
% 0.50/0.68      (((sk_B) = (k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.50/0.68      inference('demod', [status(thm)], ['83', '94'])).
% 0.50/0.68  thf('96', plain,
% 0.50/0.68      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.50/0.68      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.50/0.68  thf('97', plain,
% 0.50/0.68      (((k1_xboole_0) = (k3_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.50/0.68      inference('demod', [status(thm)], ['79', '80', '95', '96'])).
% 0.50/0.68  thf('98', plain,
% 0.50/0.68      (![X0 : $i, X1 : $i]:
% 0.50/0.68         ((k4_xboole_0 @ X0 @ X1)
% 0.50/0.68           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.50/0.68      inference('sup+', [status(thm)], ['15', '16'])).
% 0.50/0.68  thf('99', plain,
% 0.50/0.68      (((k4_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)
% 0.50/0.68         = (k5_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ k1_xboole_0))),
% 0.50/0.68      inference('sup+', [status(thm)], ['97', '98'])).
% 0.50/0.68  thf('100', plain,
% 0.50/0.68      (![X0 : $i, X1 : $i]:
% 0.50/0.68         ((k1_xboole_0)
% 0.50/0.68           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))))),
% 0.50/0.68      inference('sup+', [status(thm)], ['21', '30'])).
% 0.50/0.68  thf('101', plain,
% 0.50/0.68      (![X0 : $i, X1 : $i]:
% 0.50/0.68         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.50/0.68      inference('demod', [status(thm)], ['85', '86'])).
% 0.50/0.68  thf('102', plain,
% 0.50/0.68      (![X0 : $i, X1 : $i]:
% 0.50/0.68         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))
% 0.50/0.68           = (k5_xboole_0 @ X1 @ k1_xboole_0))),
% 0.50/0.68      inference('sup+', [status(thm)], ['100', '101'])).
% 0.50/0.68  thf('103', plain, (![X14 : $i]: ((k5_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.50/0.68      inference('cnf', [status(esa)], [t5_boole])).
% 0.50/0.68  thf('104', plain,
% 0.50/0.68      (![X0 : $i, X1 : $i]:
% 0.50/0.68         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)) = (X1))),
% 0.50/0.68      inference('demod', [status(thm)], ['102', '103'])).
% 0.50/0.68  thf('105', plain,
% 0.50/0.68      (![X0 : $i, X1 : $i]:
% 0.50/0.68         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.50/0.68      inference('demod', [status(thm)], ['85', '86'])).
% 0.50/0.68  thf('106', plain,
% 0.50/0.68      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 0.50/0.68      inference('sup+', [status(thm)], ['104', '105'])).
% 0.50/0.68  thf('107', plain,
% 0.50/0.68      (![X0 : $i]:
% 0.50/0.68         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 0.50/0.68      inference('sup+', [status(thm)], ['46', '47'])).
% 0.50/0.68  thf('108', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.50/0.68      inference('sup+', [status(thm)], ['55', '56'])).
% 0.50/0.68  thf('109', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 0.50/0.68      inference('demod', [status(thm)], ['107', '108'])).
% 0.50/0.68  thf('110', plain,
% 0.50/0.68      (((k4_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)
% 0.50/0.68         = (k3_subset_1 @ sk_A @ sk_B))),
% 0.50/0.68      inference('demod', [status(thm)], ['99', '106', '109'])).
% 0.50/0.68  thf('111', plain,
% 0.50/0.68      (![X18 : $i, X19 : $i]:
% 0.50/0.68         ((k2_xboole_0 @ X18 @ X19)
% 0.50/0.68           = (k5_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X18)))),
% 0.50/0.68      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.50/0.68  thf('112', plain,
% 0.50/0.68      (((k2_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 0.50/0.68         = (k5_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.50/0.68      inference('sup+', [status(thm)], ['110', '111'])).
% 0.50/0.68  thf('113', plain,
% 0.50/0.68      (((k2_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)) = (sk_A))),
% 0.50/0.68      inference('sup+', [status(thm)], ['59', '112'])).
% 0.50/0.68  thf('114', plain,
% 0.50/0.68      (((k4_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 0.50/0.68         != (k2_subset_1 @ sk_A))),
% 0.50/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.68  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.50/0.68  thf('115', plain, (![X38 : $i]: ((k2_subset_1 @ X38) = (X38))),
% 0.50/0.68      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.50/0.68  thf('116', plain,
% 0.50/0.68      (((k4_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)) != (sk_A))),
% 0.50/0.68      inference('demod', [status(thm)], ['114', '115'])).
% 0.50/0.68  thf('117', plain,
% 0.50/0.68      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.50/0.68      inference('sup-', [status(thm)], ['60', '61'])).
% 0.50/0.68  thf('118', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.50/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.68  thf(redefinition_k4_subset_1, axiom,
% 0.50/0.68    (![A:$i,B:$i,C:$i]:
% 0.50/0.68     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.50/0.68         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.50/0.68       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.50/0.68  thf('119', plain,
% 0.50/0.68      (![X44 : $i, X45 : $i, X46 : $i]:
% 0.50/0.68         (~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ X45))
% 0.50/0.68          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ X45))
% 0.50/0.68          | ((k4_subset_1 @ X45 @ X44 @ X46) = (k2_xboole_0 @ X44 @ X46)))),
% 0.50/0.68      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.50/0.68  thf('120', plain,
% 0.50/0.68      (![X0 : $i]:
% 0.50/0.68         (((k4_subset_1 @ sk_A @ sk_B @ X0) = (k2_xboole_0 @ sk_B @ X0))
% 0.50/0.68          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 0.50/0.68      inference('sup-', [status(thm)], ['118', '119'])).
% 0.50/0.68  thf('121', plain,
% 0.50/0.68      (((k4_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 0.50/0.68         = (k2_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.50/0.68      inference('sup-', [status(thm)], ['117', '120'])).
% 0.50/0.68  thf('122', plain,
% 0.50/0.68      (((k2_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)) != (sk_A))),
% 0.50/0.68      inference('demod', [status(thm)], ['116', '121'])).
% 0.50/0.68  thf('123', plain, ($false),
% 0.50/0.68      inference('simplify_reflect-', [status(thm)], ['113', '122'])).
% 0.50/0.68  
% 0.50/0.68  % SZS output end Refutation
% 0.50/0.68  
% 0.50/0.69  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
