%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.OX7hTID966

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:53 EST 2020

% Result     : Theorem 0.41s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :  146 ( 274 expanded)
%              Number of leaves         :   36 ( 101 expanded)
%              Depth                    :   21
%              Number of atoms          :  985 (2053 expanded)
%              Number of equality atoms :   93 ( 187 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

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
    ! [X53: $i,X54: $i] :
      ( ~ ( m1_subset_1 @ X53 @ X54 )
      | ( r2_hidden @ X53 @ X54 )
      | ( v1_xboole_0 @ X54 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('2',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('3',plain,(
    ! [X61: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X61 ) ) ),
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
    ! [X47: $i,X48: $i,X49: $i] :
      ( ~ ( r2_hidden @ X49 @ X48 )
      | ( r1_tarski @ X49 @ X47 )
      | ( X48
       != ( k1_zfmisc_1 @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('6',plain,(
    ! [X47: $i,X49: $i] :
      ( ( r1_tarski @ X49 @ X47 )
      | ~ ( r2_hidden @ X49 @ ( k1_zfmisc_1 @ X47 ) ) ) ),
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
    ! [X9: $i,X10: $i] :
      ( ( ( k3_xboole_0 @ X9 @ X10 )
        = X9 )
      | ~ ( r1_tarski @ X9 @ X10 ) ) ),
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
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
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

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('14',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('15',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('17',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['7','8'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

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
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X2 @ X1 ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X0 @ X2 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ sk_B @ ( k3_xboole_0 @ X0 @ sk_B ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ sk_A @ X0 ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['17','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_B @ X0 )
      = ( k3_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_B @ X0 )
      = ( k3_xboole_0 @ sk_B @ ( k5_xboole_0 @ X0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['16','24'])).

thf('26',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_B )
    = ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['15','25'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('27',plain,(
    ! [X11: $i] :
      ( r1_tarski @ k1_xboole_0 @ X11 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('28',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ~ ( r1_tarski @ X46 @ X47 )
      | ( r2_hidden @ X46 @ X48 )
      | ( X48
       != ( k1_zfmisc_1 @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('29',plain,(
    ! [X46: $i,X47: $i] :
      ( ( r2_hidden @ X46 @ ( k1_zfmisc_1 @ X47 ) )
      | ~ ( r1_tarski @ X46 @ X47 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( r2_hidden @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','29'])).

thf('31',plain,(
    ! [X53: $i,X54: $i] :
      ( ~ ( r2_hidden @ X53 @ X54 )
      | ( m1_subset_1 @ X53 @ X54 )
      | ( v1_xboole_0 @ X54 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X61: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X61 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['32','33'])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('35',plain,(
    ! [X59: $i,X60: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X59 @ X60 ) @ ( k1_zfmisc_1 @ X59 ) )
      | ~ ( m1_subset_1 @ X60 @ ( k1_zfmisc_1 @ X59 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['32','33'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('38',plain,(
    ! [X57: $i,X58: $i] :
      ( ( ( k3_subset_1 @ X57 @ X58 )
        = ( k4_xboole_0 @ X57 @ X58 ) )
      | ~ ( m1_subset_1 @ X58 @ ( k1_zfmisc_1 @ X57 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X11: $i] :
      ( r1_tarski @ k1_xboole_0 @ X11 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('41',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_xboole_0 @ X9 @ X10 )
        = X9 )
      | ~ ( r1_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('47',plain,(
    ! [X12: $i] :
      ( ( k5_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['39','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['36','49'])).

thf('51',plain,(
    ! [X53: $i,X54: $i] :
      ( ~ ( m1_subset_1 @ X53 @ X54 )
      | ( r2_hidden @ X53 @ X54 )
      | ( v1_xboole_0 @ X54 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X61: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X61 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X47: $i,X49: $i] :
      ( ( r1_tarski @ X49 @ X47 )
      | ~ ( r2_hidden @ X49 @ ( k1_zfmisc_1 @ X47 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('56',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_xboole_0 @ X9 @ X10 )
        = X9 )
      | ~ ( r1_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('61',plain,(
    ! [X16: $i] :
      ( ( k5_xboole_0 @ X16 @ X16 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['26','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('65',plain,
    ( ( k4_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_B )
    = ( k5_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('67',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('68',plain,(
    ! [X12: $i] :
      ( ( k5_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('70',plain,
    ( ( k4_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['65','66','69'])).

thf(t94_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('71',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X17 @ X18 ) @ ( k3_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t94_xboole_1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('72',plain,(
    ! [X51: $i,X52: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X51 @ X52 ) )
      = ( k2_xboole_0 @ X51 @ X52 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('73',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k5_xboole_0 @ X13 @ ( k5_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('75',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X17 @ X18 ) )
      = ( k5_xboole_0 @ X17 @ ( k4_xboole_0 @ X18 @ X17 ) ) ) ),
    inference(demod,[status(thm)],['71','72','73','74'])).

thf('76',plain,
    ( ( k3_tarski @ ( k2_tarski @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) ) )
    = ( k5_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['70','75'])).

thf('77',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X17 @ X18 ) )
      = ( k5_xboole_0 @ X17 @ ( k4_xboole_0 @ X18 @ X17 ) ) ) ),
    inference(demod,[status(thm)],['71','72','73','74'])).

thf('78',plain,
    ( ( k3_tarski @ ( k2_tarski @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) ) )
    = ( k3_tarski @ ( k2_tarski @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('80',plain,(
    ! [X16: $i] :
      ( ( k5_xboole_0 @ X16 @ X16 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('81',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k5_xboole_0 @ X13 @ ( k5_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,
    ( sk_A
    = ( k5_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['79','84'])).

thf('86',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X17 @ X18 ) )
      = ( k5_xboole_0 @ X17 @ ( k4_xboole_0 @ X18 @ X17 ) ) ) ),
    inference(demod,[status(thm)],['71','72','73','74'])).

thf('87',plain,
    ( sk_A
    = ( k3_tarski @ ( k2_tarski @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,
    ( ( k3_tarski @ ( k2_tarski @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) ) )
    = sk_A ),
    inference(demod,[status(thm)],['78','87'])).

thf('89',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
 != ( k2_subset_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('90',plain,(
    ! [X56: $i] :
      ( ( k2_subset_1 @ X56 )
      = X56 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('91',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
 != sk_A ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    ! [X57: $i,X58: $i] :
      ( ( ( k3_subset_1 @ X57 @ X58 )
        = ( k4_xboole_0 @ X57 @ X58 ) )
      | ~ ( m1_subset_1 @ X58 @ ( k1_zfmisc_1 @ X57 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('94',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) )
 != sk_A ),
    inference(demod,[status(thm)],['91','94'])).

thf('96',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    ! [X59: $i,X60: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X59 @ X60 ) @ ( k1_zfmisc_1 @ X59 ) )
      | ~ ( m1_subset_1 @ X60 @ ( k1_zfmisc_1 @ X59 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('98',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('100',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('102',plain,(
    ! [X62: $i,X63: $i,X64: $i] :
      ( ~ ( m1_subset_1 @ X62 @ ( k1_zfmisc_1 @ X63 ) )
      | ~ ( m1_subset_1 @ X64 @ ( k1_zfmisc_1 @ X63 ) )
      | ( ( k4_subset_1 @ X63 @ X62 @ X64 )
        = ( k2_xboole_0 @ X62 @ X64 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('103',plain,(
    ! [X51: $i,X52: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X51 @ X52 ) )
      = ( k2_xboole_0 @ X51 @ X52 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('104',plain,(
    ! [X62: $i,X63: $i,X64: $i] :
      ( ~ ( m1_subset_1 @ X62 @ ( k1_zfmisc_1 @ X63 ) )
      | ~ ( m1_subset_1 @ X64 @ ( k1_zfmisc_1 @ X63 ) )
      | ( ( k4_subset_1 @ X63 @ X62 @ X64 )
        = ( k3_tarski @ ( k2_tarski @ X62 @ X64 ) ) ) ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ sk_A @ sk_B @ X0 )
        = ( k3_tarski @ ( k2_tarski @ sk_B @ X0 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['101','104'])).

thf('106',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = ( k3_tarski @ ( k2_tarski @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['100','105'])).

thf('107',plain,(
    ( k3_tarski @ ( k2_tarski @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) ) )
 != sk_A ),
    inference(demod,[status(thm)],['95','106'])).

thf('108',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['88','107'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.OX7hTID966
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:28:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.41/0.58  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.41/0.58  % Solved by: fo/fo7.sh
% 0.41/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.41/0.58  % done 418 iterations in 0.130s
% 0.41/0.58  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.41/0.58  % SZS output start Refutation
% 0.41/0.58  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.41/0.58  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.41/0.58  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.41/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.41/0.58  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.41/0.58  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.41/0.58  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.41/0.58  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.41/0.58  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.41/0.58  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.41/0.58  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.41/0.58  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.41/0.58  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.41/0.58  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.41/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.41/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.41/0.58  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.41/0.58  thf(t25_subset_1, conjecture,
% 0.41/0.58    (![A:$i,B:$i]:
% 0.41/0.58     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.41/0.58       ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) ) =
% 0.41/0.58         ( k2_subset_1 @ A ) ) ))).
% 0.41/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.41/0.58    (~( ![A:$i,B:$i]:
% 0.41/0.58        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.41/0.58          ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) ) =
% 0.41/0.58            ( k2_subset_1 @ A ) ) ) )),
% 0.41/0.58    inference('cnf.neg', [status(esa)], [t25_subset_1])).
% 0.41/0.58  thf('0', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.41/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.58  thf(d2_subset_1, axiom,
% 0.41/0.58    (![A:$i,B:$i]:
% 0.41/0.58     ( ( ( v1_xboole_0 @ A ) =>
% 0.41/0.58         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.41/0.58       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.41/0.58         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.41/0.58  thf('1', plain,
% 0.41/0.58      (![X53 : $i, X54 : $i]:
% 0.41/0.58         (~ (m1_subset_1 @ X53 @ X54)
% 0.41/0.58          | (r2_hidden @ X53 @ X54)
% 0.41/0.58          | (v1_xboole_0 @ X54))),
% 0.41/0.58      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.41/0.58  thf('2', plain,
% 0.41/0.58      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.41/0.58        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 0.41/0.58      inference('sup-', [status(thm)], ['0', '1'])).
% 0.41/0.58  thf(fc1_subset_1, axiom,
% 0.41/0.58    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.41/0.58  thf('3', plain, (![X61 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X61))),
% 0.41/0.58      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.41/0.58  thf('4', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.41/0.58      inference('clc', [status(thm)], ['2', '3'])).
% 0.41/0.58  thf(d1_zfmisc_1, axiom,
% 0.41/0.58    (![A:$i,B:$i]:
% 0.41/0.58     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.41/0.58       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.41/0.58  thf('5', plain,
% 0.41/0.58      (![X47 : $i, X48 : $i, X49 : $i]:
% 0.41/0.58         (~ (r2_hidden @ X49 @ X48)
% 0.41/0.58          | (r1_tarski @ X49 @ X47)
% 0.41/0.58          | ((X48) != (k1_zfmisc_1 @ X47)))),
% 0.41/0.58      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.41/0.58  thf('6', plain,
% 0.41/0.58      (![X47 : $i, X49 : $i]:
% 0.41/0.58         ((r1_tarski @ X49 @ X47) | ~ (r2_hidden @ X49 @ (k1_zfmisc_1 @ X47)))),
% 0.41/0.58      inference('simplify', [status(thm)], ['5'])).
% 0.41/0.58  thf('7', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.41/0.58      inference('sup-', [status(thm)], ['4', '6'])).
% 0.41/0.58  thf(t28_xboole_1, axiom,
% 0.41/0.58    (![A:$i,B:$i]:
% 0.41/0.58     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.41/0.58  thf('8', plain,
% 0.41/0.58      (![X9 : $i, X10 : $i]:
% 0.41/0.58         (((k3_xboole_0 @ X9 @ X10) = (X9)) | ~ (r1_tarski @ X9 @ X10))),
% 0.41/0.58      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.41/0.58  thf('9', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 0.41/0.58      inference('sup-', [status(thm)], ['7', '8'])).
% 0.41/0.58  thf(commutativity_k3_xboole_0, axiom,
% 0.41/0.58    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.41/0.58  thf('10', plain,
% 0.41/0.58      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.41/0.58      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.41/0.58  thf(t100_xboole_1, axiom,
% 0.41/0.58    (![A:$i,B:$i]:
% 0.41/0.58     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.41/0.58  thf('11', plain,
% 0.41/0.58      (![X4 : $i, X5 : $i]:
% 0.41/0.58         ((k4_xboole_0 @ X4 @ X5)
% 0.41/0.58           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 0.41/0.58      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.41/0.58  thf('12', plain,
% 0.41/0.58      (![X0 : $i, X1 : $i]:
% 0.41/0.58         ((k4_xboole_0 @ X0 @ X1)
% 0.41/0.58           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.41/0.58      inference('sup+', [status(thm)], ['10', '11'])).
% 0.41/0.58  thf('13', plain,
% 0.41/0.58      (((k4_xboole_0 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 0.41/0.58      inference('sup+', [status(thm)], ['9', '12'])).
% 0.41/0.58  thf(commutativity_k5_xboole_0, axiom,
% 0.41/0.58    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.41/0.58  thf('14', plain,
% 0.41/0.58      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.41/0.58      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.41/0.58  thf('15', plain,
% 0.41/0.58      (((k4_xboole_0 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_B @ sk_A))),
% 0.41/0.58      inference('demod', [status(thm)], ['13', '14'])).
% 0.41/0.58  thf('16', plain,
% 0.41/0.58      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.41/0.58      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.41/0.58  thf('17', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 0.41/0.58      inference('sup-', [status(thm)], ['7', '8'])).
% 0.41/0.58  thf('18', plain,
% 0.41/0.58      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.41/0.58      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.41/0.58  thf(t112_xboole_1, axiom,
% 0.41/0.58    (![A:$i,B:$i,C:$i]:
% 0.41/0.58     ( ( k5_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ B ) ) =
% 0.41/0.58       ( k3_xboole_0 @ ( k5_xboole_0 @ A @ C ) @ B ) ))).
% 0.41/0.58  thf('19', plain,
% 0.41/0.58      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.41/0.58         ((k5_xboole_0 @ (k3_xboole_0 @ X6 @ X8) @ (k3_xboole_0 @ X7 @ X8))
% 0.41/0.58           = (k3_xboole_0 @ (k5_xboole_0 @ X6 @ X7) @ X8))),
% 0.41/0.58      inference('cnf', [status(esa)], [t112_xboole_1])).
% 0.41/0.58  thf('20', plain,
% 0.41/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.58         ((k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X2 @ X1))
% 0.41/0.58           = (k3_xboole_0 @ (k5_xboole_0 @ X0 @ X2) @ X1))),
% 0.41/0.58      inference('sup+', [status(thm)], ['18', '19'])).
% 0.41/0.58  thf('21', plain,
% 0.41/0.58      (![X0 : $i]:
% 0.41/0.58         ((k5_xboole_0 @ sk_B @ (k3_xboole_0 @ X0 @ sk_B))
% 0.41/0.58           = (k3_xboole_0 @ (k5_xboole_0 @ sk_A @ X0) @ sk_B))),
% 0.41/0.58      inference('sup+', [status(thm)], ['17', '20'])).
% 0.41/0.58  thf('22', plain,
% 0.41/0.58      (![X0 : $i, X1 : $i]:
% 0.41/0.58         ((k4_xboole_0 @ X0 @ X1)
% 0.41/0.58           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.41/0.58      inference('sup+', [status(thm)], ['10', '11'])).
% 0.41/0.58  thf('23', plain,
% 0.41/0.58      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.41/0.58      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.41/0.58  thf('24', plain,
% 0.41/0.58      (![X0 : $i]:
% 0.41/0.58         ((k4_xboole_0 @ sk_B @ X0)
% 0.41/0.58           = (k3_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_A @ X0)))),
% 0.41/0.58      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.41/0.58  thf('25', plain,
% 0.41/0.58      (![X0 : $i]:
% 0.41/0.58         ((k4_xboole_0 @ sk_B @ X0)
% 0.41/0.58           = (k3_xboole_0 @ sk_B @ (k5_xboole_0 @ X0 @ sk_A)))),
% 0.41/0.58      inference('sup+', [status(thm)], ['16', '24'])).
% 0.41/0.58  thf('26', plain,
% 0.41/0.58      (((k4_xboole_0 @ sk_B @ sk_B)
% 0.41/0.58         = (k3_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B)))),
% 0.41/0.58      inference('sup+', [status(thm)], ['15', '25'])).
% 0.41/0.58  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.41/0.58  thf('27', plain, (![X11 : $i]: (r1_tarski @ k1_xboole_0 @ X11)),
% 0.41/0.58      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.41/0.58  thf('28', plain,
% 0.41/0.58      (![X46 : $i, X47 : $i, X48 : $i]:
% 0.41/0.58         (~ (r1_tarski @ X46 @ X47)
% 0.41/0.58          | (r2_hidden @ X46 @ X48)
% 0.41/0.58          | ((X48) != (k1_zfmisc_1 @ X47)))),
% 0.41/0.58      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.41/0.58  thf('29', plain,
% 0.41/0.58      (![X46 : $i, X47 : $i]:
% 0.41/0.58         ((r2_hidden @ X46 @ (k1_zfmisc_1 @ X47)) | ~ (r1_tarski @ X46 @ X47))),
% 0.41/0.58      inference('simplify', [status(thm)], ['28'])).
% 0.41/0.58  thf('30', plain,
% 0.41/0.58      (![X0 : $i]: (r2_hidden @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.41/0.58      inference('sup-', [status(thm)], ['27', '29'])).
% 0.41/0.58  thf('31', plain,
% 0.41/0.58      (![X53 : $i, X54 : $i]:
% 0.41/0.58         (~ (r2_hidden @ X53 @ X54)
% 0.41/0.58          | (m1_subset_1 @ X53 @ X54)
% 0.41/0.58          | (v1_xboole_0 @ X54))),
% 0.41/0.58      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.41/0.58  thf('32', plain,
% 0.41/0.58      (![X0 : $i]:
% 0.41/0.58         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 0.41/0.58          | (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0)))),
% 0.41/0.58      inference('sup-', [status(thm)], ['30', '31'])).
% 0.41/0.58  thf('33', plain, (![X61 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X61))),
% 0.41/0.58      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.41/0.58  thf('34', plain,
% 0.41/0.58      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.41/0.58      inference('clc', [status(thm)], ['32', '33'])).
% 0.41/0.58  thf(dt_k3_subset_1, axiom,
% 0.41/0.58    (![A:$i,B:$i]:
% 0.41/0.58     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.41/0.58       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.41/0.58  thf('35', plain,
% 0.41/0.58      (![X59 : $i, X60 : $i]:
% 0.41/0.58         ((m1_subset_1 @ (k3_subset_1 @ X59 @ X60) @ (k1_zfmisc_1 @ X59))
% 0.41/0.58          | ~ (m1_subset_1 @ X60 @ (k1_zfmisc_1 @ X59)))),
% 0.41/0.58      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.41/0.58  thf('36', plain,
% 0.41/0.58      (![X0 : $i]:
% 0.41/0.58         (m1_subset_1 @ (k3_subset_1 @ X0 @ k1_xboole_0) @ (k1_zfmisc_1 @ X0))),
% 0.41/0.58      inference('sup-', [status(thm)], ['34', '35'])).
% 0.41/0.58  thf('37', plain,
% 0.41/0.58      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.41/0.58      inference('clc', [status(thm)], ['32', '33'])).
% 0.41/0.58  thf(d5_subset_1, axiom,
% 0.41/0.58    (![A:$i,B:$i]:
% 0.41/0.58     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.41/0.58       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.41/0.58  thf('38', plain,
% 0.41/0.58      (![X57 : $i, X58 : $i]:
% 0.41/0.58         (((k3_subset_1 @ X57 @ X58) = (k4_xboole_0 @ X57 @ X58))
% 0.41/0.58          | ~ (m1_subset_1 @ X58 @ (k1_zfmisc_1 @ X57)))),
% 0.41/0.58      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.41/0.58  thf('39', plain,
% 0.41/0.58      (![X0 : $i]:
% 0.41/0.58         ((k3_subset_1 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.41/0.58      inference('sup-', [status(thm)], ['37', '38'])).
% 0.41/0.58  thf('40', plain, (![X11 : $i]: (r1_tarski @ k1_xboole_0 @ X11)),
% 0.41/0.58      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.41/0.58  thf('41', plain,
% 0.41/0.58      (![X9 : $i, X10 : $i]:
% 0.41/0.58         (((k3_xboole_0 @ X9 @ X10) = (X9)) | ~ (r1_tarski @ X9 @ X10))),
% 0.41/0.58      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.41/0.58  thf('42', plain,
% 0.41/0.58      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.41/0.58      inference('sup-', [status(thm)], ['40', '41'])).
% 0.41/0.58  thf('43', plain,
% 0.41/0.58      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.41/0.58      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.41/0.58  thf('44', plain,
% 0.41/0.58      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.41/0.58      inference('sup+', [status(thm)], ['42', '43'])).
% 0.41/0.58  thf('45', plain,
% 0.41/0.58      (![X4 : $i, X5 : $i]:
% 0.41/0.58         ((k4_xboole_0 @ X4 @ X5)
% 0.41/0.58           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 0.41/0.58      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.41/0.58  thf('46', plain,
% 0.41/0.58      (![X0 : $i]:
% 0.41/0.58         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.41/0.58      inference('sup+', [status(thm)], ['44', '45'])).
% 0.41/0.58  thf(t5_boole, axiom,
% 0.41/0.58    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.41/0.58  thf('47', plain, (![X12 : $i]: ((k5_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.41/0.58      inference('cnf', [status(esa)], [t5_boole])).
% 0.41/0.58  thf('48', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.41/0.58      inference('sup+', [status(thm)], ['46', '47'])).
% 0.41/0.58  thf('49', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 0.41/0.58      inference('demod', [status(thm)], ['39', '48'])).
% 0.41/0.58  thf('50', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.41/0.58      inference('demod', [status(thm)], ['36', '49'])).
% 0.41/0.58  thf('51', plain,
% 0.41/0.58      (![X53 : $i, X54 : $i]:
% 0.41/0.58         (~ (m1_subset_1 @ X53 @ X54)
% 0.41/0.58          | (r2_hidden @ X53 @ X54)
% 0.41/0.58          | (v1_xboole_0 @ X54))),
% 0.41/0.58      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.41/0.58  thf('52', plain,
% 0.41/0.58      (![X0 : $i]:
% 0.41/0.58         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 0.41/0.58          | (r2_hidden @ X0 @ (k1_zfmisc_1 @ X0)))),
% 0.41/0.58      inference('sup-', [status(thm)], ['50', '51'])).
% 0.41/0.58  thf('53', plain, (![X61 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X61))),
% 0.41/0.58      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.41/0.58  thf('54', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.41/0.58      inference('clc', [status(thm)], ['52', '53'])).
% 0.41/0.58  thf('55', plain,
% 0.41/0.58      (![X47 : $i, X49 : $i]:
% 0.41/0.58         ((r1_tarski @ X49 @ X47) | ~ (r2_hidden @ X49 @ (k1_zfmisc_1 @ X47)))),
% 0.41/0.58      inference('simplify', [status(thm)], ['5'])).
% 0.41/0.58  thf('56', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.41/0.58      inference('sup-', [status(thm)], ['54', '55'])).
% 0.41/0.58  thf('57', plain,
% 0.41/0.58      (![X9 : $i, X10 : $i]:
% 0.41/0.58         (((k3_xboole_0 @ X9 @ X10) = (X9)) | ~ (r1_tarski @ X9 @ X10))),
% 0.41/0.58      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.41/0.58  thf('58', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.41/0.58      inference('sup-', [status(thm)], ['56', '57'])).
% 0.41/0.58  thf('59', plain,
% 0.41/0.58      (![X0 : $i, X1 : $i]:
% 0.41/0.58         ((k4_xboole_0 @ X0 @ X1)
% 0.41/0.58           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.41/0.58      inference('sup+', [status(thm)], ['10', '11'])).
% 0.41/0.58  thf('60', plain,
% 0.41/0.58      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.41/0.58      inference('sup+', [status(thm)], ['58', '59'])).
% 0.41/0.58  thf(t92_xboole_1, axiom,
% 0.41/0.58    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.41/0.58  thf('61', plain, (![X16 : $i]: ((k5_xboole_0 @ X16 @ X16) = (k1_xboole_0))),
% 0.41/0.58      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.41/0.58  thf('62', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.41/0.58      inference('sup+', [status(thm)], ['60', '61'])).
% 0.41/0.58  thf('63', plain,
% 0.41/0.58      (((k1_xboole_0) = (k3_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B)))),
% 0.41/0.58      inference('demod', [status(thm)], ['26', '62'])).
% 0.41/0.58  thf('64', plain,
% 0.41/0.58      (![X0 : $i, X1 : $i]:
% 0.41/0.58         ((k4_xboole_0 @ X0 @ X1)
% 0.41/0.58           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.41/0.58      inference('sup+', [status(thm)], ['10', '11'])).
% 0.41/0.58  thf('65', plain,
% 0.41/0.58      (((k4_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_B)
% 0.41/0.58         = (k5_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ k1_xboole_0))),
% 0.41/0.58      inference('sup+', [status(thm)], ['63', '64'])).
% 0.41/0.58  thf('66', plain,
% 0.41/0.58      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.41/0.58      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.41/0.58  thf('67', plain,
% 0.41/0.58      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.41/0.58      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.41/0.58  thf('68', plain, (![X12 : $i]: ((k5_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.41/0.58      inference('cnf', [status(esa)], [t5_boole])).
% 0.41/0.58  thf('69', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.41/0.58      inference('sup+', [status(thm)], ['67', '68'])).
% 0.41/0.58  thf('70', plain,
% 0.41/0.58      (((k4_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_B)
% 0.41/0.58         = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.41/0.58      inference('demod', [status(thm)], ['65', '66', '69'])).
% 0.41/0.58  thf(t94_xboole_1, axiom,
% 0.41/0.58    (![A:$i,B:$i]:
% 0.41/0.58     ( ( k2_xboole_0 @ A @ B ) =
% 0.41/0.58       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.41/0.58  thf('71', plain,
% 0.41/0.58      (![X17 : $i, X18 : $i]:
% 0.41/0.58         ((k2_xboole_0 @ X17 @ X18)
% 0.41/0.58           = (k5_xboole_0 @ (k5_xboole_0 @ X17 @ X18) @ 
% 0.41/0.58              (k3_xboole_0 @ X17 @ X18)))),
% 0.41/0.58      inference('cnf', [status(esa)], [t94_xboole_1])).
% 0.41/0.58  thf(l51_zfmisc_1, axiom,
% 0.41/0.58    (![A:$i,B:$i]:
% 0.41/0.58     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.41/0.58  thf('72', plain,
% 0.41/0.58      (![X51 : $i, X52 : $i]:
% 0.41/0.58         ((k3_tarski @ (k2_tarski @ X51 @ X52)) = (k2_xboole_0 @ X51 @ X52))),
% 0.41/0.58      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.41/0.58  thf(t91_xboole_1, axiom,
% 0.41/0.58    (![A:$i,B:$i,C:$i]:
% 0.41/0.58     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.41/0.58       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.41/0.58  thf('73', plain,
% 0.41/0.58      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.41/0.58         ((k5_xboole_0 @ (k5_xboole_0 @ X13 @ X14) @ X15)
% 0.41/0.58           = (k5_xboole_0 @ X13 @ (k5_xboole_0 @ X14 @ X15)))),
% 0.41/0.58      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.41/0.58  thf('74', plain,
% 0.41/0.58      (![X0 : $i, X1 : $i]:
% 0.41/0.58         ((k4_xboole_0 @ X0 @ X1)
% 0.41/0.58           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.41/0.58      inference('sup+', [status(thm)], ['10', '11'])).
% 0.41/0.58  thf('75', plain,
% 0.41/0.58      (![X17 : $i, X18 : $i]:
% 0.41/0.58         ((k3_tarski @ (k2_tarski @ X17 @ X18))
% 0.41/0.58           = (k5_xboole_0 @ X17 @ (k4_xboole_0 @ X18 @ X17)))),
% 0.41/0.58      inference('demod', [status(thm)], ['71', '72', '73', '74'])).
% 0.41/0.58  thf('76', plain,
% 0.41/0.58      (((k3_tarski @ (k2_tarski @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B)))
% 0.41/0.58         = (k5_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B)))),
% 0.41/0.58      inference('sup+', [status(thm)], ['70', '75'])).
% 0.41/0.58  thf('77', plain,
% 0.41/0.58      (![X17 : $i, X18 : $i]:
% 0.41/0.58         ((k3_tarski @ (k2_tarski @ X17 @ X18))
% 0.41/0.58           = (k5_xboole_0 @ X17 @ (k4_xboole_0 @ X18 @ X17)))),
% 0.41/0.58      inference('demod', [status(thm)], ['71', '72', '73', '74'])).
% 0.41/0.58  thf('78', plain,
% 0.41/0.58      (((k3_tarski @ (k2_tarski @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B)))
% 0.41/0.58         = (k3_tarski @ (k2_tarski @ sk_B @ sk_A)))),
% 0.41/0.58      inference('demod', [status(thm)], ['76', '77'])).
% 0.41/0.58  thf('79', plain,
% 0.41/0.58      (((k4_xboole_0 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_B @ sk_A))),
% 0.41/0.58      inference('demod', [status(thm)], ['13', '14'])).
% 0.41/0.58  thf('80', plain, (![X16 : $i]: ((k5_xboole_0 @ X16 @ X16) = (k1_xboole_0))),
% 0.41/0.58      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.41/0.58  thf('81', plain,
% 0.41/0.58      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.41/0.58         ((k5_xboole_0 @ (k5_xboole_0 @ X13 @ X14) @ X15)
% 0.41/0.58           = (k5_xboole_0 @ X13 @ (k5_xboole_0 @ X14 @ X15)))),
% 0.41/0.58      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.41/0.58  thf('82', plain,
% 0.41/0.58      (![X0 : $i, X1 : $i]:
% 0.41/0.58         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.41/0.58           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.41/0.58      inference('sup+', [status(thm)], ['80', '81'])).
% 0.41/0.58  thf('83', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.41/0.58      inference('sup+', [status(thm)], ['67', '68'])).
% 0.41/0.58  thf('84', plain,
% 0.41/0.58      (![X0 : $i, X1 : $i]:
% 0.41/0.58         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.41/0.58      inference('demod', [status(thm)], ['82', '83'])).
% 0.41/0.58  thf('85', plain,
% 0.41/0.58      (((sk_A) = (k5_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B)))),
% 0.41/0.58      inference('sup+', [status(thm)], ['79', '84'])).
% 0.41/0.58  thf('86', plain,
% 0.41/0.58      (![X17 : $i, X18 : $i]:
% 0.41/0.58         ((k3_tarski @ (k2_tarski @ X17 @ X18))
% 0.41/0.58           = (k5_xboole_0 @ X17 @ (k4_xboole_0 @ X18 @ X17)))),
% 0.41/0.58      inference('demod', [status(thm)], ['71', '72', '73', '74'])).
% 0.41/0.58  thf('87', plain, (((sk_A) = (k3_tarski @ (k2_tarski @ sk_B @ sk_A)))),
% 0.41/0.58      inference('demod', [status(thm)], ['85', '86'])).
% 0.41/0.58  thf('88', plain,
% 0.41/0.58      (((k3_tarski @ (k2_tarski @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B))) = (sk_A))),
% 0.41/0.58      inference('demod', [status(thm)], ['78', '87'])).
% 0.41/0.58  thf('89', plain,
% 0.41/0.58      (((k4_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 0.41/0.58         != (k2_subset_1 @ sk_A))),
% 0.41/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.58  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.41/0.58  thf('90', plain, (![X56 : $i]: ((k2_subset_1 @ X56) = (X56))),
% 0.41/0.58      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.41/0.58  thf('91', plain,
% 0.41/0.58      (((k4_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)) != (sk_A))),
% 0.41/0.58      inference('demod', [status(thm)], ['89', '90'])).
% 0.41/0.58  thf('92', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.41/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.58  thf('93', plain,
% 0.41/0.58      (![X57 : $i, X58 : $i]:
% 0.41/0.58         (((k3_subset_1 @ X57 @ X58) = (k4_xboole_0 @ X57 @ X58))
% 0.41/0.58          | ~ (m1_subset_1 @ X58 @ (k1_zfmisc_1 @ X57)))),
% 0.41/0.58      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.41/0.58  thf('94', plain,
% 0.41/0.58      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.41/0.58      inference('sup-', [status(thm)], ['92', '93'])).
% 0.41/0.58  thf('95', plain,
% 0.41/0.58      (((k4_subset_1 @ sk_A @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B)) != (sk_A))),
% 0.41/0.58      inference('demod', [status(thm)], ['91', '94'])).
% 0.41/0.58  thf('96', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.41/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.58  thf('97', plain,
% 0.41/0.58      (![X59 : $i, X60 : $i]:
% 0.41/0.58         ((m1_subset_1 @ (k3_subset_1 @ X59 @ X60) @ (k1_zfmisc_1 @ X59))
% 0.41/0.58          | ~ (m1_subset_1 @ X60 @ (k1_zfmisc_1 @ X59)))),
% 0.41/0.58      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.41/0.58  thf('98', plain,
% 0.41/0.58      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.41/0.58      inference('sup-', [status(thm)], ['96', '97'])).
% 0.41/0.58  thf('99', plain,
% 0.41/0.58      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.41/0.58      inference('sup-', [status(thm)], ['92', '93'])).
% 0.41/0.58  thf('100', plain,
% 0.41/0.58      ((m1_subset_1 @ (k4_xboole_0 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.41/0.58      inference('demod', [status(thm)], ['98', '99'])).
% 0.41/0.58  thf('101', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.41/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.58  thf(redefinition_k4_subset_1, axiom,
% 0.41/0.58    (![A:$i,B:$i,C:$i]:
% 0.41/0.58     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.41/0.58         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.41/0.58       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.41/0.58  thf('102', plain,
% 0.41/0.58      (![X62 : $i, X63 : $i, X64 : $i]:
% 0.41/0.58         (~ (m1_subset_1 @ X62 @ (k1_zfmisc_1 @ X63))
% 0.41/0.58          | ~ (m1_subset_1 @ X64 @ (k1_zfmisc_1 @ X63))
% 0.41/0.58          | ((k4_subset_1 @ X63 @ X62 @ X64) = (k2_xboole_0 @ X62 @ X64)))),
% 0.41/0.58      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.41/0.58  thf('103', plain,
% 0.41/0.58      (![X51 : $i, X52 : $i]:
% 0.41/0.58         ((k3_tarski @ (k2_tarski @ X51 @ X52)) = (k2_xboole_0 @ X51 @ X52))),
% 0.41/0.58      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.41/0.58  thf('104', plain,
% 0.41/0.58      (![X62 : $i, X63 : $i, X64 : $i]:
% 0.41/0.58         (~ (m1_subset_1 @ X62 @ (k1_zfmisc_1 @ X63))
% 0.41/0.58          | ~ (m1_subset_1 @ X64 @ (k1_zfmisc_1 @ X63))
% 0.41/0.58          | ((k4_subset_1 @ X63 @ X62 @ X64)
% 0.41/0.58              = (k3_tarski @ (k2_tarski @ X62 @ X64))))),
% 0.41/0.58      inference('demod', [status(thm)], ['102', '103'])).
% 0.41/0.58  thf('105', plain,
% 0.41/0.58      (![X0 : $i]:
% 0.41/0.58         (((k4_subset_1 @ sk_A @ sk_B @ X0)
% 0.41/0.58            = (k3_tarski @ (k2_tarski @ sk_B @ X0)))
% 0.41/0.58          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 0.41/0.58      inference('sup-', [status(thm)], ['101', '104'])).
% 0.41/0.58  thf('106', plain,
% 0.41/0.58      (((k4_subset_1 @ sk_A @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B))
% 0.41/0.58         = (k3_tarski @ (k2_tarski @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B))))),
% 0.41/0.58      inference('sup-', [status(thm)], ['100', '105'])).
% 0.41/0.58  thf('107', plain,
% 0.41/0.58      (((k3_tarski @ (k2_tarski @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B)))
% 0.41/0.58         != (sk_A))),
% 0.41/0.58      inference('demod', [status(thm)], ['95', '106'])).
% 0.41/0.58  thf('108', plain, ($false),
% 0.41/0.58      inference('simplify_reflect-', [status(thm)], ['88', '107'])).
% 0.41/0.58  
% 0.41/0.58  % SZS output end Refutation
% 0.41/0.58  
% 0.41/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
