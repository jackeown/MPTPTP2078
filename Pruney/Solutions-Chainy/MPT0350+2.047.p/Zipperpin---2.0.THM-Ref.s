%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.69CNAxWA0W

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:51 EST 2020

% Result     : Theorem 12.54s
% Output     : Refutation 12.54s
% Verified   : 
% Statistics : Number of formulae       :  183 ( 909 expanded)
%              Number of leaves         :   37 ( 321 expanded)
%              Depth                    :   17
%              Number of atoms          : 1322 (7281 expanded)
%              Number of equality atoms :  124 ( 774 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

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
    ! [X60: $i,X61: $i] :
      ( ~ ( m1_subset_1 @ X60 @ X61 )
      | ( r2_hidden @ X60 @ X61 )
      | ( v1_xboole_0 @ X61 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('2',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('3',plain,(
    ! [X66: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X66 ) ) ),
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
    ! [X54: $i,X55: $i,X56: $i] :
      ( ~ ( r2_hidden @ X56 @ X55 )
      | ( r1_tarski @ X56 @ X54 )
      | ( X55
       != ( k1_zfmisc_1 @ X54 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('6',plain,(
    ! [X54: $i,X56: $i] :
      ( ( r1_tarski @ X56 @ X54 )
      | ~ ( r2_hidden @ X56 @ ( k1_zfmisc_1 @ X54 ) ) ) ),
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
    ! [X16: $i,X17: $i] :
      ( ( ( k3_xboole_0 @ X16 @ X17 )
        = X16 )
      | ~ ( r1_tarski @ X16 @ X17 ) ) ),
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
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
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
    ! [X64: $i,X65: $i] :
      ( ( ( k3_subset_1 @ X64 @ X65 )
        = ( k4_xboole_0 @ X64 @ X65 ) )
      | ~ ( m1_subset_1 @ X65 @ ( k1_zfmisc_1 @ X64 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('16',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('17',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('18',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['13','16','17'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('19',plain,(
    ! [X10: $i] :
      ( ( k3_xboole_0 @ X10 @ X10 )
      = X10 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('20',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('23',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('24',plain,(
    ! [X20: $i] :
      ( ( k5_xboole_0 @ X20 @ k1_xboole_0 )
      = X20 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['22','25'])).

thf(t94_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('27',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k2_xboole_0 @ X24 @ X25 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X24 @ X25 ) @ ( k3_xboole_0 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t94_xboole_1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('28',plain,(
    ! [X58: $i,X59: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X58 @ X59 ) )
      = ( k2_xboole_0 @ X58 @ X59 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('29',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X21 @ X22 ) @ X23 )
      = ( k5_xboole_0 @ X21 @ ( k5_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('31',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X24 @ X25 ) )
      = ( k5_xboole_0 @ X24 @ ( k4_xboole_0 @ X25 @ X24 ) ) ) ),
    inference(demod,[status(thm)],['27','28','29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X0 @ k1_xboole_0 ) )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['26','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X0 @ k1_xboole_0 ) )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('35',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X18 @ X19 ) @ X18 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('36',plain,(
    ! [X53: $i,X54: $i,X55: $i] :
      ( ~ ( r1_tarski @ X53 @ X54 )
      | ( r2_hidden @ X53 @ X55 )
      | ( X55
       != ( k1_zfmisc_1 @ X54 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('37',plain,(
    ! [X53: $i,X54: $i] :
      ( ( r2_hidden @ X53 @ ( k1_zfmisc_1 @ X54 ) )
      | ~ ( r1_tarski @ X53 @ X54 ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','37'])).

thf('39',plain,(
    ! [X60: $i,X61: $i] :
      ( ~ ( r2_hidden @ X60 @ X61 )
      | ( m1_subset_1 @ X60 @ X61 )
      | ( v1_xboole_0 @ X61 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X66: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X66 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_tarski @ ( k2_tarski @ X0 @ k1_xboole_0 ) ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['34','42'])).

thf('44',plain,(
    ! [X20: $i] :
      ( ( k5_xboole_0 @ X20 @ k1_xboole_0 )
      = X20 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('45',plain,(
    ! [X10: $i] :
      ( ( k3_xboole_0 @ X10 @ X10 )
      = X10 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t112_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ B ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ A @ C ) @ B ) ) )).

thf('46',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X13 @ X15 ) @ ( k3_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X13 @ X14 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[t112_xboole_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['44','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X0 @ k1_xboole_0 ) )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('54',plain,(
    ! [X10: $i] :
      ( ( k3_xboole_0 @ X10 @ X10 )
      = X10 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X0 @ k1_xboole_0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['52','53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['43','55'])).

thf('57',plain,(
    ! [X64: $i,X65: $i] :
      ( ( ( k3_subset_1 @ X64 @ X65 )
        = ( k4_xboole_0 @ X64 @ X65 ) )
      | ~ ( m1_subset_1 @ X65 @ ( k1_zfmisc_1 @ X64 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['21','58'])).

thf('60',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X21 @ X22 ) @ X23 )
      = ( k5_xboole_0 @ X21 @ ( k5_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('61',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X2 @ X1 ) )
      = ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k3_subset_1 @ X0 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['59','62'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('64',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ( X9
        = ( k4_xboole_0 @ X5 @ X6 ) )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X5 )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('65',plain,(
    ! [X10: $i] :
      ( ( k3_xboole_0 @ X10 @ X10 )
      = X10 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['22','25'])).

thf('67',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ~ ( r2_hidden @ X8 @ X6 )
      | ( X7
       != ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('68',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['66','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['65','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( k1_xboole_0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['64','71'])).

thf('73',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X18 @ X19 ) @ X18 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('74',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k3_xboole_0 @ X16 @ X17 )
        = X16 )
      | ~ ( r1_tarski @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('79',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X13 @ X15 ) @ ( k3_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X13 @ X14 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[t112_xboole_1])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['80','81','82'])).

thf('84',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('85',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( r2_hidden @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['77','85'])).

thf('87',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ( r2_hidden @ X8 @ X5 )
      | ( X7
       != ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('88',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ( r2_hidden @ X8 @ X5 )
      | ~ ( r2_hidden @ X8 @ ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['87'])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['86','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k3_subset_1 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ ( k3_subset_1 @ X0 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['72','91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X0 @ k1_xboole_0 ) )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X0 @ k1_xboole_0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['52','53','54'])).

thf('95',plain,(
    ! [X0: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['92','95'])).

thf('97',plain,(
    ! [X20: $i] :
      ( ( k5_xboole_0 @ X20 @ k1_xboole_0 )
      = X20 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k3_subset_1 @ X0 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['63','98'])).

thf('100',plain,
    ( sk_A
    = ( k5_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['18','99'])).

thf('101',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['13','16','17'])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('103',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_A )
    = ( k3_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['101','102'])).

thf('104',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['7','8'])).

thf('105',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('106',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_A )
    = ( k5_xboole_0 @ sk_B @ sk_B ) ),
    inference('sup+',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('108',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_A )
    = ( k4_xboole_0 @ sk_B @ sk_B ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_B )
    = ( k3_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['103','108'])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('111',plain,
    ( ( k3_subset_1 @ sk_B @ sk_B )
    = ( k3_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['92','95'])).

thf('113',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('118',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('119',plain,
    ( ( k4_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ k1_xboole_0 )
    = ( k4_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup+',[status(thm)],['113','118'])).

thf('120',plain,(
    ! [X0: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('121',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X24 @ X25 ) )
      = ( k5_xboole_0 @ X24 @ ( k4_xboole_0 @ X25 @ X24 ) ) ) ),
    inference(demod,[status(thm)],['27','28','29','30'])).

thf('123',plain,
    ( ( k3_tarski @ ( k2_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) )
    = ( k5_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['121','122'])).

thf('124',plain,
    ( ( k3_tarski @ ( k2_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) )
    = sk_A ),
    inference('sup+',[status(thm)],['100','123'])).

thf('125',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
 != ( k2_subset_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('126',plain,(
    ! [X63: $i] :
      ( ( k2_subset_1 @ X63 )
      = X63 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('127',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
 != sk_A ),
    inference(demod,[status(thm)],['125','126'])).

thf('128',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('129',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X18 @ X19 ) @ X18 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('130',plain,(
    r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_A ),
    inference('sup+',[status(thm)],['128','129'])).

thf('131',plain,(
    ! [X53: $i,X54: $i] :
      ( ( r2_hidden @ X53 @ ( k1_zfmisc_1 @ X54 ) )
      | ~ ( r1_tarski @ X53 @ X54 ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('132',plain,(
    r2_hidden @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,(
    ! [X60: $i,X61: $i] :
      ( ~ ( r2_hidden @ X60 @ X61 )
      | ( m1_subset_1 @ X60 @ X61 )
      | ( v1_xboole_0 @ X61 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('134',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,(
    ! [X66: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X66 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('136',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['134','135'])).

thf('137',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('138',plain,(
    ! [X67: $i,X68: $i,X69: $i] :
      ( ~ ( m1_subset_1 @ X67 @ ( k1_zfmisc_1 @ X68 ) )
      | ~ ( m1_subset_1 @ X69 @ ( k1_zfmisc_1 @ X68 ) )
      | ( ( k4_subset_1 @ X68 @ X67 @ X69 )
        = ( k2_xboole_0 @ X67 @ X69 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('139',plain,(
    ! [X58: $i,X59: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X58 @ X59 ) )
      = ( k2_xboole_0 @ X58 @ X59 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('140',plain,(
    ! [X67: $i,X68: $i,X69: $i] :
      ( ~ ( m1_subset_1 @ X67 @ ( k1_zfmisc_1 @ X68 ) )
      | ~ ( m1_subset_1 @ X69 @ ( k1_zfmisc_1 @ X68 ) )
      | ( ( k4_subset_1 @ X68 @ X67 @ X69 )
        = ( k3_tarski @ ( k2_tarski @ X67 @ X69 ) ) ) ) ),
    inference(demod,[status(thm)],['138','139'])).

thf('141',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ sk_A @ sk_B @ X0 )
        = ( k3_tarski @ ( k2_tarski @ sk_B @ X0 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['137','140'])).

thf('142',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k3_tarski @ ( k2_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['136','141'])).

thf('143',plain,(
    ( k3_tarski @ ( k2_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) )
 != sk_A ),
    inference(demod,[status(thm)],['127','142'])).

thf('144',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['124','143'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.69CNAxWA0W
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:36:23 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 12.54/12.75  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 12.54/12.75  % Solved by: fo/fo7.sh
% 12.54/12.75  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 12.54/12.75  % done 17301 iterations in 12.293s
% 12.54/12.75  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 12.54/12.75  % SZS output start Refutation
% 12.54/12.75  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 12.54/12.75  thf(sk_B_type, type, sk_B: $i).
% 12.54/12.75  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 12.54/12.75  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 12.54/12.75  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 12.54/12.75  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 12.54/12.75  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 12.54/12.75  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 12.54/12.75  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 12.54/12.75  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 12.54/12.75  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 12.54/12.75  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 12.54/12.75  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 12.54/12.75  thf(sk_A_type, type, sk_A: $i).
% 12.54/12.75  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 12.54/12.75  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 12.54/12.75  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 12.54/12.75  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 12.54/12.75  thf(t25_subset_1, conjecture,
% 12.54/12.75    (![A:$i,B:$i]:
% 12.54/12.75     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 12.54/12.75       ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) ) =
% 12.54/12.75         ( k2_subset_1 @ A ) ) ))).
% 12.54/12.75  thf(zf_stmt_0, negated_conjecture,
% 12.54/12.75    (~( ![A:$i,B:$i]:
% 12.54/12.75        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 12.54/12.75          ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) ) =
% 12.54/12.75            ( k2_subset_1 @ A ) ) ) )),
% 12.54/12.75    inference('cnf.neg', [status(esa)], [t25_subset_1])).
% 12.54/12.75  thf('0', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 12.54/12.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.54/12.75  thf(d2_subset_1, axiom,
% 12.54/12.75    (![A:$i,B:$i]:
% 12.54/12.75     ( ( ( v1_xboole_0 @ A ) =>
% 12.54/12.75         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 12.54/12.75       ( ( ~( v1_xboole_0 @ A ) ) =>
% 12.54/12.75         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 12.54/12.75  thf('1', plain,
% 12.54/12.75      (![X60 : $i, X61 : $i]:
% 12.54/12.75         (~ (m1_subset_1 @ X60 @ X61)
% 12.54/12.75          | (r2_hidden @ X60 @ X61)
% 12.54/12.75          | (v1_xboole_0 @ X61))),
% 12.54/12.75      inference('cnf', [status(esa)], [d2_subset_1])).
% 12.54/12.75  thf('2', plain,
% 12.54/12.75      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 12.54/12.75        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 12.54/12.75      inference('sup-', [status(thm)], ['0', '1'])).
% 12.54/12.75  thf(fc1_subset_1, axiom,
% 12.54/12.75    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 12.54/12.75  thf('3', plain, (![X66 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X66))),
% 12.54/12.75      inference('cnf', [status(esa)], [fc1_subset_1])).
% 12.54/12.75  thf('4', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 12.54/12.75      inference('clc', [status(thm)], ['2', '3'])).
% 12.54/12.75  thf(d1_zfmisc_1, axiom,
% 12.54/12.75    (![A:$i,B:$i]:
% 12.54/12.75     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 12.54/12.75       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 12.54/12.75  thf('5', plain,
% 12.54/12.75      (![X54 : $i, X55 : $i, X56 : $i]:
% 12.54/12.75         (~ (r2_hidden @ X56 @ X55)
% 12.54/12.75          | (r1_tarski @ X56 @ X54)
% 12.54/12.75          | ((X55) != (k1_zfmisc_1 @ X54)))),
% 12.54/12.75      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 12.54/12.75  thf('6', plain,
% 12.54/12.75      (![X54 : $i, X56 : $i]:
% 12.54/12.75         ((r1_tarski @ X56 @ X54) | ~ (r2_hidden @ X56 @ (k1_zfmisc_1 @ X54)))),
% 12.54/12.75      inference('simplify', [status(thm)], ['5'])).
% 12.54/12.75  thf('7', plain, ((r1_tarski @ sk_B @ sk_A)),
% 12.54/12.75      inference('sup-', [status(thm)], ['4', '6'])).
% 12.54/12.75  thf(t28_xboole_1, axiom,
% 12.54/12.75    (![A:$i,B:$i]:
% 12.54/12.75     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 12.54/12.75  thf('8', plain,
% 12.54/12.75      (![X16 : $i, X17 : $i]:
% 12.54/12.75         (((k3_xboole_0 @ X16 @ X17) = (X16)) | ~ (r1_tarski @ X16 @ X17))),
% 12.54/12.75      inference('cnf', [status(esa)], [t28_xboole_1])).
% 12.54/12.75  thf('9', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 12.54/12.75      inference('sup-', [status(thm)], ['7', '8'])).
% 12.54/12.75  thf(commutativity_k3_xboole_0, axiom,
% 12.54/12.75    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 12.54/12.75  thf('10', plain,
% 12.54/12.75      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 12.54/12.75      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 12.54/12.75  thf(t100_xboole_1, axiom,
% 12.54/12.75    (![A:$i,B:$i]:
% 12.54/12.75     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 12.54/12.75  thf('11', plain,
% 12.54/12.75      (![X11 : $i, X12 : $i]:
% 12.54/12.75         ((k4_xboole_0 @ X11 @ X12)
% 12.54/12.75           = (k5_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12)))),
% 12.54/12.75      inference('cnf', [status(esa)], [t100_xboole_1])).
% 12.54/12.75  thf('12', plain,
% 12.54/12.75      (![X0 : $i, X1 : $i]:
% 12.54/12.75         ((k4_xboole_0 @ X0 @ X1)
% 12.54/12.75           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 12.54/12.75      inference('sup+', [status(thm)], ['10', '11'])).
% 12.54/12.75  thf('13', plain,
% 12.54/12.75      (((k4_xboole_0 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 12.54/12.75      inference('sup+', [status(thm)], ['9', '12'])).
% 12.54/12.75  thf('14', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 12.54/12.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.54/12.75  thf(d5_subset_1, axiom,
% 12.54/12.75    (![A:$i,B:$i]:
% 12.54/12.75     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 12.54/12.75       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 12.54/12.75  thf('15', plain,
% 12.54/12.75      (![X64 : $i, X65 : $i]:
% 12.54/12.75         (((k3_subset_1 @ X64 @ X65) = (k4_xboole_0 @ X64 @ X65))
% 12.54/12.75          | ~ (m1_subset_1 @ X65 @ (k1_zfmisc_1 @ X64)))),
% 12.54/12.75      inference('cnf', [status(esa)], [d5_subset_1])).
% 12.54/12.75  thf('16', plain,
% 12.54/12.75      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 12.54/12.75      inference('sup-', [status(thm)], ['14', '15'])).
% 12.54/12.75  thf(commutativity_k5_xboole_0, axiom,
% 12.54/12.75    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 12.54/12.75  thf('17', plain,
% 12.54/12.75      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 12.54/12.75      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 12.54/12.75  thf('18', plain,
% 12.54/12.75      (((k3_subset_1 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_B @ sk_A))),
% 12.54/12.75      inference('demod', [status(thm)], ['13', '16', '17'])).
% 12.54/12.75  thf(idempotence_k3_xboole_0, axiom,
% 12.54/12.75    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 12.54/12.75  thf('19', plain, (![X10 : $i]: ((k3_xboole_0 @ X10 @ X10) = (X10))),
% 12.54/12.75      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 12.54/12.75  thf('20', plain,
% 12.54/12.75      (![X11 : $i, X12 : $i]:
% 12.54/12.75         ((k4_xboole_0 @ X11 @ X12)
% 12.54/12.75           = (k5_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12)))),
% 12.54/12.75      inference('cnf', [status(esa)], [t100_xboole_1])).
% 12.54/12.75  thf('21', plain,
% 12.54/12.75      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 12.54/12.75      inference('sup+', [status(thm)], ['19', '20'])).
% 12.54/12.75  thf('22', plain,
% 12.54/12.75      (![X11 : $i, X12 : $i]:
% 12.54/12.75         ((k4_xboole_0 @ X11 @ X12)
% 12.54/12.75           = (k5_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12)))),
% 12.54/12.75      inference('cnf', [status(esa)], [t100_xboole_1])).
% 12.54/12.75  thf('23', plain,
% 12.54/12.75      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 12.54/12.75      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 12.54/12.75  thf(t5_boole, axiom,
% 12.54/12.75    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 12.54/12.75  thf('24', plain, (![X20 : $i]: ((k5_xboole_0 @ X20 @ k1_xboole_0) = (X20))),
% 12.54/12.75      inference('cnf', [status(esa)], [t5_boole])).
% 12.54/12.75  thf('25', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 12.54/12.75      inference('sup+', [status(thm)], ['23', '24'])).
% 12.54/12.75  thf('26', plain,
% 12.54/12.75      (![X0 : $i]:
% 12.54/12.75         ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 12.54/12.75      inference('sup+', [status(thm)], ['22', '25'])).
% 12.54/12.75  thf(t94_xboole_1, axiom,
% 12.54/12.75    (![A:$i,B:$i]:
% 12.54/12.75     ( ( k2_xboole_0 @ A @ B ) =
% 12.54/12.75       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 12.54/12.75  thf('27', plain,
% 12.54/12.75      (![X24 : $i, X25 : $i]:
% 12.54/12.75         ((k2_xboole_0 @ X24 @ X25)
% 12.54/12.75           = (k5_xboole_0 @ (k5_xboole_0 @ X24 @ X25) @ 
% 12.54/12.75              (k3_xboole_0 @ X24 @ X25)))),
% 12.54/12.75      inference('cnf', [status(esa)], [t94_xboole_1])).
% 12.54/12.75  thf(l51_zfmisc_1, axiom,
% 12.54/12.75    (![A:$i,B:$i]:
% 12.54/12.75     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 12.54/12.75  thf('28', plain,
% 12.54/12.75      (![X58 : $i, X59 : $i]:
% 12.54/12.75         ((k3_tarski @ (k2_tarski @ X58 @ X59)) = (k2_xboole_0 @ X58 @ X59))),
% 12.54/12.75      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 12.54/12.75  thf(t91_xboole_1, axiom,
% 12.54/12.75    (![A:$i,B:$i,C:$i]:
% 12.54/12.75     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 12.54/12.75       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 12.54/12.75  thf('29', plain,
% 12.54/12.75      (![X21 : $i, X22 : $i, X23 : $i]:
% 12.54/12.75         ((k5_xboole_0 @ (k5_xboole_0 @ X21 @ X22) @ X23)
% 12.54/12.75           = (k5_xboole_0 @ X21 @ (k5_xboole_0 @ X22 @ X23)))),
% 12.54/12.75      inference('cnf', [status(esa)], [t91_xboole_1])).
% 12.54/12.75  thf('30', plain,
% 12.54/12.75      (![X0 : $i, X1 : $i]:
% 12.54/12.75         ((k4_xboole_0 @ X0 @ X1)
% 12.54/12.75           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 12.54/12.75      inference('sup+', [status(thm)], ['10', '11'])).
% 12.54/12.75  thf('31', plain,
% 12.54/12.75      (![X24 : $i, X25 : $i]:
% 12.54/12.75         ((k3_tarski @ (k2_tarski @ X24 @ X25))
% 12.54/12.75           = (k5_xboole_0 @ X24 @ (k4_xboole_0 @ X25 @ X24)))),
% 12.54/12.75      inference('demod', [status(thm)], ['27', '28', '29', '30'])).
% 12.54/12.75  thf('32', plain,
% 12.54/12.75      (![X0 : $i]:
% 12.54/12.75         ((k3_tarski @ (k2_tarski @ X0 @ k1_xboole_0))
% 12.54/12.75           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ k1_xboole_0 @ X0)))),
% 12.54/12.75      inference('sup+', [status(thm)], ['26', '31'])).
% 12.54/12.75  thf('33', plain,
% 12.54/12.75      (![X0 : $i, X1 : $i]:
% 12.54/12.75         ((k4_xboole_0 @ X0 @ X1)
% 12.54/12.75           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 12.54/12.75      inference('sup+', [status(thm)], ['10', '11'])).
% 12.54/12.75  thf('34', plain,
% 12.54/12.75      (![X0 : $i]:
% 12.54/12.75         ((k3_tarski @ (k2_tarski @ X0 @ k1_xboole_0))
% 12.54/12.75           = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 12.54/12.75      inference('demod', [status(thm)], ['32', '33'])).
% 12.54/12.75  thf(t36_xboole_1, axiom,
% 12.54/12.75    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 12.54/12.75  thf('35', plain,
% 12.54/12.75      (![X18 : $i, X19 : $i]: (r1_tarski @ (k4_xboole_0 @ X18 @ X19) @ X18)),
% 12.54/12.75      inference('cnf', [status(esa)], [t36_xboole_1])).
% 12.54/12.75  thf('36', plain,
% 12.54/12.75      (![X53 : $i, X54 : $i, X55 : $i]:
% 12.54/12.75         (~ (r1_tarski @ X53 @ X54)
% 12.54/12.75          | (r2_hidden @ X53 @ X55)
% 12.54/12.75          | ((X55) != (k1_zfmisc_1 @ X54)))),
% 12.54/12.75      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 12.54/12.75  thf('37', plain,
% 12.54/12.75      (![X53 : $i, X54 : $i]:
% 12.54/12.75         ((r2_hidden @ X53 @ (k1_zfmisc_1 @ X54)) | ~ (r1_tarski @ X53 @ X54))),
% 12.54/12.75      inference('simplify', [status(thm)], ['36'])).
% 12.54/12.75  thf('38', plain,
% 12.54/12.75      (![X0 : $i, X1 : $i]:
% 12.54/12.75         (r2_hidden @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 12.54/12.75      inference('sup-', [status(thm)], ['35', '37'])).
% 12.54/12.75  thf('39', plain,
% 12.54/12.75      (![X60 : $i, X61 : $i]:
% 12.54/12.75         (~ (r2_hidden @ X60 @ X61)
% 12.54/12.75          | (m1_subset_1 @ X60 @ X61)
% 12.54/12.75          | (v1_xboole_0 @ X61))),
% 12.54/12.75      inference('cnf', [status(esa)], [d2_subset_1])).
% 12.54/12.75  thf('40', plain,
% 12.54/12.75      (![X0 : $i, X1 : $i]:
% 12.54/12.75         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 12.54/12.75          | (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0)))),
% 12.54/12.75      inference('sup-', [status(thm)], ['38', '39'])).
% 12.54/12.75  thf('41', plain, (![X66 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X66))),
% 12.54/12.75      inference('cnf', [status(esa)], [fc1_subset_1])).
% 12.54/12.75  thf('42', plain,
% 12.54/12.75      (![X0 : $i, X1 : $i]:
% 12.54/12.75         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 12.54/12.75      inference('clc', [status(thm)], ['40', '41'])).
% 12.54/12.75  thf('43', plain,
% 12.54/12.75      (![X0 : $i]:
% 12.54/12.75         (m1_subset_1 @ (k3_tarski @ (k2_tarski @ X0 @ k1_xboole_0)) @ 
% 12.54/12.75          (k1_zfmisc_1 @ X0))),
% 12.54/12.75      inference('sup+', [status(thm)], ['34', '42'])).
% 12.54/12.75  thf('44', plain, (![X20 : $i]: ((k5_xboole_0 @ X20 @ k1_xboole_0) = (X20))),
% 12.54/12.75      inference('cnf', [status(esa)], [t5_boole])).
% 12.54/12.75  thf('45', plain, (![X10 : $i]: ((k3_xboole_0 @ X10 @ X10) = (X10))),
% 12.54/12.75      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 12.54/12.75  thf(t112_xboole_1, axiom,
% 12.54/12.75    (![A:$i,B:$i,C:$i]:
% 12.54/12.75     ( ( k5_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ B ) ) =
% 12.54/12.75       ( k3_xboole_0 @ ( k5_xboole_0 @ A @ C ) @ B ) ))).
% 12.54/12.75  thf('46', plain,
% 12.54/12.75      (![X13 : $i, X14 : $i, X15 : $i]:
% 12.54/12.75         ((k5_xboole_0 @ (k3_xboole_0 @ X13 @ X15) @ (k3_xboole_0 @ X14 @ X15))
% 12.54/12.75           = (k3_xboole_0 @ (k5_xboole_0 @ X13 @ X14) @ X15))),
% 12.54/12.75      inference('cnf', [status(esa)], [t112_xboole_1])).
% 12.54/12.75  thf('47', plain,
% 12.54/12.75      (![X0 : $i, X1 : $i]:
% 12.54/12.75         ((k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 12.54/12.75           = (k3_xboole_0 @ (k5_xboole_0 @ X0 @ X1) @ X0))),
% 12.54/12.75      inference('sup+', [status(thm)], ['45', '46'])).
% 12.54/12.75  thf('48', plain,
% 12.54/12.75      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 12.54/12.75      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 12.54/12.75  thf('49', plain,
% 12.54/12.75      (![X0 : $i, X1 : $i]:
% 12.54/12.75         ((k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 12.54/12.75           = (k3_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 12.54/12.75      inference('demod', [status(thm)], ['47', '48'])).
% 12.54/12.75  thf('50', plain,
% 12.54/12.75      (![X0 : $i, X1 : $i]:
% 12.54/12.75         ((k4_xboole_0 @ X0 @ X1)
% 12.54/12.75           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 12.54/12.75      inference('sup+', [status(thm)], ['10', '11'])).
% 12.54/12.75  thf('51', plain,
% 12.54/12.75      (![X0 : $i, X1 : $i]:
% 12.54/12.75         ((k4_xboole_0 @ X1 @ X0)
% 12.54/12.75           = (k3_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 12.54/12.75      inference('sup+', [status(thm)], ['49', '50'])).
% 12.54/12.75  thf('52', plain,
% 12.54/12.75      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 12.54/12.75      inference('sup+', [status(thm)], ['44', '51'])).
% 12.54/12.75  thf('53', plain,
% 12.54/12.75      (![X0 : $i]:
% 12.54/12.75         ((k3_tarski @ (k2_tarski @ X0 @ k1_xboole_0))
% 12.54/12.75           = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 12.54/12.75      inference('demod', [status(thm)], ['32', '33'])).
% 12.54/12.75  thf('54', plain, (![X10 : $i]: ((k3_xboole_0 @ X10 @ X10) = (X10))),
% 12.54/12.75      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 12.54/12.75  thf('55', plain,
% 12.54/12.75      (![X0 : $i]: ((k3_tarski @ (k2_tarski @ X0 @ k1_xboole_0)) = (X0))),
% 12.54/12.75      inference('demod', [status(thm)], ['52', '53', '54'])).
% 12.54/12.75  thf('56', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 12.54/12.75      inference('demod', [status(thm)], ['43', '55'])).
% 12.54/12.75  thf('57', plain,
% 12.54/12.75      (![X64 : $i, X65 : $i]:
% 12.54/12.75         (((k3_subset_1 @ X64 @ X65) = (k4_xboole_0 @ X64 @ X65))
% 12.54/12.75          | ~ (m1_subset_1 @ X65 @ (k1_zfmisc_1 @ X64)))),
% 12.54/12.75      inference('cnf', [status(esa)], [d5_subset_1])).
% 12.54/12.75  thf('58', plain,
% 12.54/12.75      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 12.54/12.75      inference('sup-', [status(thm)], ['56', '57'])).
% 12.54/12.75  thf('59', plain,
% 12.54/12.75      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 12.54/12.75      inference('demod', [status(thm)], ['21', '58'])).
% 12.54/12.75  thf('60', plain,
% 12.54/12.75      (![X21 : $i, X22 : $i, X23 : $i]:
% 12.54/12.75         ((k5_xboole_0 @ (k5_xboole_0 @ X21 @ X22) @ X23)
% 12.54/12.75           = (k5_xboole_0 @ X21 @ (k5_xboole_0 @ X22 @ X23)))),
% 12.54/12.75      inference('cnf', [status(esa)], [t91_xboole_1])).
% 12.54/12.75  thf('61', plain,
% 12.54/12.75      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 12.54/12.75      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 12.54/12.75  thf('62', plain,
% 12.54/12.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.54/12.75         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X2 @ X1))
% 12.54/12.75           = (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))),
% 12.54/12.75      inference('sup+', [status(thm)], ['60', '61'])).
% 12.54/12.75  thf('63', plain,
% 12.54/12.75      (![X0 : $i, X1 : $i]:
% 12.54/12.75         ((k5_xboole_0 @ X1 @ (k3_subset_1 @ X0 @ X0))
% 12.54/12.75           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 12.54/12.75      inference('sup+', [status(thm)], ['59', '62'])).
% 12.54/12.75  thf(d5_xboole_0, axiom,
% 12.54/12.75    (![A:$i,B:$i,C:$i]:
% 12.54/12.75     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 12.54/12.75       ( ![D:$i]:
% 12.54/12.75         ( ( r2_hidden @ D @ C ) <=>
% 12.54/12.75           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 12.54/12.75  thf('64', plain,
% 12.54/12.75      (![X5 : $i, X6 : $i, X9 : $i]:
% 12.54/12.75         (((X9) = (k4_xboole_0 @ X5 @ X6))
% 12.54/12.75          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X5)
% 12.54/12.75          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X9))),
% 12.54/12.75      inference('cnf', [status(esa)], [d5_xboole_0])).
% 12.54/12.75  thf('65', plain, (![X10 : $i]: ((k3_xboole_0 @ X10 @ X10) = (X10))),
% 12.54/12.75      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 12.54/12.75  thf('66', plain,
% 12.54/12.75      (![X0 : $i]:
% 12.54/12.75         ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 12.54/12.75      inference('sup+', [status(thm)], ['22', '25'])).
% 12.54/12.75  thf('67', plain,
% 12.54/12.75      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 12.54/12.75         (~ (r2_hidden @ X8 @ X7)
% 12.54/12.75          | ~ (r2_hidden @ X8 @ X6)
% 12.54/12.75          | ((X7) != (k4_xboole_0 @ X5 @ X6)))),
% 12.54/12.75      inference('cnf', [status(esa)], [d5_xboole_0])).
% 12.54/12.75  thf('68', plain,
% 12.54/12.75      (![X5 : $i, X6 : $i, X8 : $i]:
% 12.54/12.75         (~ (r2_hidden @ X8 @ X6)
% 12.54/12.75          | ~ (r2_hidden @ X8 @ (k4_xboole_0 @ X5 @ X6)))),
% 12.54/12.75      inference('simplify', [status(thm)], ['67'])).
% 12.54/12.75  thf('69', plain,
% 12.54/12.75      (![X0 : $i, X1 : $i]:
% 12.54/12.75         (~ (r2_hidden @ X1 @ (k3_xboole_0 @ k1_xboole_0 @ X0))
% 12.54/12.75          | ~ (r2_hidden @ X1 @ X0))),
% 12.54/12.75      inference('sup-', [status(thm)], ['66', '68'])).
% 12.54/12.75  thf('70', plain,
% 12.54/12.75      (![X0 : $i]:
% 12.54/12.75         (~ (r2_hidden @ X0 @ k1_xboole_0) | ~ (r2_hidden @ X0 @ k1_xboole_0))),
% 12.54/12.75      inference('sup-', [status(thm)], ['65', '69'])).
% 12.54/12.75  thf('71', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 12.54/12.75      inference('simplify', [status(thm)], ['70'])).
% 12.54/12.75  thf('72', plain,
% 12.54/12.75      (![X0 : $i, X1 : $i]:
% 12.54/12.75         ((r2_hidden @ (sk_D @ k1_xboole_0 @ X1 @ X0) @ X0)
% 12.54/12.75          | ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X1)))),
% 12.54/12.75      inference('sup-', [status(thm)], ['64', '71'])).
% 12.54/12.75  thf('73', plain,
% 12.54/12.75      (![X18 : $i, X19 : $i]: (r1_tarski @ (k4_xboole_0 @ X18 @ X19) @ X18)),
% 12.54/12.75      inference('cnf', [status(esa)], [t36_xboole_1])).
% 12.54/12.75  thf('74', plain,
% 12.54/12.75      (![X16 : $i, X17 : $i]:
% 12.54/12.75         (((k3_xboole_0 @ X16 @ X17) = (X16)) | ~ (r1_tarski @ X16 @ X17))),
% 12.54/12.75      inference('cnf', [status(esa)], [t28_xboole_1])).
% 12.54/12.75  thf('75', plain,
% 12.54/12.75      (![X0 : $i, X1 : $i]:
% 12.54/12.75         ((k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0)
% 12.54/12.75           = (k4_xboole_0 @ X0 @ X1))),
% 12.54/12.75      inference('sup-', [status(thm)], ['73', '74'])).
% 12.54/12.75  thf('76', plain,
% 12.54/12.75      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 12.54/12.75      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 12.54/12.75  thf('77', plain,
% 12.54/12.75      (![X0 : $i, X1 : $i]:
% 12.54/12.75         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 12.54/12.75           = (k4_xboole_0 @ X0 @ X1))),
% 12.54/12.75      inference('demod', [status(thm)], ['75', '76'])).
% 12.54/12.75  thf('78', plain,
% 12.54/12.75      (![X11 : $i, X12 : $i]:
% 12.54/12.75         ((k4_xboole_0 @ X11 @ X12)
% 12.54/12.75           = (k5_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12)))),
% 12.54/12.75      inference('cnf', [status(esa)], [t100_xboole_1])).
% 12.54/12.75  thf('79', plain,
% 12.54/12.75      (![X13 : $i, X14 : $i, X15 : $i]:
% 12.54/12.75         ((k5_xboole_0 @ (k3_xboole_0 @ X13 @ X15) @ (k3_xboole_0 @ X14 @ X15))
% 12.54/12.75           = (k3_xboole_0 @ (k5_xboole_0 @ X13 @ X14) @ X15))),
% 12.54/12.75      inference('cnf', [status(esa)], [t112_xboole_1])).
% 12.54/12.75  thf('80', plain,
% 12.54/12.75      (![X0 : $i, X1 : $i]:
% 12.54/12.75         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0)
% 12.54/12.75           = (k3_xboole_0 @ (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)) @ X0))),
% 12.54/12.75      inference('sup+', [status(thm)], ['78', '79'])).
% 12.54/12.75  thf('81', plain,
% 12.54/12.75      (![X11 : $i, X12 : $i]:
% 12.54/12.75         ((k4_xboole_0 @ X11 @ X12)
% 12.54/12.75           = (k5_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12)))),
% 12.54/12.75      inference('cnf', [status(esa)], [t100_xboole_1])).
% 12.54/12.75  thf('82', plain,
% 12.54/12.75      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 12.54/12.75      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 12.54/12.75  thf('83', plain,
% 12.54/12.75      (![X0 : $i, X1 : $i]:
% 12.54/12.75         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0)
% 12.54/12.75           = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 12.54/12.75      inference('demod', [status(thm)], ['80', '81', '82'])).
% 12.54/12.75  thf('84', plain,
% 12.54/12.75      (![X5 : $i, X6 : $i, X8 : $i]:
% 12.54/12.75         (~ (r2_hidden @ X8 @ X6)
% 12.54/12.75          | ~ (r2_hidden @ X8 @ (k4_xboole_0 @ X5 @ X6)))),
% 12.54/12.75      inference('simplify', [status(thm)], ['67'])).
% 12.54/12.75  thf('85', plain,
% 12.54/12.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.54/12.75         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))
% 12.54/12.75          | ~ (r2_hidden @ X2 @ X0))),
% 12.54/12.75      inference('sup-', [status(thm)], ['83', '84'])).
% 12.54/12.75  thf('86', plain,
% 12.54/12.75      (![X0 : $i, X1 : $i]:
% 12.54/12.75         (~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0))
% 12.54/12.75          | ~ (r2_hidden @ X1 @ X0))),
% 12.54/12.75      inference('sup-', [status(thm)], ['77', '85'])).
% 12.54/12.75  thf('87', plain,
% 12.54/12.75      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 12.54/12.75         (~ (r2_hidden @ X8 @ X7)
% 12.54/12.75          | (r2_hidden @ X8 @ X5)
% 12.54/12.75          | ((X7) != (k4_xboole_0 @ X5 @ X6)))),
% 12.54/12.75      inference('cnf', [status(esa)], [d5_xboole_0])).
% 12.54/12.75  thf('88', plain,
% 12.54/12.75      (![X5 : $i, X6 : $i, X8 : $i]:
% 12.54/12.75         ((r2_hidden @ X8 @ X5) | ~ (r2_hidden @ X8 @ (k4_xboole_0 @ X5 @ X6)))),
% 12.54/12.75      inference('simplify', [status(thm)], ['87'])).
% 12.54/12.75  thf('89', plain,
% 12.54/12.75      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0))),
% 12.54/12.75      inference('clc', [status(thm)], ['86', '88'])).
% 12.54/12.75  thf('90', plain,
% 12.54/12.75      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 12.54/12.75      inference('sup-', [status(thm)], ['56', '57'])).
% 12.54/12.75  thf('91', plain,
% 12.54/12.75      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k3_subset_1 @ X0 @ X0))),
% 12.54/12.75      inference('demod', [status(thm)], ['89', '90'])).
% 12.54/12.75  thf('92', plain,
% 12.54/12.75      (![X0 : $i, X1 : $i]:
% 12.54/12.75         ((k1_xboole_0) = (k4_xboole_0 @ (k3_subset_1 @ X0 @ X0) @ X1))),
% 12.54/12.75      inference('sup-', [status(thm)], ['72', '91'])).
% 12.54/12.75  thf('93', plain,
% 12.54/12.75      (![X0 : $i]:
% 12.54/12.75         ((k3_tarski @ (k2_tarski @ X0 @ k1_xboole_0))
% 12.54/12.75           = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 12.54/12.75      inference('demod', [status(thm)], ['32', '33'])).
% 12.54/12.75  thf('94', plain,
% 12.54/12.75      (![X0 : $i]: ((k3_tarski @ (k2_tarski @ X0 @ k1_xboole_0)) = (X0))),
% 12.54/12.75      inference('demod', [status(thm)], ['52', '53', '54'])).
% 12.54/12.75  thf('95', plain, (![X0 : $i]: ((X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 12.54/12.75      inference('demod', [status(thm)], ['93', '94'])).
% 12.54/12.75  thf('96', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 12.54/12.75      inference('sup+', [status(thm)], ['92', '95'])).
% 12.54/12.75  thf('97', plain, (![X20 : $i]: ((k5_xboole_0 @ X20 @ k1_xboole_0) = (X20))),
% 12.54/12.75      inference('cnf', [status(esa)], [t5_boole])).
% 12.54/12.75  thf('98', plain,
% 12.54/12.75      (![X0 : $i, X1 : $i]:
% 12.54/12.75         ((k5_xboole_0 @ X1 @ (k3_subset_1 @ X0 @ X0)) = (X1))),
% 12.54/12.75      inference('sup+', [status(thm)], ['96', '97'])).
% 12.54/12.75  thf('99', plain,
% 12.54/12.75      (![X0 : $i, X1 : $i]:
% 12.54/12.75         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 12.54/12.75      inference('demod', [status(thm)], ['63', '98'])).
% 12.54/12.75  thf('100', plain,
% 12.54/12.75      (((sk_A) = (k5_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 12.54/12.75      inference('sup+', [status(thm)], ['18', '99'])).
% 12.54/12.75  thf('101', plain,
% 12.54/12.75      (((k3_subset_1 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_B @ sk_A))),
% 12.54/12.75      inference('demod', [status(thm)], ['13', '16', '17'])).
% 12.54/12.75  thf('102', plain,
% 12.54/12.75      (![X0 : $i, X1 : $i]:
% 12.54/12.75         ((k4_xboole_0 @ X1 @ X0)
% 12.54/12.75           = (k3_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 12.54/12.75      inference('sup+', [status(thm)], ['49', '50'])).
% 12.54/12.75  thf('103', plain,
% 12.54/12.75      (((k4_xboole_0 @ sk_B @ sk_A)
% 12.54/12.75         = (k3_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 12.54/12.75      inference('sup+', [status(thm)], ['101', '102'])).
% 12.54/12.75  thf('104', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 12.54/12.75      inference('sup-', [status(thm)], ['7', '8'])).
% 12.54/12.75  thf('105', plain,
% 12.54/12.75      (![X11 : $i, X12 : $i]:
% 12.54/12.75         ((k4_xboole_0 @ X11 @ X12)
% 12.54/12.75           = (k5_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12)))),
% 12.54/12.75      inference('cnf', [status(esa)], [t100_xboole_1])).
% 12.54/12.75  thf('106', plain,
% 12.54/12.75      (((k4_xboole_0 @ sk_B @ sk_A) = (k5_xboole_0 @ sk_B @ sk_B))),
% 12.54/12.75      inference('sup+', [status(thm)], ['104', '105'])).
% 12.54/12.75  thf('107', plain,
% 12.54/12.75      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 12.54/12.75      inference('sup+', [status(thm)], ['19', '20'])).
% 12.54/12.75  thf('108', plain,
% 12.54/12.75      (((k4_xboole_0 @ sk_B @ sk_A) = (k4_xboole_0 @ sk_B @ sk_B))),
% 12.54/12.75      inference('demod', [status(thm)], ['106', '107'])).
% 12.54/12.75  thf('109', plain,
% 12.54/12.75      (((k4_xboole_0 @ sk_B @ sk_B)
% 12.54/12.75         = (k3_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 12.54/12.75      inference('demod', [status(thm)], ['103', '108'])).
% 12.54/12.75  thf('110', plain,
% 12.54/12.75      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 12.54/12.75      inference('sup-', [status(thm)], ['56', '57'])).
% 12.54/12.75  thf('111', plain,
% 12.54/12.75      (((k3_subset_1 @ sk_B @ sk_B)
% 12.54/12.75         = (k3_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 12.54/12.75      inference('demod', [status(thm)], ['109', '110'])).
% 12.54/12.75  thf('112', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 12.54/12.75      inference('sup+', [status(thm)], ['92', '95'])).
% 12.54/12.75  thf('113', plain,
% 12.54/12.75      (((k1_xboole_0) = (k3_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 12.54/12.75      inference('demod', [status(thm)], ['111', '112'])).
% 12.54/12.75  thf('114', plain,
% 12.54/12.75      (![X0 : $i, X1 : $i]:
% 12.54/12.75         ((k4_xboole_0 @ X0 @ X1)
% 12.54/12.75           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 12.54/12.75      inference('sup+', [status(thm)], ['10', '11'])).
% 12.54/12.75  thf('115', plain,
% 12.54/12.75      (![X0 : $i, X1 : $i]:
% 12.54/12.75         ((k4_xboole_0 @ X1 @ X0)
% 12.54/12.75           = (k3_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 12.54/12.75      inference('sup+', [status(thm)], ['49', '50'])).
% 12.54/12.75  thf('116', plain,
% 12.54/12.75      (![X0 : $i, X1 : $i]:
% 12.54/12.75         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X1))
% 12.54/12.75           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 12.54/12.75      inference('sup+', [status(thm)], ['114', '115'])).
% 12.54/12.75  thf('117', plain,
% 12.54/12.75      (![X0 : $i, X1 : $i]:
% 12.54/12.75         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 12.54/12.75           = (k4_xboole_0 @ X0 @ X1))),
% 12.54/12.75      inference('demod', [status(thm)], ['75', '76'])).
% 12.54/12.75  thf('118', plain,
% 12.54/12.75      (![X0 : $i, X1 : $i]:
% 12.54/12.75         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X1))
% 12.54/12.75           = (k4_xboole_0 @ X1 @ X0))),
% 12.54/12.75      inference('demod', [status(thm)], ['116', '117'])).
% 12.54/12.75  thf('119', plain,
% 12.54/12.75      (((k4_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ k1_xboole_0)
% 12.54/12.75         = (k4_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))),
% 12.54/12.75      inference('sup+', [status(thm)], ['113', '118'])).
% 12.54/12.75  thf('120', plain, (![X0 : $i]: ((X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 12.54/12.75      inference('demod', [status(thm)], ['93', '94'])).
% 12.54/12.75  thf('121', plain,
% 12.54/12.75      (((k3_subset_1 @ sk_A @ sk_B)
% 12.54/12.75         = (k4_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))),
% 12.54/12.75      inference('demod', [status(thm)], ['119', '120'])).
% 12.54/12.75  thf('122', plain,
% 12.54/12.75      (![X24 : $i, X25 : $i]:
% 12.54/12.75         ((k3_tarski @ (k2_tarski @ X24 @ X25))
% 12.54/12.75           = (k5_xboole_0 @ X24 @ (k4_xboole_0 @ X25 @ X24)))),
% 12.54/12.75      inference('demod', [status(thm)], ['27', '28', '29', '30'])).
% 12.54/12.75  thf('123', plain,
% 12.54/12.75      (((k3_tarski @ (k2_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))
% 12.54/12.75         = (k5_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 12.54/12.75      inference('sup+', [status(thm)], ['121', '122'])).
% 12.54/12.75  thf('124', plain,
% 12.54/12.75      (((k3_tarski @ (k2_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))) = (sk_A))),
% 12.54/12.75      inference('sup+', [status(thm)], ['100', '123'])).
% 12.54/12.75  thf('125', plain,
% 12.54/12.75      (((k4_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 12.54/12.75         != (k2_subset_1 @ sk_A))),
% 12.54/12.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.54/12.75  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 12.54/12.75  thf('126', plain, (![X63 : $i]: ((k2_subset_1 @ X63) = (X63))),
% 12.54/12.75      inference('cnf', [status(esa)], [d4_subset_1])).
% 12.54/12.75  thf('127', plain,
% 12.54/12.75      (((k4_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)) != (sk_A))),
% 12.54/12.75      inference('demod', [status(thm)], ['125', '126'])).
% 12.54/12.75  thf('128', plain,
% 12.54/12.75      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 12.54/12.75      inference('sup-', [status(thm)], ['14', '15'])).
% 12.54/12.75  thf('129', plain,
% 12.54/12.75      (![X18 : $i, X19 : $i]: (r1_tarski @ (k4_xboole_0 @ X18 @ X19) @ X18)),
% 12.54/12.75      inference('cnf', [status(esa)], [t36_xboole_1])).
% 12.54/12.75  thf('130', plain, ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_A)),
% 12.54/12.75      inference('sup+', [status(thm)], ['128', '129'])).
% 12.54/12.75  thf('131', plain,
% 12.54/12.75      (![X53 : $i, X54 : $i]:
% 12.54/12.75         ((r2_hidden @ X53 @ (k1_zfmisc_1 @ X54)) | ~ (r1_tarski @ X53 @ X54))),
% 12.54/12.75      inference('simplify', [status(thm)], ['36'])).
% 12.54/12.75  thf('132', plain,
% 12.54/12.75      ((r2_hidden @ (k3_subset_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 12.54/12.75      inference('sup-', [status(thm)], ['130', '131'])).
% 12.54/12.75  thf('133', plain,
% 12.54/12.75      (![X60 : $i, X61 : $i]:
% 12.54/12.75         (~ (r2_hidden @ X60 @ X61)
% 12.54/12.75          | (m1_subset_1 @ X60 @ X61)
% 12.54/12.75          | (v1_xboole_0 @ X61))),
% 12.54/12.75      inference('cnf', [status(esa)], [d2_subset_1])).
% 12.54/12.75  thf('134', plain,
% 12.54/12.75      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 12.54/12.75        | (m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A)))),
% 12.54/12.75      inference('sup-', [status(thm)], ['132', '133'])).
% 12.54/12.75  thf('135', plain, (![X66 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X66))),
% 12.54/12.75      inference('cnf', [status(esa)], [fc1_subset_1])).
% 12.54/12.75  thf('136', plain,
% 12.54/12.75      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 12.54/12.75      inference('clc', [status(thm)], ['134', '135'])).
% 12.54/12.75  thf('137', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 12.54/12.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.54/12.75  thf(redefinition_k4_subset_1, axiom,
% 12.54/12.75    (![A:$i,B:$i,C:$i]:
% 12.54/12.75     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 12.54/12.75         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 12.54/12.75       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 12.54/12.75  thf('138', plain,
% 12.54/12.75      (![X67 : $i, X68 : $i, X69 : $i]:
% 12.54/12.75         (~ (m1_subset_1 @ X67 @ (k1_zfmisc_1 @ X68))
% 12.54/12.75          | ~ (m1_subset_1 @ X69 @ (k1_zfmisc_1 @ X68))
% 12.54/12.75          | ((k4_subset_1 @ X68 @ X67 @ X69) = (k2_xboole_0 @ X67 @ X69)))),
% 12.54/12.75      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 12.54/12.75  thf('139', plain,
% 12.54/12.75      (![X58 : $i, X59 : $i]:
% 12.54/12.75         ((k3_tarski @ (k2_tarski @ X58 @ X59)) = (k2_xboole_0 @ X58 @ X59))),
% 12.54/12.75      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 12.54/12.75  thf('140', plain,
% 12.54/12.75      (![X67 : $i, X68 : $i, X69 : $i]:
% 12.54/12.75         (~ (m1_subset_1 @ X67 @ (k1_zfmisc_1 @ X68))
% 12.54/12.75          | ~ (m1_subset_1 @ X69 @ (k1_zfmisc_1 @ X68))
% 12.54/12.75          | ((k4_subset_1 @ X68 @ X67 @ X69)
% 12.54/12.75              = (k3_tarski @ (k2_tarski @ X67 @ X69))))),
% 12.54/12.75      inference('demod', [status(thm)], ['138', '139'])).
% 12.54/12.75  thf('141', plain,
% 12.54/12.75      (![X0 : $i]:
% 12.54/12.75         (((k4_subset_1 @ sk_A @ sk_B @ X0)
% 12.54/12.75            = (k3_tarski @ (k2_tarski @ sk_B @ X0)))
% 12.54/12.75          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 12.54/12.75      inference('sup-', [status(thm)], ['137', '140'])).
% 12.54/12.75  thf('142', plain,
% 12.54/12.75      (((k4_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 12.54/12.75         = (k3_tarski @ (k2_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))))),
% 12.54/12.75      inference('sup-', [status(thm)], ['136', '141'])).
% 12.54/12.75  thf('143', plain,
% 12.54/12.75      (((k3_tarski @ (k2_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))
% 12.54/12.75         != (sk_A))),
% 12.54/12.75      inference('demod', [status(thm)], ['127', '142'])).
% 12.54/12.75  thf('144', plain, ($false),
% 12.54/12.75      inference('simplify_reflect-', [status(thm)], ['124', '143'])).
% 12.54/12.75  
% 12.54/12.75  % SZS output end Refutation
% 12.54/12.75  
% 12.54/12.76  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
