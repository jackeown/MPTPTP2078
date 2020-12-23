%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.C7mYLyr2ay

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:52 EST 2020

% Result     : Theorem 1.01s
% Output     : Refutation 1.01s
% Verified   : 
% Statistics : Number of formulae       :  170 ( 509 expanded)
%              Number of leaves         :   37 ( 181 expanded)
%              Depth                    :   24
%              Number of atoms          : 1203 (3783 expanded)
%              Number of equality atoms :  123 ( 385 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

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

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('1',plain,(
    ! [X58: $i,X59: $i] :
      ( ~ ( m1_subset_1 @ X58 @ X59 )
      | ( r2_hidden @ X58 @ X59 )
      | ( v1_xboole_0 @ X59 ) ) ),
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
    ! [X52: $i,X53: $i,X54: $i] :
      ( ~ ( r2_hidden @ X54 @ X53 )
      | ( r1_tarski @ X54 @ X52 )
      | ( X53
       != ( k1_zfmisc_1 @ X52 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('6',plain,(
    ! [X52: $i,X54: $i] :
      ( ( r1_tarski @ X54 @ X52 )
      | ~ ( r2_hidden @ X54 @ ( k1_zfmisc_1 @ X52 ) ) ) ),
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
    ! [X12: $i,X13: $i] :
      ( ( ( k3_xboole_0 @ X12 @ X13 )
        = X12 )
      | ~ ( r1_tarski @ X12 @ X13 ) ) ),
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
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
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
    ! [X62: $i,X63: $i] :
      ( ( ( k3_subset_1 @ X62 @ X63 )
        = ( k4_xboole_0 @ X62 @ X63 ) )
      | ~ ( m1_subset_1 @ X63 @ ( k1_zfmisc_1 @ X62 ) ) ) ),
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
    ! [X4: $i] :
      ( ( k3_xboole_0 @ X4 @ X4 )
      = X4 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('20',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('22',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k2_xboole_0 @ X16 @ X17 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('23',plain,(
    ! [X56: $i,X57: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X56 @ X57 ) )
      = ( k2_xboole_0 @ X56 @ X57 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('24',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k3_tarski @ ( k2_tarski @ X16 @ X17 ) ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['22','23'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('25',plain,(
    ! [X14: $i,X15: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X14 @ X15 ) @ X14 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_xboole_0 @ X12 @ X13 )
        = X12 )
      | ~ ( r1_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('33',plain,(
    ! [X18: $i] :
      ( ( k5_xboole_0 @ X18 @ k1_xboole_0 )
      = X18 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X14: $i,X15: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X14 @ X15 ) @ X14 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X51: $i,X52: $i,X53: $i] :
      ( ~ ( r1_tarski @ X51 @ X52 )
      | ( r2_hidden @ X51 @ X53 )
      | ( X53
       != ( k1_zfmisc_1 @ X52 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('38',plain,(
    ! [X51: $i,X52: $i] :
      ( ( r2_hidden @ X51 @ ( k1_zfmisc_1 @ X52 ) )
      | ~ ( r1_tarski @ X51 @ X52 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','38'])).

thf('40',plain,(
    ! [X58: $i,X59: $i] :
      ( ~ ( r2_hidden @ X58 @ X59 )
      | ( m1_subset_1 @ X58 @ X59 )
      | ( v1_xboole_0 @ X59 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X66: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X66 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X62: $i,X63: $i] :
      ( ( ( k3_subset_1 @ X62 @ X63 )
        = ( k4_xboole_0 @ X62 @ X63 ) )
      | ~ ( m1_subset_1 @ X63 @ ( k1_zfmisc_1 @ X62 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['21','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('48',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('51',plain,(
    ! [X18: $i] :
      ( ( k5_xboole_0 @ X18 @ k1_xboole_0 )
      = X18 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['49','52'])).

thf(t94_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('54',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ X22 @ X23 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X22 @ X23 ) @ ( k3_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t94_xboole_1])).

thf('55',plain,(
    ! [X56: $i,X57: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X56 @ X57 ) )
      = ( k2_xboole_0 @ X56 @ X57 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('56',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X19 @ X20 ) @ X21 )
      = ( k5_xboole_0 @ X19 @ ( k5_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('58',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X22 @ X23 ) )
      = ( k5_xboole_0 @ X22 @ ( k4_xboole_0 @ X23 @ X22 ) ) ) ),
    inference(demod,[status(thm)],['54','55','56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X0 @ k1_xboole_0 ) )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['53','58'])).

thf('60',plain,(
    ! [X18: $i] :
      ( ( k5_xboole_0 @ X18 @ k1_xboole_0 )
      = X18 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X0 @ k1_xboole_0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k3_tarski @ ( k2_tarski @ X16 @ X17 ) ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['46','65'])).

thf('67',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X19 @ X20 ) @ X21 )
      = ( k5_xboole_0 @ X19 @ ( k5_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,
    ( sk_A
    = ( k5_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['18','70'])).

thf('72',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('73',plain,(
    ! [X14: $i,X15: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X14 @ X15 ) @ X14 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('74',plain,(
    r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_A ),
    inference('sup+',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_xboole_0 @ X12 @ X13 )
        = X12 )
      | ~ ( r1_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('76',plain,
    ( ( k3_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_A )
    = ( k3_subset_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('78',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k3_subset_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf(t112_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ B ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ A @ C ) @ B ) ) )).

thf('80',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X7 @ X9 ) @ ( k3_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X7 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t112_xboole_1])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['81','82','83'])).

thf('85',plain,
    ( ( k4_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k3_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['78','84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('87',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('88',plain,(
    ! [X64: $i,X65: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X64 @ X65 ) @ ( k1_zfmisc_1 @ X64 ) )
      | ~ ( m1_subset_1 @ X65 @ ( k1_zfmisc_1 @ X64 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('89',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X62: $i,X63: $i] :
      ( ( ( k3_subset_1 @ X62 @ X63 )
        = ( k4_xboole_0 @ X62 @ X63 ) )
      | ~ ( m1_subset_1 @ X63 @ ( k1_zfmisc_1 @ X62 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('91',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['21','45'])).

thf('93',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['13','16','17'])).

thf('94',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X19 @ X20 ) @ X21 )
      = ( k5_xboole_0 @ X19 @ ( k5_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ X0 )
      = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['93','94'])).

thf('96',plain,
    ( ( k5_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_A )
    = ( k5_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_A ) ) ),
    inference('sup+',[status(thm)],['92','95'])).

thf('97',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('98',plain,
    ( ( k5_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k5_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k3_subset_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('100',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('101',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k5_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['99','100'])).

thf('102',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('103',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k5_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k5_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_A ) ) ),
    inference('sup+',[status(thm)],['98','103'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('106',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('108',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['104','105','106','107'])).

thf('109',plain,
    ( sk_B
    = ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['91','108'])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('111',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['85','86','109','110'])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('113',plain,
    ( ( k4_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
    = ( k5_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('115',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('116',plain,
    ( ( k4_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
    = ( k3_subset_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['113','114','115'])).

thf('117',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X22 @ X23 ) )
      = ( k5_xboole_0 @ X22 @ ( k4_xboole_0 @ X23 @ X22 ) ) ) ),
    inference(demod,[status(thm)],['54','55','56','57'])).

thf('118',plain,
    ( ( k3_tarski @ ( k2_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) )
    = ( k5_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['116','117'])).

thf('119',plain,
    ( ( k3_tarski @ ( k2_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) )
    = sk_A ),
    inference('sup+',[status(thm)],['71','118'])).

thf('120',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
 != ( k2_subset_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('121',plain,(
    ! [X61: $i] :
      ( ( k2_subset_1 @ X61 )
      = X61 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('122',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
 != sk_A ),
    inference(demod,[status(thm)],['120','121'])).

thf('123',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('124',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('125',plain,(
    ! [X67: $i,X68: $i,X69: $i] :
      ( ~ ( m1_subset_1 @ X67 @ ( k1_zfmisc_1 @ X68 ) )
      | ~ ( m1_subset_1 @ X69 @ ( k1_zfmisc_1 @ X68 ) )
      | ( ( k4_subset_1 @ X68 @ X67 @ X69 )
        = ( k2_xboole_0 @ X67 @ X69 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('126',plain,(
    ! [X56: $i,X57: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X56 @ X57 ) )
      = ( k2_xboole_0 @ X56 @ X57 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('127',plain,(
    ! [X67: $i,X68: $i,X69: $i] :
      ( ~ ( m1_subset_1 @ X67 @ ( k1_zfmisc_1 @ X68 ) )
      | ~ ( m1_subset_1 @ X69 @ ( k1_zfmisc_1 @ X68 ) )
      | ( ( k4_subset_1 @ X68 @ X67 @ X69 )
        = ( k3_tarski @ ( k2_tarski @ X67 @ X69 ) ) ) ) ),
    inference(demod,[status(thm)],['125','126'])).

thf('128',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ sk_A @ sk_B @ X0 )
        = ( k3_tarski @ ( k2_tarski @ sk_B @ X0 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['124','127'])).

thf('129',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k3_tarski @ ( k2_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['123','128'])).

thf('130',plain,(
    ( k3_tarski @ ( k2_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) )
 != sk_A ),
    inference(demod,[status(thm)],['122','129'])).

thf('131',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['119','130'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.C7mYLyr2ay
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:02:18 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.19/0.34  % Number of cores: 8
% 0.19/0.35  % Python version: Python 3.6.8
% 0.19/0.35  % Running in FO mode
% 1.01/1.22  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.01/1.22  % Solved by: fo/fo7.sh
% 1.01/1.22  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.01/1.22  % done 1675 iterations in 0.768s
% 1.01/1.22  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.01/1.22  % SZS output start Refutation
% 1.01/1.22  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.01/1.22  thf(sk_A_type, type, sk_A: $i).
% 1.01/1.22  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.01/1.22  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 1.01/1.22  thf(sk_B_type, type, sk_B: $i).
% 1.01/1.22  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.01/1.22  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.01/1.22  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.01/1.22  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 1.01/1.22  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 1.01/1.22  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.01/1.22  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 1.01/1.22  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.01/1.22  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.01/1.22  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.01/1.22  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.01/1.22  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.01/1.22  thf(t25_subset_1, conjecture,
% 1.01/1.22    (![A:$i,B:$i]:
% 1.01/1.22     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.01/1.22       ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) ) =
% 1.01/1.22         ( k2_subset_1 @ A ) ) ))).
% 1.01/1.22  thf(zf_stmt_0, negated_conjecture,
% 1.01/1.22    (~( ![A:$i,B:$i]:
% 1.01/1.22        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.01/1.22          ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) ) =
% 1.01/1.22            ( k2_subset_1 @ A ) ) ) )),
% 1.01/1.22    inference('cnf.neg', [status(esa)], [t25_subset_1])).
% 1.01/1.22  thf('0', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 1.01/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.22  thf(d2_subset_1, axiom,
% 1.01/1.22    (![A:$i,B:$i]:
% 1.01/1.22     ( ( ( v1_xboole_0 @ A ) =>
% 1.01/1.22         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 1.01/1.22       ( ( ~( v1_xboole_0 @ A ) ) =>
% 1.01/1.22         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 1.01/1.22  thf('1', plain,
% 1.01/1.22      (![X58 : $i, X59 : $i]:
% 1.01/1.22         (~ (m1_subset_1 @ X58 @ X59)
% 1.01/1.22          | (r2_hidden @ X58 @ X59)
% 1.01/1.22          | (v1_xboole_0 @ X59))),
% 1.01/1.22      inference('cnf', [status(esa)], [d2_subset_1])).
% 1.01/1.22  thf('2', plain,
% 1.01/1.22      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 1.01/1.22        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 1.01/1.22      inference('sup-', [status(thm)], ['0', '1'])).
% 1.01/1.22  thf(fc1_subset_1, axiom,
% 1.01/1.22    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 1.01/1.22  thf('3', plain, (![X66 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X66))),
% 1.01/1.22      inference('cnf', [status(esa)], [fc1_subset_1])).
% 1.01/1.22  thf('4', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 1.01/1.22      inference('clc', [status(thm)], ['2', '3'])).
% 1.01/1.22  thf(d1_zfmisc_1, axiom,
% 1.01/1.22    (![A:$i,B:$i]:
% 1.01/1.22     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 1.01/1.22       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 1.01/1.22  thf('5', plain,
% 1.01/1.22      (![X52 : $i, X53 : $i, X54 : $i]:
% 1.01/1.22         (~ (r2_hidden @ X54 @ X53)
% 1.01/1.22          | (r1_tarski @ X54 @ X52)
% 1.01/1.22          | ((X53) != (k1_zfmisc_1 @ X52)))),
% 1.01/1.22      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 1.01/1.22  thf('6', plain,
% 1.01/1.22      (![X52 : $i, X54 : $i]:
% 1.01/1.22         ((r1_tarski @ X54 @ X52) | ~ (r2_hidden @ X54 @ (k1_zfmisc_1 @ X52)))),
% 1.01/1.22      inference('simplify', [status(thm)], ['5'])).
% 1.01/1.22  thf('7', plain, ((r1_tarski @ sk_B @ sk_A)),
% 1.01/1.22      inference('sup-', [status(thm)], ['4', '6'])).
% 1.01/1.22  thf(t28_xboole_1, axiom,
% 1.01/1.22    (![A:$i,B:$i]:
% 1.01/1.22     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.01/1.22  thf('8', plain,
% 1.01/1.22      (![X12 : $i, X13 : $i]:
% 1.01/1.22         (((k3_xboole_0 @ X12 @ X13) = (X12)) | ~ (r1_tarski @ X12 @ X13))),
% 1.01/1.22      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.01/1.22  thf('9', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 1.01/1.22      inference('sup-', [status(thm)], ['7', '8'])).
% 1.01/1.22  thf(commutativity_k3_xboole_0, axiom,
% 1.01/1.22    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 1.01/1.22  thf('10', plain,
% 1.01/1.22      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.01/1.22      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.01/1.22  thf(t100_xboole_1, axiom,
% 1.01/1.22    (![A:$i,B:$i]:
% 1.01/1.22     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.01/1.22  thf('11', plain,
% 1.01/1.22      (![X5 : $i, X6 : $i]:
% 1.01/1.22         ((k4_xboole_0 @ X5 @ X6)
% 1.01/1.22           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 1.01/1.22      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.01/1.22  thf('12', plain,
% 1.01/1.22      (![X0 : $i, X1 : $i]:
% 1.01/1.22         ((k4_xboole_0 @ X0 @ X1)
% 1.01/1.22           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.01/1.22      inference('sup+', [status(thm)], ['10', '11'])).
% 1.01/1.22  thf('13', plain,
% 1.01/1.22      (((k4_xboole_0 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 1.01/1.22      inference('sup+', [status(thm)], ['9', '12'])).
% 1.01/1.22  thf('14', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 1.01/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.22  thf(d5_subset_1, axiom,
% 1.01/1.22    (![A:$i,B:$i]:
% 1.01/1.22     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.01/1.22       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 1.01/1.22  thf('15', plain,
% 1.01/1.22      (![X62 : $i, X63 : $i]:
% 1.01/1.22         (((k3_subset_1 @ X62 @ X63) = (k4_xboole_0 @ X62 @ X63))
% 1.01/1.22          | ~ (m1_subset_1 @ X63 @ (k1_zfmisc_1 @ X62)))),
% 1.01/1.22      inference('cnf', [status(esa)], [d5_subset_1])).
% 1.01/1.22  thf('16', plain,
% 1.01/1.22      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 1.01/1.22      inference('sup-', [status(thm)], ['14', '15'])).
% 1.01/1.22  thf(commutativity_k5_xboole_0, axiom,
% 1.01/1.22    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 1.01/1.22  thf('17', plain,
% 1.01/1.22      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 1.01/1.22      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.01/1.22  thf('18', plain,
% 1.01/1.22      (((k3_subset_1 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_B @ sk_A))),
% 1.01/1.22      inference('demod', [status(thm)], ['13', '16', '17'])).
% 1.01/1.22  thf(idempotence_k3_xboole_0, axiom,
% 1.01/1.22    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 1.01/1.22  thf('19', plain, (![X4 : $i]: ((k3_xboole_0 @ X4 @ X4) = (X4))),
% 1.01/1.22      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 1.01/1.22  thf('20', plain,
% 1.01/1.22      (![X5 : $i, X6 : $i]:
% 1.01/1.22         ((k4_xboole_0 @ X5 @ X6)
% 1.01/1.22           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 1.01/1.22      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.01/1.22  thf('21', plain,
% 1.01/1.22      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 1.01/1.22      inference('sup+', [status(thm)], ['19', '20'])).
% 1.01/1.22  thf(t46_xboole_1, axiom,
% 1.01/1.22    (![A:$i,B:$i]:
% 1.01/1.22     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 1.01/1.22  thf('22', plain,
% 1.01/1.22      (![X16 : $i, X17 : $i]:
% 1.01/1.22         ((k4_xboole_0 @ X16 @ (k2_xboole_0 @ X16 @ X17)) = (k1_xboole_0))),
% 1.01/1.22      inference('cnf', [status(esa)], [t46_xboole_1])).
% 1.01/1.22  thf(l51_zfmisc_1, axiom,
% 1.01/1.22    (![A:$i,B:$i]:
% 1.01/1.22     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 1.01/1.22  thf('23', plain,
% 1.01/1.22      (![X56 : $i, X57 : $i]:
% 1.01/1.22         ((k3_tarski @ (k2_tarski @ X56 @ X57)) = (k2_xboole_0 @ X56 @ X57))),
% 1.01/1.22      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.01/1.22  thf('24', plain,
% 1.01/1.22      (![X16 : $i, X17 : $i]:
% 1.01/1.22         ((k4_xboole_0 @ X16 @ (k3_tarski @ (k2_tarski @ X16 @ X17)))
% 1.01/1.22           = (k1_xboole_0))),
% 1.01/1.22      inference('demod', [status(thm)], ['22', '23'])).
% 1.01/1.22  thf(t36_xboole_1, axiom,
% 1.01/1.22    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 1.01/1.22  thf('25', plain,
% 1.01/1.22      (![X14 : $i, X15 : $i]: (r1_tarski @ (k4_xboole_0 @ X14 @ X15) @ X14)),
% 1.01/1.22      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.01/1.22  thf('26', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 1.01/1.22      inference('sup+', [status(thm)], ['24', '25'])).
% 1.01/1.22  thf('27', plain,
% 1.01/1.22      (![X12 : $i, X13 : $i]:
% 1.01/1.22         (((k3_xboole_0 @ X12 @ X13) = (X12)) | ~ (r1_tarski @ X12 @ X13))),
% 1.01/1.22      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.01/1.22  thf('28', plain,
% 1.01/1.22      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 1.01/1.22      inference('sup-', [status(thm)], ['26', '27'])).
% 1.01/1.22  thf('29', plain,
% 1.01/1.22      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.01/1.22      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.01/1.22  thf('30', plain,
% 1.01/1.22      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 1.01/1.22      inference('sup+', [status(thm)], ['28', '29'])).
% 1.01/1.22  thf('31', plain,
% 1.01/1.22      (![X5 : $i, X6 : $i]:
% 1.01/1.22         ((k4_xboole_0 @ X5 @ X6)
% 1.01/1.22           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 1.01/1.22      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.01/1.22  thf('32', plain,
% 1.01/1.22      (![X0 : $i]:
% 1.01/1.22         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 1.01/1.22      inference('sup+', [status(thm)], ['30', '31'])).
% 1.01/1.22  thf(t5_boole, axiom,
% 1.01/1.22    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.01/1.22  thf('33', plain, (![X18 : $i]: ((k5_xboole_0 @ X18 @ k1_xboole_0) = (X18))),
% 1.01/1.22      inference('cnf', [status(esa)], [t5_boole])).
% 1.01/1.22  thf('34', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 1.01/1.22      inference('sup+', [status(thm)], ['32', '33'])).
% 1.01/1.22  thf('35', plain,
% 1.01/1.22      (![X14 : $i, X15 : $i]: (r1_tarski @ (k4_xboole_0 @ X14 @ X15) @ X14)),
% 1.01/1.22      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.01/1.22  thf('36', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 1.01/1.22      inference('sup+', [status(thm)], ['34', '35'])).
% 1.01/1.22  thf('37', plain,
% 1.01/1.22      (![X51 : $i, X52 : $i, X53 : $i]:
% 1.01/1.22         (~ (r1_tarski @ X51 @ X52)
% 1.01/1.22          | (r2_hidden @ X51 @ X53)
% 1.01/1.22          | ((X53) != (k1_zfmisc_1 @ X52)))),
% 1.01/1.22      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 1.01/1.22  thf('38', plain,
% 1.01/1.22      (![X51 : $i, X52 : $i]:
% 1.01/1.22         ((r2_hidden @ X51 @ (k1_zfmisc_1 @ X52)) | ~ (r1_tarski @ X51 @ X52))),
% 1.01/1.22      inference('simplify', [status(thm)], ['37'])).
% 1.01/1.22  thf('39', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_zfmisc_1 @ X0))),
% 1.01/1.22      inference('sup-', [status(thm)], ['36', '38'])).
% 1.01/1.22  thf('40', plain,
% 1.01/1.22      (![X58 : $i, X59 : $i]:
% 1.01/1.22         (~ (r2_hidden @ X58 @ X59)
% 1.01/1.22          | (m1_subset_1 @ X58 @ X59)
% 1.01/1.22          | (v1_xboole_0 @ X59))),
% 1.01/1.22      inference('cnf', [status(esa)], [d2_subset_1])).
% 1.01/1.22  thf('41', plain,
% 1.01/1.22      (![X0 : $i]:
% 1.01/1.22         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 1.01/1.22          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0)))),
% 1.01/1.22      inference('sup-', [status(thm)], ['39', '40'])).
% 1.01/1.22  thf('42', plain, (![X66 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X66))),
% 1.01/1.22      inference('cnf', [status(esa)], [fc1_subset_1])).
% 1.01/1.22  thf('43', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 1.01/1.22      inference('clc', [status(thm)], ['41', '42'])).
% 1.01/1.22  thf('44', plain,
% 1.01/1.22      (![X62 : $i, X63 : $i]:
% 1.01/1.22         (((k3_subset_1 @ X62 @ X63) = (k4_xboole_0 @ X62 @ X63))
% 1.01/1.22          | ~ (m1_subset_1 @ X63 @ (k1_zfmisc_1 @ X62)))),
% 1.01/1.22      inference('cnf', [status(esa)], [d5_subset_1])).
% 1.01/1.22  thf('45', plain,
% 1.01/1.22      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 1.01/1.22      inference('sup-', [status(thm)], ['43', '44'])).
% 1.01/1.22  thf('46', plain,
% 1.01/1.22      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 1.01/1.22      inference('demod', [status(thm)], ['21', '45'])).
% 1.01/1.22  thf('47', plain,
% 1.01/1.22      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 1.01/1.22      inference('sup-', [status(thm)], ['26', '27'])).
% 1.01/1.22  thf('48', plain,
% 1.01/1.22      (![X5 : $i, X6 : $i]:
% 1.01/1.22         ((k4_xboole_0 @ X5 @ X6)
% 1.01/1.22           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 1.01/1.22      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.01/1.22  thf('49', plain,
% 1.01/1.22      (![X0 : $i]:
% 1.01/1.22         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 1.01/1.22           = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 1.01/1.22      inference('sup+', [status(thm)], ['47', '48'])).
% 1.01/1.22  thf('50', plain,
% 1.01/1.22      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 1.01/1.22      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.01/1.22  thf('51', plain, (![X18 : $i]: ((k5_xboole_0 @ X18 @ k1_xboole_0) = (X18))),
% 1.01/1.22      inference('cnf', [status(esa)], [t5_boole])).
% 1.01/1.22  thf('52', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.01/1.22      inference('sup+', [status(thm)], ['50', '51'])).
% 1.01/1.22  thf('53', plain,
% 1.01/1.22      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 1.01/1.22      inference('demod', [status(thm)], ['49', '52'])).
% 1.01/1.22  thf(t94_xboole_1, axiom,
% 1.01/1.22    (![A:$i,B:$i]:
% 1.01/1.22     ( ( k2_xboole_0 @ A @ B ) =
% 1.01/1.22       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.01/1.22  thf('54', plain,
% 1.01/1.22      (![X22 : $i, X23 : $i]:
% 1.01/1.22         ((k2_xboole_0 @ X22 @ X23)
% 1.01/1.22           = (k5_xboole_0 @ (k5_xboole_0 @ X22 @ X23) @ 
% 1.01/1.22              (k3_xboole_0 @ X22 @ X23)))),
% 1.01/1.22      inference('cnf', [status(esa)], [t94_xboole_1])).
% 1.01/1.22  thf('55', plain,
% 1.01/1.22      (![X56 : $i, X57 : $i]:
% 1.01/1.22         ((k3_tarski @ (k2_tarski @ X56 @ X57)) = (k2_xboole_0 @ X56 @ X57))),
% 1.01/1.22      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.01/1.22  thf(t91_xboole_1, axiom,
% 1.01/1.22    (![A:$i,B:$i,C:$i]:
% 1.01/1.22     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 1.01/1.22       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 1.01/1.22  thf('56', plain,
% 1.01/1.22      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.01/1.22         ((k5_xboole_0 @ (k5_xboole_0 @ X19 @ X20) @ X21)
% 1.01/1.22           = (k5_xboole_0 @ X19 @ (k5_xboole_0 @ X20 @ X21)))),
% 1.01/1.22      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.01/1.22  thf('57', plain,
% 1.01/1.22      (![X0 : $i, X1 : $i]:
% 1.01/1.22         ((k4_xboole_0 @ X0 @ X1)
% 1.01/1.22           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.01/1.22      inference('sup+', [status(thm)], ['10', '11'])).
% 1.01/1.22  thf('58', plain,
% 1.01/1.22      (![X22 : $i, X23 : $i]:
% 1.01/1.22         ((k3_tarski @ (k2_tarski @ X22 @ X23))
% 1.01/1.22           = (k5_xboole_0 @ X22 @ (k4_xboole_0 @ X23 @ X22)))),
% 1.01/1.22      inference('demod', [status(thm)], ['54', '55', '56', '57'])).
% 1.01/1.22  thf('59', plain,
% 1.01/1.22      (![X0 : $i]:
% 1.01/1.22         ((k3_tarski @ (k2_tarski @ X0 @ k1_xboole_0))
% 1.01/1.22           = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 1.01/1.22      inference('sup+', [status(thm)], ['53', '58'])).
% 1.01/1.22  thf('60', plain, (![X18 : $i]: ((k5_xboole_0 @ X18 @ k1_xboole_0) = (X18))),
% 1.01/1.22      inference('cnf', [status(esa)], [t5_boole])).
% 1.01/1.22  thf('61', plain,
% 1.01/1.22      (![X0 : $i]: ((k3_tarski @ (k2_tarski @ X0 @ k1_xboole_0)) = (X0))),
% 1.01/1.22      inference('sup+', [status(thm)], ['59', '60'])).
% 1.01/1.22  thf('62', plain,
% 1.01/1.22      (![X16 : $i, X17 : $i]:
% 1.01/1.22         ((k4_xboole_0 @ X16 @ (k3_tarski @ (k2_tarski @ X16 @ X17)))
% 1.01/1.22           = (k1_xboole_0))),
% 1.01/1.22      inference('demod', [status(thm)], ['22', '23'])).
% 1.01/1.22  thf('63', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.01/1.22      inference('sup+', [status(thm)], ['61', '62'])).
% 1.01/1.22  thf('64', plain,
% 1.01/1.22      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 1.01/1.22      inference('sup-', [status(thm)], ['43', '44'])).
% 1.01/1.22  thf('65', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 1.01/1.22      inference('sup+', [status(thm)], ['63', '64'])).
% 1.01/1.22  thf('66', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 1.01/1.22      inference('demod', [status(thm)], ['46', '65'])).
% 1.01/1.22  thf('67', plain,
% 1.01/1.22      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.01/1.22         ((k5_xboole_0 @ (k5_xboole_0 @ X19 @ X20) @ X21)
% 1.01/1.22           = (k5_xboole_0 @ X19 @ (k5_xboole_0 @ X20 @ X21)))),
% 1.01/1.22      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.01/1.22  thf('68', plain,
% 1.01/1.22      (![X0 : $i, X1 : $i]:
% 1.01/1.22         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 1.01/1.22           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.01/1.22      inference('sup+', [status(thm)], ['66', '67'])).
% 1.01/1.22  thf('69', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.01/1.22      inference('sup+', [status(thm)], ['50', '51'])).
% 1.01/1.22  thf('70', plain,
% 1.01/1.22      (![X0 : $i, X1 : $i]:
% 1.01/1.22         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.01/1.22      inference('demod', [status(thm)], ['68', '69'])).
% 1.01/1.22  thf('71', plain,
% 1.01/1.22      (((sk_A) = (k5_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 1.01/1.22      inference('sup+', [status(thm)], ['18', '70'])).
% 1.01/1.22  thf('72', plain,
% 1.01/1.22      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 1.01/1.22      inference('sup-', [status(thm)], ['14', '15'])).
% 1.01/1.22  thf('73', plain,
% 1.01/1.22      (![X14 : $i, X15 : $i]: (r1_tarski @ (k4_xboole_0 @ X14 @ X15) @ X14)),
% 1.01/1.22      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.01/1.22  thf('74', plain, ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_A)),
% 1.01/1.22      inference('sup+', [status(thm)], ['72', '73'])).
% 1.01/1.22  thf('75', plain,
% 1.01/1.22      (![X12 : $i, X13 : $i]:
% 1.01/1.22         (((k3_xboole_0 @ X12 @ X13) = (X12)) | ~ (r1_tarski @ X12 @ X13))),
% 1.01/1.22      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.01/1.22  thf('76', plain,
% 1.01/1.22      (((k3_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ sk_A)
% 1.01/1.22         = (k3_subset_1 @ sk_A @ sk_B))),
% 1.01/1.22      inference('sup-', [status(thm)], ['74', '75'])).
% 1.01/1.22  thf('77', plain,
% 1.01/1.22      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.01/1.22      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.01/1.22  thf('78', plain,
% 1.01/1.22      (((k3_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B))
% 1.01/1.22         = (k3_subset_1 @ sk_A @ sk_B))),
% 1.01/1.22      inference('demod', [status(thm)], ['76', '77'])).
% 1.01/1.22  thf('79', plain,
% 1.01/1.22      (![X5 : $i, X6 : $i]:
% 1.01/1.22         ((k4_xboole_0 @ X5 @ X6)
% 1.01/1.22           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 1.01/1.22      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.01/1.22  thf(t112_xboole_1, axiom,
% 1.01/1.22    (![A:$i,B:$i,C:$i]:
% 1.01/1.22     ( ( k5_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ B ) ) =
% 1.01/1.22       ( k3_xboole_0 @ ( k5_xboole_0 @ A @ C ) @ B ) ))).
% 1.01/1.22  thf('80', plain,
% 1.01/1.22      (![X7 : $i, X8 : $i, X9 : $i]:
% 1.01/1.22         ((k5_xboole_0 @ (k3_xboole_0 @ X7 @ X9) @ (k3_xboole_0 @ X8 @ X9))
% 1.01/1.22           = (k3_xboole_0 @ (k5_xboole_0 @ X7 @ X8) @ X9))),
% 1.01/1.22      inference('cnf', [status(esa)], [t112_xboole_1])).
% 1.01/1.22  thf('81', plain,
% 1.01/1.22      (![X0 : $i, X1 : $i]:
% 1.01/1.22         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0)
% 1.01/1.22           = (k3_xboole_0 @ (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)) @ X0))),
% 1.01/1.22      inference('sup+', [status(thm)], ['79', '80'])).
% 1.01/1.22  thf('82', plain,
% 1.01/1.22      (![X5 : $i, X6 : $i]:
% 1.01/1.22         ((k4_xboole_0 @ X5 @ X6)
% 1.01/1.22           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 1.01/1.22      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.01/1.22  thf('83', plain,
% 1.01/1.22      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.01/1.22      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.01/1.22  thf('84', plain,
% 1.01/1.22      (![X0 : $i, X1 : $i]:
% 1.01/1.22         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0)
% 1.01/1.22           = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.01/1.22      inference('demod', [status(thm)], ['81', '82', '83'])).
% 1.01/1.22  thf('85', plain,
% 1.01/1.22      (((k4_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ 
% 1.01/1.22         (k3_subset_1 @ sk_A @ sk_B))
% 1.01/1.22         = (k3_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ 
% 1.01/1.22            (k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B))))),
% 1.01/1.22      inference('sup+', [status(thm)], ['78', '84'])).
% 1.01/1.22  thf('86', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.01/1.22      inference('sup+', [status(thm)], ['61', '62'])).
% 1.01/1.22  thf('87', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 1.01/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.22  thf(dt_k3_subset_1, axiom,
% 1.01/1.22    (![A:$i,B:$i]:
% 1.01/1.22     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.01/1.22       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 1.01/1.22  thf('88', plain,
% 1.01/1.22      (![X64 : $i, X65 : $i]:
% 1.01/1.22         ((m1_subset_1 @ (k3_subset_1 @ X64 @ X65) @ (k1_zfmisc_1 @ X64))
% 1.01/1.22          | ~ (m1_subset_1 @ X65 @ (k1_zfmisc_1 @ X64)))),
% 1.01/1.22      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 1.01/1.22  thf('89', plain,
% 1.01/1.22      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 1.01/1.22      inference('sup-', [status(thm)], ['87', '88'])).
% 1.01/1.22  thf('90', plain,
% 1.01/1.22      (![X62 : $i, X63 : $i]:
% 1.01/1.22         (((k3_subset_1 @ X62 @ X63) = (k4_xboole_0 @ X62 @ X63))
% 1.01/1.22          | ~ (m1_subset_1 @ X63 @ (k1_zfmisc_1 @ X62)))),
% 1.01/1.22      inference('cnf', [status(esa)], [d5_subset_1])).
% 1.01/1.22  thf('91', plain,
% 1.01/1.22      (((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B))
% 1.01/1.22         = (k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)))),
% 1.01/1.22      inference('sup-', [status(thm)], ['89', '90'])).
% 1.01/1.22  thf('92', plain,
% 1.01/1.22      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 1.01/1.22      inference('demod', [status(thm)], ['21', '45'])).
% 1.01/1.22  thf('93', plain,
% 1.01/1.22      (((k3_subset_1 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_B @ sk_A))),
% 1.01/1.22      inference('demod', [status(thm)], ['13', '16', '17'])).
% 1.01/1.22  thf('94', plain,
% 1.01/1.22      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.01/1.22         ((k5_xboole_0 @ (k5_xboole_0 @ X19 @ X20) @ X21)
% 1.01/1.22           = (k5_xboole_0 @ X19 @ (k5_xboole_0 @ X20 @ X21)))),
% 1.01/1.22      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.01/1.22  thf('95', plain,
% 1.01/1.22      (![X0 : $i]:
% 1.01/1.22         ((k5_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ X0)
% 1.01/1.22           = (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_A @ X0)))),
% 1.01/1.22      inference('sup+', [status(thm)], ['93', '94'])).
% 1.01/1.22  thf('96', plain,
% 1.01/1.22      (((k5_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ sk_A)
% 1.01/1.22         = (k5_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_A)))),
% 1.01/1.22      inference('sup+', [status(thm)], ['92', '95'])).
% 1.01/1.22  thf('97', plain,
% 1.01/1.22      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 1.01/1.22      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.01/1.22  thf('98', plain,
% 1.01/1.22      (((k5_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B))
% 1.01/1.22         = (k5_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_A)))),
% 1.01/1.22      inference('demod', [status(thm)], ['96', '97'])).
% 1.01/1.22  thf('99', plain,
% 1.01/1.22      (((k3_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B))
% 1.01/1.22         = (k3_subset_1 @ sk_A @ sk_B))),
% 1.01/1.22      inference('demod', [status(thm)], ['76', '77'])).
% 1.01/1.22  thf('100', plain,
% 1.01/1.22      (![X5 : $i, X6 : $i]:
% 1.01/1.22         ((k4_xboole_0 @ X5 @ X6)
% 1.01/1.22           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 1.01/1.22      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.01/1.22  thf('101', plain,
% 1.01/1.22      (((k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B))
% 1.01/1.22         = (k5_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)))),
% 1.01/1.22      inference('sup+', [status(thm)], ['99', '100'])).
% 1.01/1.22  thf('102', plain,
% 1.01/1.22      (((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B))
% 1.01/1.22         = (k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)))),
% 1.01/1.22      inference('sup-', [status(thm)], ['89', '90'])).
% 1.01/1.22  thf('103', plain,
% 1.01/1.22      (((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B))
% 1.01/1.22         = (k5_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)))),
% 1.01/1.22      inference('demod', [status(thm)], ['101', '102'])).
% 1.01/1.22  thf('104', plain,
% 1.01/1.22      (((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B))
% 1.01/1.22         = (k5_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_A)))),
% 1.01/1.22      inference('sup+', [status(thm)], ['98', '103'])).
% 1.01/1.22  thf('105', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 1.01/1.22      inference('sup+', [status(thm)], ['63', '64'])).
% 1.01/1.22  thf('106', plain,
% 1.01/1.22      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 1.01/1.22      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.01/1.22  thf('107', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.01/1.22      inference('sup+', [status(thm)], ['50', '51'])).
% 1.01/1.22  thf('108', plain,
% 1.01/1.22      (((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)) = (sk_B))),
% 1.01/1.22      inference('demod', [status(thm)], ['104', '105', '106', '107'])).
% 1.01/1.22  thf('109', plain,
% 1.01/1.22      (((sk_B) = (k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)))),
% 1.01/1.22      inference('demod', [status(thm)], ['91', '108'])).
% 1.01/1.22  thf('110', plain,
% 1.01/1.22      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.01/1.22      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.01/1.22  thf('111', plain,
% 1.01/1.22      (((k1_xboole_0) = (k3_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 1.01/1.22      inference('demod', [status(thm)], ['85', '86', '109', '110'])).
% 1.01/1.22  thf('112', plain,
% 1.01/1.22      (![X0 : $i, X1 : $i]:
% 1.01/1.22         ((k4_xboole_0 @ X0 @ X1)
% 1.01/1.22           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.01/1.22      inference('sup+', [status(thm)], ['10', '11'])).
% 1.01/1.22  thf('113', plain,
% 1.01/1.22      (((k4_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)
% 1.01/1.22         = (k5_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ k1_xboole_0))),
% 1.01/1.22      inference('sup+', [status(thm)], ['111', '112'])).
% 1.01/1.22  thf('114', plain,
% 1.01/1.22      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 1.01/1.22      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.01/1.22  thf('115', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.01/1.22      inference('sup+', [status(thm)], ['50', '51'])).
% 1.01/1.22  thf('116', plain,
% 1.01/1.22      (((k4_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)
% 1.01/1.22         = (k3_subset_1 @ sk_A @ sk_B))),
% 1.01/1.22      inference('demod', [status(thm)], ['113', '114', '115'])).
% 1.01/1.22  thf('117', plain,
% 1.01/1.22      (![X22 : $i, X23 : $i]:
% 1.01/1.22         ((k3_tarski @ (k2_tarski @ X22 @ X23))
% 1.01/1.22           = (k5_xboole_0 @ X22 @ (k4_xboole_0 @ X23 @ X22)))),
% 1.01/1.22      inference('demod', [status(thm)], ['54', '55', '56', '57'])).
% 1.01/1.22  thf('118', plain,
% 1.01/1.22      (((k3_tarski @ (k2_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))
% 1.01/1.22         = (k5_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 1.01/1.22      inference('sup+', [status(thm)], ['116', '117'])).
% 1.01/1.22  thf('119', plain,
% 1.01/1.22      (((k3_tarski @ (k2_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))) = (sk_A))),
% 1.01/1.22      inference('sup+', [status(thm)], ['71', '118'])).
% 1.01/1.22  thf('120', plain,
% 1.01/1.22      (((k4_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 1.01/1.22         != (k2_subset_1 @ sk_A))),
% 1.01/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.22  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 1.01/1.22  thf('121', plain, (![X61 : $i]: ((k2_subset_1 @ X61) = (X61))),
% 1.01/1.22      inference('cnf', [status(esa)], [d4_subset_1])).
% 1.01/1.22  thf('122', plain,
% 1.01/1.22      (((k4_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)) != (sk_A))),
% 1.01/1.22      inference('demod', [status(thm)], ['120', '121'])).
% 1.01/1.22  thf('123', plain,
% 1.01/1.22      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 1.01/1.22      inference('sup-', [status(thm)], ['87', '88'])).
% 1.01/1.22  thf('124', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 1.01/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.22  thf(redefinition_k4_subset_1, axiom,
% 1.01/1.22    (![A:$i,B:$i,C:$i]:
% 1.01/1.22     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 1.01/1.22         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.01/1.22       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 1.01/1.22  thf('125', plain,
% 1.01/1.22      (![X67 : $i, X68 : $i, X69 : $i]:
% 1.01/1.22         (~ (m1_subset_1 @ X67 @ (k1_zfmisc_1 @ X68))
% 1.01/1.22          | ~ (m1_subset_1 @ X69 @ (k1_zfmisc_1 @ X68))
% 1.01/1.22          | ((k4_subset_1 @ X68 @ X67 @ X69) = (k2_xboole_0 @ X67 @ X69)))),
% 1.01/1.22      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 1.01/1.22  thf('126', plain,
% 1.01/1.22      (![X56 : $i, X57 : $i]:
% 1.01/1.22         ((k3_tarski @ (k2_tarski @ X56 @ X57)) = (k2_xboole_0 @ X56 @ X57))),
% 1.01/1.22      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.01/1.22  thf('127', plain,
% 1.01/1.22      (![X67 : $i, X68 : $i, X69 : $i]:
% 1.01/1.22         (~ (m1_subset_1 @ X67 @ (k1_zfmisc_1 @ X68))
% 1.01/1.22          | ~ (m1_subset_1 @ X69 @ (k1_zfmisc_1 @ X68))
% 1.01/1.22          | ((k4_subset_1 @ X68 @ X67 @ X69)
% 1.01/1.22              = (k3_tarski @ (k2_tarski @ X67 @ X69))))),
% 1.01/1.22      inference('demod', [status(thm)], ['125', '126'])).
% 1.01/1.22  thf('128', plain,
% 1.01/1.22      (![X0 : $i]:
% 1.01/1.22         (((k4_subset_1 @ sk_A @ sk_B @ X0)
% 1.01/1.22            = (k3_tarski @ (k2_tarski @ sk_B @ X0)))
% 1.01/1.22          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 1.01/1.22      inference('sup-', [status(thm)], ['124', '127'])).
% 1.01/1.22  thf('129', plain,
% 1.01/1.22      (((k4_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 1.01/1.22         = (k3_tarski @ (k2_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))))),
% 1.01/1.22      inference('sup-', [status(thm)], ['123', '128'])).
% 1.01/1.22  thf('130', plain,
% 1.01/1.22      (((k3_tarski @ (k2_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))
% 1.01/1.22         != (sk_A))),
% 1.01/1.22      inference('demod', [status(thm)], ['122', '129'])).
% 1.01/1.22  thf('131', plain, ($false),
% 1.01/1.22      inference('simplify_reflect-', [status(thm)], ['119', '130'])).
% 1.01/1.22  
% 1.01/1.22  % SZS output end Refutation
% 1.01/1.22  
% 1.07/1.23  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
