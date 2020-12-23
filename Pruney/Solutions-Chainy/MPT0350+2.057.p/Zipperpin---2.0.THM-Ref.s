%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ieG2p4fhvB

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:53 EST 2020

% Result     : Theorem 1.05s
% Output     : Refutation 1.05s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 264 expanded)
%              Number of leaves         :   34 ( 101 expanded)
%              Depth                    :   13
%              Number of atoms          :  859 (2159 expanded)
%              Number of equality atoms :   85 ( 212 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

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
    ( k4_subset_1 @ sk_A @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
 != ( k2_subset_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('1',plain,(
    ! [X56: $i] :
      ( ( k2_subset_1 @ X56 )
      = X56 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('2',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
 != sk_A ),
    inference(demod,[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X57: $i,X58: $i] :
      ( ( ( k3_subset_1 @ X57 @ X58 )
        = ( k4_xboole_0 @ X57 @ X58 ) )
      | ~ ( m1_subset_1 @ X58 @ ( k1_zfmisc_1 @ X57 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('5',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) )
 != sk_A ),
    inference(demod,[status(thm)],['2','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('8',plain,(
    ! [X59: $i,X60: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X59 @ X60 ) @ ( k1_zfmisc_1 @ X59 ) )
      | ~ ( m1_subset_1 @ X60 @ ( k1_zfmisc_1 @ X59 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('9',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('11',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('13',plain,(
    ! [X62: $i,X63: $i,X64: $i] :
      ( ~ ( m1_subset_1 @ X62 @ ( k1_zfmisc_1 @ X63 ) )
      | ~ ( m1_subset_1 @ X64 @ ( k1_zfmisc_1 @ X63 ) )
      | ( ( k4_subset_1 @ X63 @ X62 @ X64 )
        = ( k2_xboole_0 @ X62 @ X64 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('14',plain,(
    ! [X51: $i,X52: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X51 @ X52 ) )
      = ( k2_xboole_0 @ X51 @ X52 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('15',plain,(
    ! [X62: $i,X63: $i,X64: $i] :
      ( ~ ( m1_subset_1 @ X62 @ ( k1_zfmisc_1 @ X63 ) )
      | ~ ( m1_subset_1 @ X64 @ ( k1_zfmisc_1 @ X63 ) )
      | ( ( k4_subset_1 @ X63 @ X62 @ X64 )
        = ( k3_tarski @ ( k2_tarski @ X62 @ X64 ) ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ sk_A @ sk_B @ X0 )
        = ( k3_tarski @ ( k2_tarski @ sk_B @ X0 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = ( k3_tarski @ ( k2_tarski @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['11','16'])).

thf('18',plain,(
    ( k3_tarski @ ( k2_tarski @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) ) )
 != sk_A ),
    inference(demod,[status(thm)],['6','17'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('19',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf(t112_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ B ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ A @ C ) @ B ) ) )).

thf('20',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X7 @ X9 ) @ ( k3_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X7 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t112_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf(t94_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('25',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X17 @ X18 ) @ ( k3_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t94_xboole_1])).

thf('26',plain,(
    ! [X51: $i,X52: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X51 @ X52 ) )
      = ( k2_xboole_0 @ X51 @ X52 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('27',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X14 @ X15 ) @ X16 )
      = ( k5_xboole_0 @ X14 @ ( k5_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('29',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X17 @ X18 ) )
      = ( k5_xboole_0 @ X17 @ ( k4_xboole_0 @ X18 @ X17 ) ) ) ),
    inference(demod,[status(thm)],['25','26','27','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['24','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = A ) )).

thf('34',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) )
      = X10 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('35',plain,(
    ! [X51: $i,X52: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X51 @ X52 ) )
      = ( k2_xboole_0 @ X51 @ X52 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('36',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) )
      = X10 ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['33','36'])).

thf('38',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['32','37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['32','37','38'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X17 @ X18 ) )
      = ( k5_xboole_0 @ X17 @ ( k4_xboole_0 @ X18 @ X17 ) ) ) ),
    inference(demod,[status(thm)],['25','26','27','30'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X17 @ X18 ) )
      = ( k5_xboole_0 @ X17 @ ( k4_xboole_0 @ X18 @ X17 ) ) ) ),
    inference(demod,[status(thm)],['25','26','27','30'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X0 @ X1 ) )
      = ( k3_tarski @ ( k2_tarski @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
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

thf('47',plain,(
    ! [X53: $i,X54: $i] :
      ( ~ ( m1_subset_1 @ X53 @ X54 )
      | ( r2_hidden @ X53 @ X54 )
      | ( v1_xboole_0 @ X54 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('48',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('49',plain,(
    ! [X61: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X61 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('50',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['48','49'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('51',plain,(
    ! [X47: $i,X48: $i,X49: $i] :
      ( ~ ( r2_hidden @ X49 @ X48 )
      | ( r1_tarski @ X49 @ X47 )
      | ( X48
       != ( k1_zfmisc_1 @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('52',plain,(
    ! [X47: $i,X49: $i] :
      ( ( r1_tarski @ X49 @ X47 )
      | ~ ( r2_hidden @ X49 @ ( k1_zfmisc_1 @ X47 ) ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['50','52'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('54',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_xboole_0 @ X12 @ X13 )
        = X12 )
      | ~ ( r1_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('55',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('57',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('58',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('59',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['57','58'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('60',plain,(
    ! [X4: $i] :
      ( ( k3_xboole_0 @ X4 @ X4 )
      = X4 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('61',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X14 @ X15 ) @ X16 )
      = ( k5_xboole_0 @ X14 @ ( k5_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,
    ( ( k5_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_B ) @ sk_A )
    = ( k5_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['59','64'])).

thf('66',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('67',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X17 @ X18 ) )
      = ( k5_xboole_0 @ X17 @ ( k4_xboole_0 @ X18 @ X17 ) ) ) ),
    inference(demod,[status(thm)],['25','26','27','30'])).

thf('68',plain,
    ( ( k5_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_B ) )
    = ( k3_tarski @ ( k2_tarski @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['65','66','67'])).

thf('69',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['53','54'])).

thf('70',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('71',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_A )
    = ( k5_xboole_0 @ sk_B @ sk_B ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('73',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_A )
    = ( k4_xboole_0 @ sk_B @ sk_B ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X17 @ X18 ) )
      = ( k5_xboole_0 @ X17 @ ( k4_xboole_0 @ X18 @ X17 ) ) ) ),
    inference(demod,[status(thm)],['25','26','27','30'])).

thf('75',plain,
    ( ( k3_tarski @ ( k2_tarski @ sk_A @ sk_B ) )
    = ( k5_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_B ) ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['53','54'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['33','36'])).

thf('78',plain,
    ( ( k3_tarski @ ( k2_tarski @ sk_A @ sk_B ) )
    = sk_A ),
    inference('sup+',[status(thm)],['76','77'])).

thf('79',plain,
    ( sk_A
    = ( k5_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_B ) ) ),
    inference(demod,[status(thm)],['75','78'])).

thf('80',plain,
    ( sk_A
    = ( k3_tarski @ ( k2_tarski @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['68','79'])).

thf('81',plain,(
    sk_A != sk_A ),
    inference(demod,[status(thm)],['18','45','80'])).

thf('82',plain,(
    $false ),
    inference(simplify,[status(thm)],['81'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ieG2p4fhvB
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 09:55:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 1.05/1.24  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.05/1.24  % Solved by: fo/fo7.sh
% 1.05/1.24  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.05/1.24  % done 843 iterations in 0.792s
% 1.05/1.24  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.05/1.24  % SZS output start Refutation
% 1.05/1.24  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.05/1.24  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.05/1.24  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.05/1.24  thf(sk_A_type, type, sk_A: $i).
% 1.05/1.24  thf(sk_B_type, type, sk_B: $i).
% 1.05/1.24  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 1.05/1.24  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.05/1.24  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.05/1.24  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 1.05/1.24  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.05/1.24  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.05/1.24  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 1.05/1.24  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 1.05/1.24  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.05/1.24  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.05/1.24  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.05/1.24  thf(t25_subset_1, conjecture,
% 1.05/1.24    (![A:$i,B:$i]:
% 1.05/1.24     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.05/1.24       ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) ) =
% 1.05/1.24         ( k2_subset_1 @ A ) ) ))).
% 1.05/1.24  thf(zf_stmt_0, negated_conjecture,
% 1.05/1.24    (~( ![A:$i,B:$i]:
% 1.05/1.24        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.05/1.24          ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) ) =
% 1.05/1.24            ( k2_subset_1 @ A ) ) ) )),
% 1.05/1.24    inference('cnf.neg', [status(esa)], [t25_subset_1])).
% 1.05/1.24  thf('0', plain,
% 1.05/1.24      (((k4_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 1.05/1.24         != (k2_subset_1 @ sk_A))),
% 1.05/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.24  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 1.05/1.24  thf('1', plain, (![X56 : $i]: ((k2_subset_1 @ X56) = (X56))),
% 1.05/1.24      inference('cnf', [status(esa)], [d4_subset_1])).
% 1.05/1.24  thf('2', plain,
% 1.05/1.24      (((k4_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)) != (sk_A))),
% 1.05/1.24      inference('demod', [status(thm)], ['0', '1'])).
% 1.05/1.24  thf('3', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 1.05/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.24  thf(d5_subset_1, axiom,
% 1.05/1.24    (![A:$i,B:$i]:
% 1.05/1.24     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.05/1.24       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 1.05/1.24  thf('4', plain,
% 1.05/1.24      (![X57 : $i, X58 : $i]:
% 1.05/1.24         (((k3_subset_1 @ X57 @ X58) = (k4_xboole_0 @ X57 @ X58))
% 1.05/1.24          | ~ (m1_subset_1 @ X58 @ (k1_zfmisc_1 @ X57)))),
% 1.05/1.24      inference('cnf', [status(esa)], [d5_subset_1])).
% 1.05/1.24  thf('5', plain,
% 1.05/1.24      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 1.05/1.24      inference('sup-', [status(thm)], ['3', '4'])).
% 1.05/1.24  thf('6', plain,
% 1.05/1.24      (((k4_subset_1 @ sk_A @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B)) != (sk_A))),
% 1.05/1.24      inference('demod', [status(thm)], ['2', '5'])).
% 1.05/1.24  thf('7', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 1.05/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.24  thf(dt_k3_subset_1, axiom,
% 1.05/1.24    (![A:$i,B:$i]:
% 1.05/1.24     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.05/1.24       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 1.05/1.24  thf('8', plain,
% 1.05/1.24      (![X59 : $i, X60 : $i]:
% 1.05/1.24         ((m1_subset_1 @ (k3_subset_1 @ X59 @ X60) @ (k1_zfmisc_1 @ X59))
% 1.05/1.24          | ~ (m1_subset_1 @ X60 @ (k1_zfmisc_1 @ X59)))),
% 1.05/1.24      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 1.05/1.24  thf('9', plain,
% 1.05/1.24      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 1.05/1.24      inference('sup-', [status(thm)], ['7', '8'])).
% 1.05/1.24  thf('10', plain,
% 1.05/1.24      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 1.05/1.24      inference('sup-', [status(thm)], ['3', '4'])).
% 1.05/1.24  thf('11', plain,
% 1.05/1.24      ((m1_subset_1 @ (k4_xboole_0 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 1.05/1.24      inference('demod', [status(thm)], ['9', '10'])).
% 1.05/1.24  thf('12', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 1.05/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.24  thf(redefinition_k4_subset_1, axiom,
% 1.05/1.24    (![A:$i,B:$i,C:$i]:
% 1.05/1.24     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 1.05/1.24         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.05/1.24       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 1.05/1.24  thf('13', plain,
% 1.05/1.24      (![X62 : $i, X63 : $i, X64 : $i]:
% 1.05/1.24         (~ (m1_subset_1 @ X62 @ (k1_zfmisc_1 @ X63))
% 1.05/1.24          | ~ (m1_subset_1 @ X64 @ (k1_zfmisc_1 @ X63))
% 1.05/1.24          | ((k4_subset_1 @ X63 @ X62 @ X64) = (k2_xboole_0 @ X62 @ X64)))),
% 1.05/1.24      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 1.05/1.24  thf(l51_zfmisc_1, axiom,
% 1.05/1.24    (![A:$i,B:$i]:
% 1.05/1.24     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 1.05/1.24  thf('14', plain,
% 1.05/1.24      (![X51 : $i, X52 : $i]:
% 1.05/1.24         ((k3_tarski @ (k2_tarski @ X51 @ X52)) = (k2_xboole_0 @ X51 @ X52))),
% 1.05/1.24      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.05/1.24  thf('15', plain,
% 1.05/1.24      (![X62 : $i, X63 : $i, X64 : $i]:
% 1.05/1.24         (~ (m1_subset_1 @ X62 @ (k1_zfmisc_1 @ X63))
% 1.05/1.24          | ~ (m1_subset_1 @ X64 @ (k1_zfmisc_1 @ X63))
% 1.05/1.24          | ((k4_subset_1 @ X63 @ X62 @ X64)
% 1.05/1.24              = (k3_tarski @ (k2_tarski @ X62 @ X64))))),
% 1.05/1.24      inference('demod', [status(thm)], ['13', '14'])).
% 1.05/1.24  thf('16', plain,
% 1.05/1.24      (![X0 : $i]:
% 1.05/1.24         (((k4_subset_1 @ sk_A @ sk_B @ X0)
% 1.05/1.24            = (k3_tarski @ (k2_tarski @ sk_B @ X0)))
% 1.05/1.24          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 1.05/1.24      inference('sup-', [status(thm)], ['12', '15'])).
% 1.05/1.24  thf('17', plain,
% 1.05/1.24      (((k4_subset_1 @ sk_A @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B))
% 1.05/1.24         = (k3_tarski @ (k2_tarski @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B))))),
% 1.05/1.24      inference('sup-', [status(thm)], ['11', '16'])).
% 1.05/1.24  thf('18', plain,
% 1.05/1.24      (((k3_tarski @ (k2_tarski @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B)))
% 1.05/1.24         != (sk_A))),
% 1.05/1.24      inference('demod', [status(thm)], ['6', '17'])).
% 1.05/1.24  thf(t100_xboole_1, axiom,
% 1.05/1.24    (![A:$i,B:$i]:
% 1.05/1.24     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.05/1.24  thf('19', plain,
% 1.05/1.24      (![X5 : $i, X6 : $i]:
% 1.05/1.24         ((k4_xboole_0 @ X5 @ X6)
% 1.05/1.24           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 1.05/1.24      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.05/1.24  thf(t112_xboole_1, axiom,
% 1.05/1.24    (![A:$i,B:$i,C:$i]:
% 1.05/1.24     ( ( k5_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ B ) ) =
% 1.05/1.24       ( k3_xboole_0 @ ( k5_xboole_0 @ A @ C ) @ B ) ))).
% 1.05/1.24  thf('20', plain,
% 1.05/1.24      (![X7 : $i, X8 : $i, X9 : $i]:
% 1.05/1.24         ((k5_xboole_0 @ (k3_xboole_0 @ X7 @ X9) @ (k3_xboole_0 @ X8 @ X9))
% 1.05/1.24           = (k3_xboole_0 @ (k5_xboole_0 @ X7 @ X8) @ X9))),
% 1.05/1.24      inference('cnf', [status(esa)], [t112_xboole_1])).
% 1.05/1.24  thf('21', plain,
% 1.05/1.24      (![X0 : $i, X1 : $i]:
% 1.05/1.24         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0)
% 1.05/1.24           = (k3_xboole_0 @ (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)) @ X0))),
% 1.05/1.24      inference('sup+', [status(thm)], ['19', '20'])).
% 1.05/1.24  thf('22', plain,
% 1.05/1.24      (![X5 : $i, X6 : $i]:
% 1.05/1.24         ((k4_xboole_0 @ X5 @ X6)
% 1.05/1.24           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 1.05/1.24      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.05/1.24  thf(commutativity_k3_xboole_0, axiom,
% 1.05/1.24    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 1.05/1.24  thf('23', plain,
% 1.05/1.24      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.05/1.24      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.05/1.24  thf('24', plain,
% 1.05/1.24      (![X0 : $i, X1 : $i]:
% 1.05/1.24         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0)
% 1.05/1.24           = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.05/1.24      inference('demod', [status(thm)], ['21', '22', '23'])).
% 1.05/1.24  thf(t94_xboole_1, axiom,
% 1.05/1.24    (![A:$i,B:$i]:
% 1.05/1.24     ( ( k2_xboole_0 @ A @ B ) =
% 1.05/1.24       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.05/1.24  thf('25', plain,
% 1.05/1.24      (![X17 : $i, X18 : $i]:
% 1.05/1.24         ((k2_xboole_0 @ X17 @ X18)
% 1.05/1.24           = (k5_xboole_0 @ (k5_xboole_0 @ X17 @ X18) @ 
% 1.05/1.24              (k3_xboole_0 @ X17 @ X18)))),
% 1.05/1.24      inference('cnf', [status(esa)], [t94_xboole_1])).
% 1.05/1.24  thf('26', plain,
% 1.05/1.24      (![X51 : $i, X52 : $i]:
% 1.05/1.24         ((k3_tarski @ (k2_tarski @ X51 @ X52)) = (k2_xboole_0 @ X51 @ X52))),
% 1.05/1.24      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.05/1.24  thf(t91_xboole_1, axiom,
% 1.05/1.24    (![A:$i,B:$i,C:$i]:
% 1.05/1.24     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 1.05/1.24       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 1.05/1.24  thf('27', plain,
% 1.05/1.24      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.05/1.24         ((k5_xboole_0 @ (k5_xboole_0 @ X14 @ X15) @ X16)
% 1.05/1.24           = (k5_xboole_0 @ X14 @ (k5_xboole_0 @ X15 @ X16)))),
% 1.05/1.24      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.05/1.24  thf('28', plain,
% 1.05/1.24      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.05/1.24      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.05/1.24  thf('29', plain,
% 1.05/1.24      (![X5 : $i, X6 : $i]:
% 1.05/1.24         ((k4_xboole_0 @ X5 @ X6)
% 1.05/1.24           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 1.05/1.24      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.05/1.24  thf('30', plain,
% 1.05/1.24      (![X0 : $i, X1 : $i]:
% 1.05/1.24         ((k4_xboole_0 @ X0 @ X1)
% 1.05/1.24           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.05/1.24      inference('sup+', [status(thm)], ['28', '29'])).
% 1.05/1.24  thf('31', plain,
% 1.05/1.24      (![X17 : $i, X18 : $i]:
% 1.05/1.24         ((k3_tarski @ (k2_tarski @ X17 @ X18))
% 1.05/1.24           = (k5_xboole_0 @ X17 @ (k4_xboole_0 @ X18 @ X17)))),
% 1.05/1.24      inference('demod', [status(thm)], ['25', '26', '27', '30'])).
% 1.05/1.24  thf('32', plain,
% 1.05/1.24      (![X0 : $i, X1 : $i]:
% 1.05/1.24         ((k3_tarski @ (k2_tarski @ X0 @ (k3_xboole_0 @ X1 @ X0)))
% 1.05/1.24           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))))),
% 1.05/1.24      inference('sup+', [status(thm)], ['24', '31'])).
% 1.05/1.24  thf('33', plain,
% 1.05/1.24      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.05/1.24      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.05/1.24  thf(t22_xboole_1, axiom,
% 1.05/1.24    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 1.05/1.24  thf('34', plain,
% 1.05/1.24      (![X10 : $i, X11 : $i]:
% 1.05/1.24         ((k2_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)) = (X10))),
% 1.05/1.24      inference('cnf', [status(esa)], [t22_xboole_1])).
% 1.05/1.24  thf('35', plain,
% 1.05/1.24      (![X51 : $i, X52 : $i]:
% 1.05/1.24         ((k3_tarski @ (k2_tarski @ X51 @ X52)) = (k2_xboole_0 @ X51 @ X52))),
% 1.05/1.24      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.05/1.24  thf('36', plain,
% 1.05/1.24      (![X10 : $i, X11 : $i]:
% 1.05/1.24         ((k3_tarski @ (k2_tarski @ X10 @ (k3_xboole_0 @ X10 @ X11))) = (X10))),
% 1.05/1.24      inference('demod', [status(thm)], ['34', '35'])).
% 1.05/1.24  thf('37', plain,
% 1.05/1.24      (![X0 : $i, X1 : $i]:
% 1.05/1.24         ((k3_tarski @ (k2_tarski @ X0 @ (k3_xboole_0 @ X1 @ X0))) = (X0))),
% 1.05/1.24      inference('sup+', [status(thm)], ['33', '36'])).
% 1.05/1.24  thf('38', plain,
% 1.05/1.24      (![X5 : $i, X6 : $i]:
% 1.05/1.24         ((k4_xboole_0 @ X5 @ X6)
% 1.05/1.24           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 1.05/1.24      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.05/1.24  thf('39', plain,
% 1.05/1.24      (![X0 : $i, X1 : $i]:
% 1.05/1.24         ((X0) = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.05/1.24      inference('demod', [status(thm)], ['32', '37', '38'])).
% 1.05/1.24  thf('40', plain,
% 1.05/1.24      (![X0 : $i, X1 : $i]:
% 1.05/1.24         ((X0) = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.05/1.24      inference('demod', [status(thm)], ['32', '37', '38'])).
% 1.05/1.24  thf('41', plain,
% 1.05/1.24      (![X0 : $i, X1 : $i]:
% 1.05/1.24         ((k4_xboole_0 @ X1 @ X0)
% 1.05/1.24           = (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 1.05/1.24      inference('sup+', [status(thm)], ['39', '40'])).
% 1.05/1.24  thf('42', plain,
% 1.05/1.24      (![X17 : $i, X18 : $i]:
% 1.05/1.24         ((k3_tarski @ (k2_tarski @ X17 @ X18))
% 1.05/1.24           = (k5_xboole_0 @ X17 @ (k4_xboole_0 @ X18 @ X17)))),
% 1.05/1.24      inference('demod', [status(thm)], ['25', '26', '27', '30'])).
% 1.05/1.24  thf('43', plain,
% 1.05/1.24      (![X0 : $i, X1 : $i]:
% 1.05/1.24         ((k3_tarski @ (k2_tarski @ X0 @ (k4_xboole_0 @ X1 @ X0)))
% 1.05/1.24           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.05/1.24      inference('sup+', [status(thm)], ['41', '42'])).
% 1.05/1.24  thf('44', plain,
% 1.05/1.24      (![X17 : $i, X18 : $i]:
% 1.05/1.24         ((k3_tarski @ (k2_tarski @ X17 @ X18))
% 1.05/1.24           = (k5_xboole_0 @ X17 @ (k4_xboole_0 @ X18 @ X17)))),
% 1.05/1.24      inference('demod', [status(thm)], ['25', '26', '27', '30'])).
% 1.05/1.24  thf('45', plain,
% 1.05/1.24      (![X0 : $i, X1 : $i]:
% 1.05/1.24         ((k3_tarski @ (k2_tarski @ X0 @ X1))
% 1.05/1.24           = (k3_tarski @ (k2_tarski @ X0 @ (k4_xboole_0 @ X1 @ X0))))),
% 1.05/1.24      inference('sup+', [status(thm)], ['43', '44'])).
% 1.05/1.24  thf('46', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 1.05/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.24  thf(d2_subset_1, axiom,
% 1.05/1.24    (![A:$i,B:$i]:
% 1.05/1.24     ( ( ( v1_xboole_0 @ A ) =>
% 1.05/1.24         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 1.05/1.24       ( ( ~( v1_xboole_0 @ A ) ) =>
% 1.05/1.24         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 1.05/1.24  thf('47', plain,
% 1.05/1.24      (![X53 : $i, X54 : $i]:
% 1.05/1.24         (~ (m1_subset_1 @ X53 @ X54)
% 1.05/1.24          | (r2_hidden @ X53 @ X54)
% 1.05/1.24          | (v1_xboole_0 @ X54))),
% 1.05/1.24      inference('cnf', [status(esa)], [d2_subset_1])).
% 1.05/1.24  thf('48', plain,
% 1.05/1.24      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 1.05/1.24        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 1.05/1.24      inference('sup-', [status(thm)], ['46', '47'])).
% 1.05/1.24  thf(fc1_subset_1, axiom,
% 1.05/1.24    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 1.05/1.24  thf('49', plain, (![X61 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X61))),
% 1.05/1.24      inference('cnf', [status(esa)], [fc1_subset_1])).
% 1.05/1.24  thf('50', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 1.05/1.24      inference('clc', [status(thm)], ['48', '49'])).
% 1.05/1.24  thf(d1_zfmisc_1, axiom,
% 1.05/1.24    (![A:$i,B:$i]:
% 1.05/1.24     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 1.05/1.24       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 1.05/1.24  thf('51', plain,
% 1.05/1.24      (![X47 : $i, X48 : $i, X49 : $i]:
% 1.05/1.24         (~ (r2_hidden @ X49 @ X48)
% 1.05/1.24          | (r1_tarski @ X49 @ X47)
% 1.05/1.24          | ((X48) != (k1_zfmisc_1 @ X47)))),
% 1.05/1.24      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 1.05/1.24  thf('52', plain,
% 1.05/1.24      (![X47 : $i, X49 : $i]:
% 1.05/1.24         ((r1_tarski @ X49 @ X47) | ~ (r2_hidden @ X49 @ (k1_zfmisc_1 @ X47)))),
% 1.05/1.24      inference('simplify', [status(thm)], ['51'])).
% 1.05/1.24  thf('53', plain, ((r1_tarski @ sk_B @ sk_A)),
% 1.05/1.24      inference('sup-', [status(thm)], ['50', '52'])).
% 1.05/1.24  thf(t28_xboole_1, axiom,
% 1.05/1.24    (![A:$i,B:$i]:
% 1.05/1.24     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.05/1.24  thf('54', plain,
% 1.05/1.24      (![X12 : $i, X13 : $i]:
% 1.05/1.24         (((k3_xboole_0 @ X12 @ X13) = (X12)) | ~ (r1_tarski @ X12 @ X13))),
% 1.05/1.24      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.05/1.24  thf('55', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 1.05/1.24      inference('sup-', [status(thm)], ['53', '54'])).
% 1.05/1.24  thf('56', plain,
% 1.05/1.24      (![X0 : $i, X1 : $i]:
% 1.05/1.24         ((k4_xboole_0 @ X0 @ X1)
% 1.05/1.24           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.05/1.24      inference('sup+', [status(thm)], ['28', '29'])).
% 1.05/1.24  thf('57', plain,
% 1.05/1.24      (((k4_xboole_0 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 1.05/1.24      inference('sup+', [status(thm)], ['55', '56'])).
% 1.05/1.24  thf(commutativity_k5_xboole_0, axiom,
% 1.05/1.24    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 1.05/1.24  thf('58', plain,
% 1.05/1.24      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 1.05/1.24      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.05/1.24  thf('59', plain,
% 1.05/1.24      (((k4_xboole_0 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_B @ sk_A))),
% 1.05/1.24      inference('demod', [status(thm)], ['57', '58'])).
% 1.05/1.24  thf(idempotence_k3_xboole_0, axiom,
% 1.05/1.24    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 1.05/1.24  thf('60', plain, (![X4 : $i]: ((k3_xboole_0 @ X4 @ X4) = (X4))),
% 1.05/1.24      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 1.05/1.24  thf('61', plain,
% 1.05/1.24      (![X5 : $i, X6 : $i]:
% 1.05/1.24         ((k4_xboole_0 @ X5 @ X6)
% 1.05/1.24           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 1.05/1.24      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.05/1.24  thf('62', plain,
% 1.05/1.24      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 1.05/1.24      inference('sup+', [status(thm)], ['60', '61'])).
% 1.05/1.24  thf('63', plain,
% 1.05/1.24      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.05/1.24         ((k5_xboole_0 @ (k5_xboole_0 @ X14 @ X15) @ X16)
% 1.05/1.24           = (k5_xboole_0 @ X14 @ (k5_xboole_0 @ X15 @ X16)))),
% 1.05/1.24      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.05/1.24  thf('64', plain,
% 1.05/1.24      (![X0 : $i, X1 : $i]:
% 1.05/1.24         ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X1)
% 1.05/1.24           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 1.05/1.24      inference('sup+', [status(thm)], ['62', '63'])).
% 1.05/1.24  thf('65', plain,
% 1.05/1.24      (((k5_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_B) @ sk_A)
% 1.05/1.24         = (k5_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B)))),
% 1.05/1.24      inference('sup+', [status(thm)], ['59', '64'])).
% 1.05/1.24  thf('66', plain,
% 1.05/1.24      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 1.05/1.24      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.05/1.24  thf('67', plain,
% 1.05/1.24      (![X17 : $i, X18 : $i]:
% 1.05/1.24         ((k3_tarski @ (k2_tarski @ X17 @ X18))
% 1.05/1.24           = (k5_xboole_0 @ X17 @ (k4_xboole_0 @ X18 @ X17)))),
% 1.05/1.24      inference('demod', [status(thm)], ['25', '26', '27', '30'])).
% 1.05/1.24  thf('68', plain,
% 1.05/1.24      (((k5_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_B))
% 1.05/1.24         = (k3_tarski @ (k2_tarski @ sk_B @ sk_A)))),
% 1.05/1.24      inference('demod', [status(thm)], ['65', '66', '67'])).
% 1.05/1.24  thf('69', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 1.05/1.24      inference('sup-', [status(thm)], ['53', '54'])).
% 1.05/1.24  thf('70', plain,
% 1.05/1.24      (![X5 : $i, X6 : $i]:
% 1.05/1.24         ((k4_xboole_0 @ X5 @ X6)
% 1.05/1.24           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 1.05/1.24      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.05/1.24  thf('71', plain,
% 1.05/1.24      (((k4_xboole_0 @ sk_B @ sk_A) = (k5_xboole_0 @ sk_B @ sk_B))),
% 1.05/1.24      inference('sup+', [status(thm)], ['69', '70'])).
% 1.05/1.24  thf('72', plain,
% 1.05/1.24      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 1.05/1.24      inference('sup+', [status(thm)], ['60', '61'])).
% 1.05/1.24  thf('73', plain,
% 1.05/1.24      (((k4_xboole_0 @ sk_B @ sk_A) = (k4_xboole_0 @ sk_B @ sk_B))),
% 1.05/1.24      inference('demod', [status(thm)], ['71', '72'])).
% 1.05/1.24  thf('74', plain,
% 1.05/1.24      (![X17 : $i, X18 : $i]:
% 1.05/1.24         ((k3_tarski @ (k2_tarski @ X17 @ X18))
% 1.05/1.24           = (k5_xboole_0 @ X17 @ (k4_xboole_0 @ X18 @ X17)))),
% 1.05/1.24      inference('demod', [status(thm)], ['25', '26', '27', '30'])).
% 1.05/1.24  thf('75', plain,
% 1.05/1.24      (((k3_tarski @ (k2_tarski @ sk_A @ sk_B))
% 1.05/1.24         = (k5_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_B)))),
% 1.05/1.24      inference('sup+', [status(thm)], ['73', '74'])).
% 1.05/1.24  thf('76', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 1.05/1.24      inference('sup-', [status(thm)], ['53', '54'])).
% 1.05/1.24  thf('77', plain,
% 1.05/1.24      (![X0 : $i, X1 : $i]:
% 1.05/1.24         ((k3_tarski @ (k2_tarski @ X0 @ (k3_xboole_0 @ X1 @ X0))) = (X0))),
% 1.05/1.24      inference('sup+', [status(thm)], ['33', '36'])).
% 1.05/1.24  thf('78', plain, (((k3_tarski @ (k2_tarski @ sk_A @ sk_B)) = (sk_A))),
% 1.05/1.24      inference('sup+', [status(thm)], ['76', '77'])).
% 1.05/1.24  thf('79', plain,
% 1.05/1.24      (((sk_A) = (k5_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_B)))),
% 1.05/1.24      inference('demod', [status(thm)], ['75', '78'])).
% 1.05/1.24  thf('80', plain, (((sk_A) = (k3_tarski @ (k2_tarski @ sk_B @ sk_A)))),
% 1.05/1.24      inference('sup+', [status(thm)], ['68', '79'])).
% 1.05/1.24  thf('81', plain, (((sk_A) != (sk_A))),
% 1.05/1.24      inference('demod', [status(thm)], ['18', '45', '80'])).
% 1.05/1.24  thf('82', plain, ($false), inference('simplify', [status(thm)], ['81'])).
% 1.05/1.24  
% 1.05/1.24  % SZS output end Refutation
% 1.05/1.24  
% 1.05/1.24  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
