%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Js8lqSQ3Ly

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:51 EST 2020

% Result     : Theorem 0.58s
% Output     : Refutation 0.58s
% Verified   : 
% Statistics : Number of formulae       :  198 (1267 expanded)
%              Number of leaves         :   37 ( 420 expanded)
%              Depth                    :   24
%              Number of atoms          : 1418 (9154 expanded)
%              Number of equality atoms :  128 ( 727 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X62: $i,X63: $i] :
      ( ( ( k3_subset_1 @ X62 @ X63 )
        = ( k4_xboole_0 @ X62 @ X63 ) )
      | ~ ( m1_subset_1 @ X63 @ ( k1_zfmisc_1 @ X62 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('2',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t94_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('3',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ X22 @ X23 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X22 @ X23 ) @ ( k3_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t94_xboole_1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X56: $i,X57: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X56 @ X57 ) )
      = ( k2_xboole_0 @ X56 @ X57 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('5',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X19 @ X20 ) @ X21 )
      = ( k5_xboole_0 @ X19 @ ( k5_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('7',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X22 @ X23 ) )
      = ( k5_xboole_0 @ X22 @ ( k4_xboole_0 @ X23 @ X22 ) ) ) ),
    inference(demod,[status(thm)],['3','4','5','8'])).

thf('10',plain,
    ( ( k3_tarski @ ( k2_tarski @ sk_B @ sk_A ) )
    = ( k5_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['2','9'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('11',plain,(
    ! [X17: $i] :
      ( r1_tarski @ k1_xboole_0 @ X17 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('12',plain,(
    ! [X51: $i,X52: $i,X53: $i] :
      ( ~ ( r1_tarski @ X51 @ X52 )
      | ( r2_hidden @ X51 @ X53 )
      | ( X53
       != ( k1_zfmisc_1 @ X52 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('13',plain,(
    ! [X51: $i,X52: $i] :
      ( ( r2_hidden @ X51 @ ( k1_zfmisc_1 @ X52 ) )
      | ~ ( r1_tarski @ X51 @ X52 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( r2_hidden @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('15',plain,(
    ! [X58: $i,X59: $i] :
      ( ~ ( r2_hidden @ X58 @ X59 )
      | ( m1_subset_1 @ X58 @ X59 )
      | ( v1_xboole_0 @ X59 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('17',plain,(
    ! [X66: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X66 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['16','17'])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('19',plain,(
    ! [X64: $i,X65: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X64 @ X65 ) @ ( k1_zfmisc_1 @ X64 ) )
      | ~ ( m1_subset_1 @ X65 @ ( k1_zfmisc_1 @ X64 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('22',plain,(
    ! [X62: $i,X63: $i] :
      ( ( ( k3_subset_1 @ X62 @ X63 )
        = ( k4_xboole_0 @ X62 @ X63 ) )
      | ~ ( m1_subset_1 @ X63 @ ( k1_zfmisc_1 @ X62 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X17: $i] :
      ( r1_tarski @ k1_xboole_0 @ X17 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('25',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k3_xboole_0 @ X15 @ X16 )
        = X15 )
      | ~ ( r1_tarski @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('31',plain,(
    ! [X18: $i] :
      ( ( k5_xboole_0 @ X18 @ k1_xboole_0 )
      = X18 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['23','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['20','33'])).

thf('35',plain,(
    ! [X58: $i,X59: $i] :
      ( ~ ( m1_subset_1 @ X58 @ X59 )
      | ( r2_hidden @ X58 @ X59 )
      | ( v1_xboole_0 @ X59 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X66: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X66 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X52: $i,X53: $i,X54: $i] :
      ( ~ ( r2_hidden @ X54 @ X53 )
      | ( r1_tarski @ X54 @ X52 )
      | ( X53
       != ( k1_zfmisc_1 @ X52 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('40',plain,(
    ! [X52: $i,X54: $i] :
      ( ( r1_tarski @ X54 @ X52 )
      | ~ ( r2_hidden @ X54 @ ( k1_zfmisc_1 @ X52 ) ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup-',[status(thm)],['38','40'])).

thf('42',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k3_xboole_0 @ X15 @ X16 )
        = X15 )
      | ~ ( r1_tarski @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['20','33'])).

thf('47',plain,(
    ! [X62: $i,X63: $i] :
      ( ( ( k3_subset_1 @ X62 @ X63 )
        = ( k4_xboole_0 @ X62 @ X63 ) )
      | ~ ( m1_subset_1 @ X63 @ ( k1_zfmisc_1 @ X62 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['45','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['45','48'])).

thf('51',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X58: $i,X59: $i] :
      ( ~ ( m1_subset_1 @ X58 @ X59 )
      | ( r2_hidden @ X58 @ X59 )
      | ( v1_xboole_0 @ X59 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('53',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X66: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X66 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('55',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X52: $i,X54: $i] :
      ( ( r1_tarski @ X54 @ X52 )
      | ~ ( r2_hidden @ X54 @ ( k1_zfmisc_1 @ X52 ) ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('57',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k3_xboole_0 @ X15 @ X16 )
        = X15 )
      | ~ ( r1_tarski @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('59',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('61',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('63',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('64',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('65',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X19 @ X20 ) @ X21 )
      = ( k5_xboole_0 @ X19 @ ( k5_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ X0 )
      = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( k5_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_A )
    = ( k5_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_A ) ) ),
    inference('sup+',[status(thm)],['50','66'])).

thf('68',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('69',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ( X9
        = ( k4_xboole_0 @ X5 @ X6 ) )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X5 )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('70',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('71',plain,(
    ! [X18: $i] :
      ( ( k5_xboole_0 @ X18 @ k1_xboole_0 )
      = X18 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ~ ( r2_hidden @ X8 @ X6 )
      | ( X7
       != ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('78',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['76','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( X1
        = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['69','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('85',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ( r2_hidden @ X8 @ X5 )
      | ( X7
       != ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('86',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ( r2_hidden @ X8 @ X5 )
      | ~ ( r2_hidden @ X8 @ ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['85'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k3_subset_1 @ X0 @ X0 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['84','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('89',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['77'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k3_subset_1 @ X0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k3_subset_1 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['87','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['83','91'])).

thf('93',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('95',plain,
    ( ( k5_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['67','68','92','93','94'])).

thf('96',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X19 @ X20 ) @ X21 )
      = ( k5_xboole_0 @ X19 @ ( k5_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ sk_B @ X0 )
      = ( k5_xboole_0 @ sk_A @ ( k5_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['95','96'])).

thf('98',plain,
    ( ( k5_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k5_xboole_0 @ sk_A @ ( k3_subset_1 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['49','97'])).

thf('99',plain,
    ( ( k3_tarski @ ( k2_tarski @ sk_B @ sk_A ) )
    = ( k5_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['2','9'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['83','91'])).

thf('101',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('103',plain,
    ( ( k3_tarski @ ( k2_tarski @ sk_B @ sk_A ) )
    = sk_A ),
    inference(demod,[status(thm)],['98','99','100','101','102'])).

thf('104',plain,
    ( sk_A
    = ( k5_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['10','103'])).

thf('105',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    ! [X64: $i,X65: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X64 @ X65 ) @ ( k1_zfmisc_1 @ X64 ) )
      | ~ ( m1_subset_1 @ X65 @ ( k1_zfmisc_1 @ X64 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('107',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X58: $i,X59: $i] :
      ( ~ ( m1_subset_1 @ X58 @ X59 )
      | ( r2_hidden @ X58 @ X59 )
      | ( v1_xboole_0 @ X59 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('109',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X66: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X66 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('111',plain,(
    r2_hidden @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X52: $i,X54: $i] :
      ( ( r1_tarski @ X54 @ X52 )
      | ~ ( r2_hidden @ X54 @ ( k1_zfmisc_1 @ X52 ) ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('113',plain,(
    r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_A ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k3_xboole_0 @ X15 @ X16 )
        = X15 )
      | ~ ( r1_tarski @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('115',plain,
    ( ( k3_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_A )
    = ( k3_subset_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('117',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k3_subset_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['115','116'])).

thf('118',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf(t112_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ B ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ A @ C ) @ B ) ) )).

thf('119',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X12 @ X14 ) @ ( k3_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X12 @ X13 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[t112_xboole_1])).

thf('120',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['118','119'])).

thf('121',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('122',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('123',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['120','121','122'])).

thf('124',plain,
    ( ( k4_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k3_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['117','123'])).

thf('125',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('126',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['83','91'])).

thf('127',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('128',plain,(
    ! [X62: $i,X63: $i] :
      ( ( ( k3_subset_1 @ X62 @ X63 )
        = ( k4_xboole_0 @ X62 @ X63 ) )
      | ~ ( m1_subset_1 @ X63 @ ( k1_zfmisc_1 @ X62 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('129',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,
    ( ( k5_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['67','68','92','93','94'])).

thf('131',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k3_subset_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['115','116'])).

thf('132',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('133',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k5_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['131','132'])).

thf('134',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('135',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k5_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['133','134'])).

thf('136',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference('sup+',[status(thm)],['130','135'])).

thf('137',plain,
    ( sk_B
    = ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['129','136'])).

thf('138',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('139',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['124','125','126','137','138'])).

thf('140',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('141',plain,
    ( ( k4_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
    = ( k5_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['139','140'])).

thf('142',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('143',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('144',plain,
    ( ( k4_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
    = ( k3_subset_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['141','142','143'])).

thf('145',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X22 @ X23 ) )
      = ( k5_xboole_0 @ X22 @ ( k4_xboole_0 @ X23 @ X22 ) ) ) ),
    inference(demod,[status(thm)],['3','4','5','8'])).

thf('146',plain,
    ( ( k3_tarski @ ( k2_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) )
    = ( k5_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['144','145'])).

thf('147',plain,
    ( ( k3_tarski @ ( k2_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) )
    = sk_A ),
    inference('sup+',[status(thm)],['104','146'])).

thf('148',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
 != ( k2_subset_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('149',plain,(
    ! [X61: $i] :
      ( ( k2_subset_1 @ X61 )
      = X61 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('150',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
 != sk_A ),
    inference(demod,[status(thm)],['148','149'])).

thf('151',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('152',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('153',plain,(
    ! [X67: $i,X68: $i,X69: $i] :
      ( ~ ( m1_subset_1 @ X67 @ ( k1_zfmisc_1 @ X68 ) )
      | ~ ( m1_subset_1 @ X69 @ ( k1_zfmisc_1 @ X68 ) )
      | ( ( k4_subset_1 @ X68 @ X67 @ X69 )
        = ( k2_xboole_0 @ X67 @ X69 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('154',plain,(
    ! [X56: $i,X57: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X56 @ X57 ) )
      = ( k2_xboole_0 @ X56 @ X57 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('155',plain,(
    ! [X67: $i,X68: $i,X69: $i] :
      ( ~ ( m1_subset_1 @ X67 @ ( k1_zfmisc_1 @ X68 ) )
      | ~ ( m1_subset_1 @ X69 @ ( k1_zfmisc_1 @ X68 ) )
      | ( ( k4_subset_1 @ X68 @ X67 @ X69 )
        = ( k3_tarski @ ( k2_tarski @ X67 @ X69 ) ) ) ) ),
    inference(demod,[status(thm)],['153','154'])).

thf('156',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ sk_A @ sk_B @ X0 )
        = ( k3_tarski @ ( k2_tarski @ sk_B @ X0 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['152','155'])).

thf('157',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k3_tarski @ ( k2_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['151','156'])).

thf('158',plain,(
    ( k3_tarski @ ( k2_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) )
 != sk_A ),
    inference(demod,[status(thm)],['150','157'])).

thf('159',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['147','158'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Js8lqSQ3Ly
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:26:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.58/0.75  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.58/0.75  % Solved by: fo/fo7.sh
% 0.58/0.75  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.58/0.75  % done 785 iterations in 0.301s
% 0.58/0.75  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.58/0.75  % SZS output start Refutation
% 0.58/0.75  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.58/0.75  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.58/0.75  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.58/0.75  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.58/0.75  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.58/0.75  thf(sk_A_type, type, sk_A: $i).
% 0.58/0.75  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.58/0.75  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.58/0.75  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.58/0.75  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.58/0.75  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.58/0.75  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.58/0.75  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.58/0.75  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.58/0.75  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.58/0.75  thf(sk_B_type, type, sk_B: $i).
% 0.58/0.75  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.58/0.75  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.58/0.75  thf(t25_subset_1, conjecture,
% 0.58/0.75    (![A:$i,B:$i]:
% 0.58/0.75     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.58/0.75       ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) ) =
% 0.58/0.75         ( k2_subset_1 @ A ) ) ))).
% 0.58/0.75  thf(zf_stmt_0, negated_conjecture,
% 0.58/0.75    (~( ![A:$i,B:$i]:
% 0.58/0.75        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.58/0.75          ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) ) =
% 0.58/0.75            ( k2_subset_1 @ A ) ) ) )),
% 0.58/0.75    inference('cnf.neg', [status(esa)], [t25_subset_1])).
% 0.58/0.75  thf('0', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.58/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.75  thf(d5_subset_1, axiom,
% 0.58/0.75    (![A:$i,B:$i]:
% 0.58/0.75     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.58/0.75       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.58/0.75  thf('1', plain,
% 0.58/0.75      (![X62 : $i, X63 : $i]:
% 0.58/0.75         (((k3_subset_1 @ X62 @ X63) = (k4_xboole_0 @ X62 @ X63))
% 0.58/0.75          | ~ (m1_subset_1 @ X63 @ (k1_zfmisc_1 @ X62)))),
% 0.58/0.75      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.58/0.75  thf('2', plain,
% 0.58/0.75      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.58/0.75      inference('sup-', [status(thm)], ['0', '1'])).
% 0.58/0.75  thf(t94_xboole_1, axiom,
% 0.58/0.75    (![A:$i,B:$i]:
% 0.58/0.75     ( ( k2_xboole_0 @ A @ B ) =
% 0.58/0.75       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.58/0.75  thf('3', plain,
% 0.58/0.75      (![X22 : $i, X23 : $i]:
% 0.58/0.75         ((k2_xboole_0 @ X22 @ X23)
% 0.58/0.75           = (k5_xboole_0 @ (k5_xboole_0 @ X22 @ X23) @ 
% 0.58/0.75              (k3_xboole_0 @ X22 @ X23)))),
% 0.58/0.75      inference('cnf', [status(esa)], [t94_xboole_1])).
% 0.58/0.75  thf(l51_zfmisc_1, axiom,
% 0.58/0.75    (![A:$i,B:$i]:
% 0.58/0.75     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.58/0.75  thf('4', plain,
% 0.58/0.75      (![X56 : $i, X57 : $i]:
% 0.58/0.75         ((k3_tarski @ (k2_tarski @ X56 @ X57)) = (k2_xboole_0 @ X56 @ X57))),
% 0.58/0.75      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.58/0.75  thf(t91_xboole_1, axiom,
% 0.58/0.75    (![A:$i,B:$i,C:$i]:
% 0.58/0.75     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.58/0.75       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.58/0.76  thf('5', plain,
% 0.58/0.76      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.58/0.76         ((k5_xboole_0 @ (k5_xboole_0 @ X19 @ X20) @ X21)
% 0.58/0.76           = (k5_xboole_0 @ X19 @ (k5_xboole_0 @ X20 @ X21)))),
% 0.58/0.76      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.58/0.76  thf(commutativity_k3_xboole_0, axiom,
% 0.58/0.76    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.58/0.76  thf('6', plain,
% 0.58/0.76      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.58/0.76      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.58/0.76  thf(t100_xboole_1, axiom,
% 0.58/0.76    (![A:$i,B:$i]:
% 0.58/0.76     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.58/0.76  thf('7', plain,
% 0.58/0.76      (![X10 : $i, X11 : $i]:
% 0.58/0.76         ((k4_xboole_0 @ X10 @ X11)
% 0.58/0.76           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 0.58/0.76      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.58/0.76  thf('8', plain,
% 0.58/0.76      (![X0 : $i, X1 : $i]:
% 0.58/0.76         ((k4_xboole_0 @ X0 @ X1)
% 0.58/0.76           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.58/0.76      inference('sup+', [status(thm)], ['6', '7'])).
% 0.58/0.76  thf('9', plain,
% 0.58/0.76      (![X22 : $i, X23 : $i]:
% 0.58/0.76         ((k3_tarski @ (k2_tarski @ X22 @ X23))
% 0.58/0.76           = (k5_xboole_0 @ X22 @ (k4_xboole_0 @ X23 @ X22)))),
% 0.58/0.76      inference('demod', [status(thm)], ['3', '4', '5', '8'])).
% 0.58/0.76  thf('10', plain,
% 0.58/0.76      (((k3_tarski @ (k2_tarski @ sk_B @ sk_A))
% 0.58/0.76         = (k5_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.58/0.76      inference('sup+', [status(thm)], ['2', '9'])).
% 0.58/0.76  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.58/0.76  thf('11', plain, (![X17 : $i]: (r1_tarski @ k1_xboole_0 @ X17)),
% 0.58/0.76      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.58/0.76  thf(d1_zfmisc_1, axiom,
% 0.58/0.76    (![A:$i,B:$i]:
% 0.58/0.76     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.58/0.76       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.58/0.76  thf('12', plain,
% 0.58/0.76      (![X51 : $i, X52 : $i, X53 : $i]:
% 0.58/0.76         (~ (r1_tarski @ X51 @ X52)
% 0.58/0.76          | (r2_hidden @ X51 @ X53)
% 0.58/0.76          | ((X53) != (k1_zfmisc_1 @ X52)))),
% 0.58/0.76      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.58/0.76  thf('13', plain,
% 0.58/0.76      (![X51 : $i, X52 : $i]:
% 0.58/0.76         ((r2_hidden @ X51 @ (k1_zfmisc_1 @ X52)) | ~ (r1_tarski @ X51 @ X52))),
% 0.58/0.76      inference('simplify', [status(thm)], ['12'])).
% 0.58/0.76  thf('14', plain,
% 0.58/0.76      (![X0 : $i]: (r2_hidden @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.58/0.76      inference('sup-', [status(thm)], ['11', '13'])).
% 0.58/0.76  thf(d2_subset_1, axiom,
% 0.58/0.76    (![A:$i,B:$i]:
% 0.58/0.76     ( ( ( v1_xboole_0 @ A ) =>
% 0.58/0.76         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.58/0.76       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.58/0.76         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.58/0.76  thf('15', plain,
% 0.58/0.76      (![X58 : $i, X59 : $i]:
% 0.58/0.76         (~ (r2_hidden @ X58 @ X59)
% 0.58/0.76          | (m1_subset_1 @ X58 @ X59)
% 0.58/0.76          | (v1_xboole_0 @ X59))),
% 0.58/0.76      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.58/0.76  thf('16', plain,
% 0.58/0.76      (![X0 : $i]:
% 0.58/0.76         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 0.58/0.76          | (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0)))),
% 0.58/0.76      inference('sup-', [status(thm)], ['14', '15'])).
% 0.58/0.76  thf(fc1_subset_1, axiom,
% 0.58/0.76    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.58/0.76  thf('17', plain, (![X66 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X66))),
% 0.58/0.76      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.58/0.76  thf('18', plain,
% 0.58/0.76      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.58/0.76      inference('clc', [status(thm)], ['16', '17'])).
% 0.58/0.76  thf(dt_k3_subset_1, axiom,
% 0.58/0.76    (![A:$i,B:$i]:
% 0.58/0.76     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.58/0.76       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.58/0.76  thf('19', plain,
% 0.58/0.76      (![X64 : $i, X65 : $i]:
% 0.58/0.76         ((m1_subset_1 @ (k3_subset_1 @ X64 @ X65) @ (k1_zfmisc_1 @ X64))
% 0.58/0.76          | ~ (m1_subset_1 @ X65 @ (k1_zfmisc_1 @ X64)))),
% 0.58/0.76      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.58/0.76  thf('20', plain,
% 0.58/0.76      (![X0 : $i]:
% 0.58/0.76         (m1_subset_1 @ (k3_subset_1 @ X0 @ k1_xboole_0) @ (k1_zfmisc_1 @ X0))),
% 0.58/0.76      inference('sup-', [status(thm)], ['18', '19'])).
% 0.58/0.76  thf('21', plain,
% 0.58/0.76      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.58/0.76      inference('clc', [status(thm)], ['16', '17'])).
% 0.58/0.76  thf('22', plain,
% 0.58/0.76      (![X62 : $i, X63 : $i]:
% 0.58/0.76         (((k3_subset_1 @ X62 @ X63) = (k4_xboole_0 @ X62 @ X63))
% 0.58/0.76          | ~ (m1_subset_1 @ X63 @ (k1_zfmisc_1 @ X62)))),
% 0.58/0.76      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.58/0.76  thf('23', plain,
% 0.58/0.76      (![X0 : $i]:
% 0.58/0.76         ((k3_subset_1 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.58/0.76      inference('sup-', [status(thm)], ['21', '22'])).
% 0.58/0.76  thf('24', plain, (![X17 : $i]: (r1_tarski @ k1_xboole_0 @ X17)),
% 0.58/0.76      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.58/0.76  thf(t28_xboole_1, axiom,
% 0.58/0.76    (![A:$i,B:$i]:
% 0.58/0.76     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.58/0.76  thf('25', plain,
% 0.58/0.76      (![X15 : $i, X16 : $i]:
% 0.58/0.76         (((k3_xboole_0 @ X15 @ X16) = (X15)) | ~ (r1_tarski @ X15 @ X16))),
% 0.58/0.76      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.58/0.76  thf('26', plain,
% 0.58/0.76      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.58/0.76      inference('sup-', [status(thm)], ['24', '25'])).
% 0.58/0.76  thf('27', plain,
% 0.58/0.76      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.58/0.76      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.58/0.76  thf('28', plain,
% 0.58/0.76      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.58/0.76      inference('sup+', [status(thm)], ['26', '27'])).
% 0.58/0.76  thf('29', plain,
% 0.58/0.76      (![X10 : $i, X11 : $i]:
% 0.58/0.76         ((k4_xboole_0 @ X10 @ X11)
% 0.58/0.76           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 0.58/0.76      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.58/0.76  thf('30', plain,
% 0.58/0.76      (![X0 : $i]:
% 0.58/0.76         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.58/0.76      inference('sup+', [status(thm)], ['28', '29'])).
% 0.58/0.76  thf(t5_boole, axiom,
% 0.58/0.76    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.58/0.76  thf('31', plain, (![X18 : $i]: ((k5_xboole_0 @ X18 @ k1_xboole_0) = (X18))),
% 0.58/0.76      inference('cnf', [status(esa)], [t5_boole])).
% 0.58/0.76  thf('32', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.58/0.76      inference('sup+', [status(thm)], ['30', '31'])).
% 0.58/0.76  thf('33', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 0.58/0.76      inference('sup+', [status(thm)], ['23', '32'])).
% 0.58/0.76  thf('34', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.58/0.76      inference('demod', [status(thm)], ['20', '33'])).
% 0.58/0.76  thf('35', plain,
% 0.58/0.76      (![X58 : $i, X59 : $i]:
% 0.58/0.76         (~ (m1_subset_1 @ X58 @ X59)
% 0.58/0.76          | (r2_hidden @ X58 @ X59)
% 0.58/0.76          | (v1_xboole_0 @ X59))),
% 0.58/0.76      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.58/0.76  thf('36', plain,
% 0.58/0.76      (![X0 : $i]:
% 0.58/0.76         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 0.58/0.76          | (r2_hidden @ X0 @ (k1_zfmisc_1 @ X0)))),
% 0.58/0.76      inference('sup-', [status(thm)], ['34', '35'])).
% 0.58/0.76  thf('37', plain, (![X66 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X66))),
% 0.58/0.76      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.58/0.76  thf('38', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.58/0.76      inference('clc', [status(thm)], ['36', '37'])).
% 0.58/0.76  thf('39', plain,
% 0.58/0.76      (![X52 : $i, X53 : $i, X54 : $i]:
% 0.58/0.76         (~ (r2_hidden @ X54 @ X53)
% 0.58/0.76          | (r1_tarski @ X54 @ X52)
% 0.58/0.76          | ((X53) != (k1_zfmisc_1 @ X52)))),
% 0.58/0.76      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.58/0.76  thf('40', plain,
% 0.58/0.76      (![X52 : $i, X54 : $i]:
% 0.58/0.76         ((r1_tarski @ X54 @ X52) | ~ (r2_hidden @ X54 @ (k1_zfmisc_1 @ X52)))),
% 0.58/0.76      inference('simplify', [status(thm)], ['39'])).
% 0.58/0.76  thf('41', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.58/0.76      inference('sup-', [status(thm)], ['38', '40'])).
% 0.58/0.76  thf('42', plain,
% 0.58/0.76      (![X15 : $i, X16 : $i]:
% 0.58/0.76         (((k3_xboole_0 @ X15 @ X16) = (X15)) | ~ (r1_tarski @ X15 @ X16))),
% 0.58/0.76      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.58/0.76  thf('43', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.58/0.76      inference('sup-', [status(thm)], ['41', '42'])).
% 0.58/0.76  thf('44', plain,
% 0.58/0.76      (![X0 : $i, X1 : $i]:
% 0.58/0.76         ((k4_xboole_0 @ X0 @ X1)
% 0.58/0.76           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.58/0.76      inference('sup+', [status(thm)], ['6', '7'])).
% 0.58/0.76  thf('45', plain,
% 0.58/0.76      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.58/0.76      inference('sup+', [status(thm)], ['43', '44'])).
% 0.58/0.76  thf('46', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.58/0.76      inference('demod', [status(thm)], ['20', '33'])).
% 0.58/0.76  thf('47', plain,
% 0.58/0.76      (![X62 : $i, X63 : $i]:
% 0.58/0.76         (((k3_subset_1 @ X62 @ X63) = (k4_xboole_0 @ X62 @ X63))
% 0.58/0.76          | ~ (m1_subset_1 @ X63 @ (k1_zfmisc_1 @ X62)))),
% 0.58/0.76      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.58/0.76  thf('48', plain,
% 0.58/0.76      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 0.58/0.76      inference('sup-', [status(thm)], ['46', '47'])).
% 0.58/0.76  thf('49', plain,
% 0.58/0.76      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.58/0.76      inference('demod', [status(thm)], ['45', '48'])).
% 0.58/0.76  thf('50', plain,
% 0.58/0.76      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.58/0.76      inference('demod', [status(thm)], ['45', '48'])).
% 0.58/0.76  thf('51', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.58/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.76  thf('52', plain,
% 0.58/0.76      (![X58 : $i, X59 : $i]:
% 0.58/0.76         (~ (m1_subset_1 @ X58 @ X59)
% 0.58/0.76          | (r2_hidden @ X58 @ X59)
% 0.58/0.76          | (v1_xboole_0 @ X59))),
% 0.58/0.76      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.58/0.76  thf('53', plain,
% 0.58/0.76      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.58/0.76        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 0.58/0.76      inference('sup-', [status(thm)], ['51', '52'])).
% 0.58/0.76  thf('54', plain, (![X66 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X66))),
% 0.58/0.76      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.58/0.76  thf('55', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.58/0.76      inference('clc', [status(thm)], ['53', '54'])).
% 0.58/0.76  thf('56', plain,
% 0.58/0.76      (![X52 : $i, X54 : $i]:
% 0.58/0.76         ((r1_tarski @ X54 @ X52) | ~ (r2_hidden @ X54 @ (k1_zfmisc_1 @ X52)))),
% 0.58/0.76      inference('simplify', [status(thm)], ['39'])).
% 0.58/0.76  thf('57', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.58/0.76      inference('sup-', [status(thm)], ['55', '56'])).
% 0.58/0.76  thf('58', plain,
% 0.58/0.76      (![X15 : $i, X16 : $i]:
% 0.58/0.76         (((k3_xboole_0 @ X15 @ X16) = (X15)) | ~ (r1_tarski @ X15 @ X16))),
% 0.58/0.76      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.58/0.76  thf('59', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 0.58/0.76      inference('sup-', [status(thm)], ['57', '58'])).
% 0.58/0.76  thf('60', plain,
% 0.58/0.76      (![X0 : $i, X1 : $i]:
% 0.58/0.76         ((k4_xboole_0 @ X0 @ X1)
% 0.58/0.76           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.58/0.76      inference('sup+', [status(thm)], ['6', '7'])).
% 0.58/0.76  thf('61', plain,
% 0.58/0.76      (((k4_xboole_0 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 0.58/0.76      inference('sup+', [status(thm)], ['59', '60'])).
% 0.58/0.76  thf('62', plain,
% 0.58/0.76      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.58/0.76      inference('sup-', [status(thm)], ['0', '1'])).
% 0.58/0.76  thf(commutativity_k5_xboole_0, axiom,
% 0.58/0.76    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.58/0.76  thf('63', plain,
% 0.58/0.76      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.58/0.76      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.58/0.76  thf('64', plain,
% 0.58/0.76      (((k3_subset_1 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_B @ sk_A))),
% 0.58/0.76      inference('demod', [status(thm)], ['61', '62', '63'])).
% 0.58/0.76  thf('65', plain,
% 0.58/0.76      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.58/0.76         ((k5_xboole_0 @ (k5_xboole_0 @ X19 @ X20) @ X21)
% 0.58/0.76           = (k5_xboole_0 @ X19 @ (k5_xboole_0 @ X20 @ X21)))),
% 0.58/0.76      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.58/0.76  thf('66', plain,
% 0.58/0.76      (![X0 : $i]:
% 0.58/0.76         ((k5_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ X0)
% 0.58/0.76           = (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_A @ X0)))),
% 0.58/0.76      inference('sup+', [status(thm)], ['64', '65'])).
% 0.58/0.76  thf('67', plain,
% 0.58/0.76      (((k5_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ sk_A)
% 0.58/0.76         = (k5_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_A)))),
% 0.58/0.76      inference('sup+', [status(thm)], ['50', '66'])).
% 0.58/0.76  thf('68', plain,
% 0.58/0.76      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.58/0.76      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.58/0.76  thf(d5_xboole_0, axiom,
% 0.58/0.76    (![A:$i,B:$i,C:$i]:
% 0.58/0.76     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.58/0.76       ( ![D:$i]:
% 0.58/0.76         ( ( r2_hidden @ D @ C ) <=>
% 0.58/0.76           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.58/0.76  thf('69', plain,
% 0.58/0.76      (![X5 : $i, X6 : $i, X9 : $i]:
% 0.58/0.76         (((X9) = (k4_xboole_0 @ X5 @ X6))
% 0.58/0.76          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X5)
% 0.58/0.76          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X9))),
% 0.58/0.76      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.58/0.76  thf('70', plain,
% 0.58/0.76      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.58/0.76      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.58/0.76  thf('71', plain, (![X18 : $i]: ((k5_xboole_0 @ X18 @ k1_xboole_0) = (X18))),
% 0.58/0.76      inference('cnf', [status(esa)], [t5_boole])).
% 0.58/0.76  thf('72', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.58/0.76      inference('sup+', [status(thm)], ['70', '71'])).
% 0.58/0.76  thf('73', plain,
% 0.58/0.76      (![X10 : $i, X11 : $i]:
% 0.58/0.76         ((k4_xboole_0 @ X10 @ X11)
% 0.58/0.76           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 0.58/0.76      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.58/0.76  thf('74', plain,
% 0.58/0.76      (![X0 : $i]:
% 0.58/0.76         ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 0.58/0.76      inference('sup+', [status(thm)], ['72', '73'])).
% 0.58/0.76  thf('75', plain,
% 0.58/0.76      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.58/0.76      inference('sup-', [status(thm)], ['24', '25'])).
% 0.58/0.76  thf('76', plain,
% 0.58/0.76      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.58/0.76      inference('demod', [status(thm)], ['74', '75'])).
% 0.58/0.76  thf('77', plain,
% 0.58/0.76      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.58/0.76         (~ (r2_hidden @ X8 @ X7)
% 0.58/0.76          | ~ (r2_hidden @ X8 @ X6)
% 0.58/0.76          | ((X7) != (k4_xboole_0 @ X5 @ X6)))),
% 0.58/0.76      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.58/0.76  thf('78', plain,
% 0.58/0.76      (![X5 : $i, X6 : $i, X8 : $i]:
% 0.58/0.76         (~ (r2_hidden @ X8 @ X6)
% 0.58/0.76          | ~ (r2_hidden @ X8 @ (k4_xboole_0 @ X5 @ X6)))),
% 0.58/0.76      inference('simplify', [status(thm)], ['77'])).
% 0.58/0.76  thf('79', plain,
% 0.58/0.76      (![X0 : $i, X1 : $i]:
% 0.58/0.76         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r2_hidden @ X1 @ X0))),
% 0.58/0.76      inference('sup-', [status(thm)], ['76', '78'])).
% 0.58/0.76  thf('80', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.58/0.76      inference('condensation', [status(thm)], ['79'])).
% 0.58/0.76  thf('81', plain,
% 0.58/0.76      (![X0 : $i, X1 : $i]:
% 0.58/0.76         ((r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1)
% 0.58/0.76          | ((X1) = (k4_xboole_0 @ k1_xboole_0 @ X0)))),
% 0.58/0.76      inference('sup-', [status(thm)], ['69', '80'])).
% 0.58/0.76  thf('82', plain,
% 0.58/0.76      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.58/0.76      inference('demod', [status(thm)], ['74', '75'])).
% 0.58/0.76  thf('83', plain,
% 0.58/0.76      (![X0 : $i, X1 : $i]:
% 0.58/0.76         ((r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1)
% 0.58/0.76          | ((X1) = (k1_xboole_0)))),
% 0.58/0.76      inference('demod', [status(thm)], ['81', '82'])).
% 0.58/0.76  thf('84', plain,
% 0.58/0.76      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 0.58/0.76      inference('sup-', [status(thm)], ['46', '47'])).
% 0.58/0.76  thf('85', plain,
% 0.58/0.76      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.58/0.76         (~ (r2_hidden @ X8 @ X7)
% 0.58/0.76          | (r2_hidden @ X8 @ X5)
% 0.58/0.76          | ((X7) != (k4_xboole_0 @ X5 @ X6)))),
% 0.58/0.76      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.58/0.76  thf('86', plain,
% 0.58/0.76      (![X5 : $i, X6 : $i, X8 : $i]:
% 0.58/0.76         ((r2_hidden @ X8 @ X5) | ~ (r2_hidden @ X8 @ (k4_xboole_0 @ X5 @ X6)))),
% 0.58/0.76      inference('simplify', [status(thm)], ['85'])).
% 0.58/0.76  thf('87', plain,
% 0.58/0.76      (![X0 : $i, X1 : $i]:
% 0.58/0.76         (~ (r2_hidden @ X1 @ (k3_subset_1 @ X0 @ X0)) | (r2_hidden @ X1 @ X0))),
% 0.58/0.76      inference('sup-', [status(thm)], ['84', '86'])).
% 0.58/0.76  thf('88', plain,
% 0.58/0.76      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 0.58/0.76      inference('sup-', [status(thm)], ['46', '47'])).
% 0.58/0.76  thf('89', plain,
% 0.58/0.76      (![X5 : $i, X6 : $i, X8 : $i]:
% 0.58/0.76         (~ (r2_hidden @ X8 @ X6)
% 0.58/0.76          | ~ (r2_hidden @ X8 @ (k4_xboole_0 @ X5 @ X6)))),
% 0.58/0.76      inference('simplify', [status(thm)], ['77'])).
% 0.58/0.76  thf('90', plain,
% 0.58/0.76      (![X0 : $i, X1 : $i]:
% 0.58/0.76         (~ (r2_hidden @ X1 @ (k3_subset_1 @ X0 @ X0))
% 0.58/0.76          | ~ (r2_hidden @ X1 @ X0))),
% 0.58/0.76      inference('sup-', [status(thm)], ['88', '89'])).
% 0.58/0.76  thf('91', plain,
% 0.58/0.76      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k3_subset_1 @ X0 @ X0))),
% 0.58/0.76      inference('clc', [status(thm)], ['87', '90'])).
% 0.58/0.76  thf('92', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.58/0.76      inference('sup-', [status(thm)], ['83', '91'])).
% 0.58/0.76  thf('93', plain,
% 0.58/0.76      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.58/0.76      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.58/0.76  thf('94', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.58/0.76      inference('sup+', [status(thm)], ['70', '71'])).
% 0.58/0.76  thf('95', plain,
% 0.58/0.76      (((k5_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)) = (sk_B))),
% 0.58/0.76      inference('demod', [status(thm)], ['67', '68', '92', '93', '94'])).
% 0.58/0.76  thf('96', plain,
% 0.58/0.76      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.58/0.76         ((k5_xboole_0 @ (k5_xboole_0 @ X19 @ X20) @ X21)
% 0.58/0.76           = (k5_xboole_0 @ X19 @ (k5_xboole_0 @ X20 @ X21)))),
% 0.58/0.76      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.58/0.76  thf('97', plain,
% 0.58/0.76      (![X0 : $i]:
% 0.58/0.76         ((k5_xboole_0 @ sk_B @ X0)
% 0.58/0.76           = (k5_xboole_0 @ sk_A @ 
% 0.58/0.76              (k5_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ X0)))),
% 0.58/0.76      inference('sup+', [status(thm)], ['95', '96'])).
% 0.58/0.76  thf('98', plain,
% 0.58/0.76      (((k5_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 0.58/0.76         = (k5_xboole_0 @ sk_A @ 
% 0.58/0.76            (k3_subset_1 @ (k3_subset_1 @ sk_A @ sk_B) @ 
% 0.58/0.76             (k3_subset_1 @ sk_A @ sk_B))))),
% 0.58/0.76      inference('sup+', [status(thm)], ['49', '97'])).
% 0.58/0.76  thf('99', plain,
% 0.58/0.76      (((k3_tarski @ (k2_tarski @ sk_B @ sk_A))
% 0.58/0.76         = (k5_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.58/0.76      inference('sup+', [status(thm)], ['2', '9'])).
% 0.58/0.76  thf('100', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.58/0.76      inference('sup-', [status(thm)], ['83', '91'])).
% 0.58/0.76  thf('101', plain,
% 0.58/0.76      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.58/0.76      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.58/0.76  thf('102', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.58/0.76      inference('sup+', [status(thm)], ['70', '71'])).
% 0.58/0.76  thf('103', plain, (((k3_tarski @ (k2_tarski @ sk_B @ sk_A)) = (sk_A))),
% 0.58/0.76      inference('demod', [status(thm)], ['98', '99', '100', '101', '102'])).
% 0.58/0.76  thf('104', plain,
% 0.58/0.76      (((sk_A) = (k5_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.58/0.76      inference('demod', [status(thm)], ['10', '103'])).
% 0.58/0.76  thf('105', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.58/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.76  thf('106', plain,
% 0.58/0.76      (![X64 : $i, X65 : $i]:
% 0.58/0.76         ((m1_subset_1 @ (k3_subset_1 @ X64 @ X65) @ (k1_zfmisc_1 @ X64))
% 0.58/0.76          | ~ (m1_subset_1 @ X65 @ (k1_zfmisc_1 @ X64)))),
% 0.58/0.76      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.58/0.76  thf('107', plain,
% 0.58/0.76      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.58/0.76      inference('sup-', [status(thm)], ['105', '106'])).
% 0.58/0.76  thf('108', plain,
% 0.58/0.76      (![X58 : $i, X59 : $i]:
% 0.58/0.76         (~ (m1_subset_1 @ X58 @ X59)
% 0.58/0.76          | (r2_hidden @ X58 @ X59)
% 0.58/0.76          | (v1_xboole_0 @ X59))),
% 0.58/0.76      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.58/0.76  thf('109', plain,
% 0.58/0.76      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.58/0.76        | (r2_hidden @ (k3_subset_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A)))),
% 0.58/0.76      inference('sup-', [status(thm)], ['107', '108'])).
% 0.58/0.76  thf('110', plain, (![X66 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X66))),
% 0.58/0.76      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.58/0.76  thf('111', plain,
% 0.58/0.76      ((r2_hidden @ (k3_subset_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.58/0.76      inference('clc', [status(thm)], ['109', '110'])).
% 0.58/0.76  thf('112', plain,
% 0.58/0.76      (![X52 : $i, X54 : $i]:
% 0.58/0.76         ((r1_tarski @ X54 @ X52) | ~ (r2_hidden @ X54 @ (k1_zfmisc_1 @ X52)))),
% 0.58/0.76      inference('simplify', [status(thm)], ['39'])).
% 0.58/0.76  thf('113', plain, ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_A)),
% 0.58/0.76      inference('sup-', [status(thm)], ['111', '112'])).
% 0.58/0.76  thf('114', plain,
% 0.58/0.76      (![X15 : $i, X16 : $i]:
% 0.58/0.76         (((k3_xboole_0 @ X15 @ X16) = (X15)) | ~ (r1_tarski @ X15 @ X16))),
% 0.58/0.76      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.58/0.76  thf('115', plain,
% 0.58/0.76      (((k3_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ sk_A)
% 0.58/0.76         = (k3_subset_1 @ sk_A @ sk_B))),
% 0.58/0.76      inference('sup-', [status(thm)], ['113', '114'])).
% 0.58/0.76  thf('116', plain,
% 0.58/0.76      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.58/0.76      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.58/0.76  thf('117', plain,
% 0.58/0.76      (((k3_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B))
% 0.58/0.76         = (k3_subset_1 @ sk_A @ sk_B))),
% 0.58/0.76      inference('demod', [status(thm)], ['115', '116'])).
% 0.58/0.76  thf('118', plain,
% 0.58/0.76      (![X10 : $i, X11 : $i]:
% 0.58/0.76         ((k4_xboole_0 @ X10 @ X11)
% 0.58/0.76           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 0.58/0.76      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.58/0.76  thf(t112_xboole_1, axiom,
% 0.58/0.76    (![A:$i,B:$i,C:$i]:
% 0.58/0.76     ( ( k5_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ B ) ) =
% 0.58/0.76       ( k3_xboole_0 @ ( k5_xboole_0 @ A @ C ) @ B ) ))).
% 0.58/0.76  thf('119', plain,
% 0.58/0.76      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.58/0.76         ((k5_xboole_0 @ (k3_xboole_0 @ X12 @ X14) @ (k3_xboole_0 @ X13 @ X14))
% 0.58/0.76           = (k3_xboole_0 @ (k5_xboole_0 @ X12 @ X13) @ X14))),
% 0.58/0.76      inference('cnf', [status(esa)], [t112_xboole_1])).
% 0.58/0.76  thf('120', plain,
% 0.58/0.76      (![X0 : $i, X1 : $i]:
% 0.58/0.76         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0)
% 0.58/0.76           = (k3_xboole_0 @ (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)) @ X0))),
% 0.58/0.76      inference('sup+', [status(thm)], ['118', '119'])).
% 0.58/0.76  thf('121', plain,
% 0.58/0.76      (![X10 : $i, X11 : $i]:
% 0.58/0.76         ((k4_xboole_0 @ X10 @ X11)
% 0.58/0.76           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 0.58/0.76      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.58/0.76  thf('122', plain,
% 0.58/0.76      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.58/0.76      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.58/0.76  thf('123', plain,
% 0.58/0.76      (![X0 : $i, X1 : $i]:
% 0.58/0.76         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0)
% 0.58/0.76           = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.58/0.76      inference('demod', [status(thm)], ['120', '121', '122'])).
% 0.58/0.76  thf('124', plain,
% 0.58/0.76      (((k4_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ 
% 0.58/0.76         (k3_subset_1 @ sk_A @ sk_B))
% 0.58/0.76         = (k3_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ 
% 0.58/0.76            (k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B))))),
% 0.58/0.76      inference('sup+', [status(thm)], ['117', '123'])).
% 0.58/0.76  thf('125', plain,
% 0.58/0.76      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 0.58/0.76      inference('sup-', [status(thm)], ['46', '47'])).
% 0.58/0.76  thf('126', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.58/0.76      inference('sup-', [status(thm)], ['83', '91'])).
% 0.58/0.76  thf('127', plain,
% 0.58/0.76      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.58/0.76      inference('sup-', [status(thm)], ['105', '106'])).
% 0.58/0.76  thf('128', plain,
% 0.58/0.76      (![X62 : $i, X63 : $i]:
% 0.58/0.76         (((k3_subset_1 @ X62 @ X63) = (k4_xboole_0 @ X62 @ X63))
% 0.58/0.76          | ~ (m1_subset_1 @ X63 @ (k1_zfmisc_1 @ X62)))),
% 0.58/0.76      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.58/0.76  thf('129', plain,
% 0.58/0.76      (((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B))
% 0.58/0.76         = (k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.58/0.76      inference('sup-', [status(thm)], ['127', '128'])).
% 0.58/0.76  thf('130', plain,
% 0.58/0.76      (((k5_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)) = (sk_B))),
% 0.58/0.76      inference('demod', [status(thm)], ['67', '68', '92', '93', '94'])).
% 0.58/0.76  thf('131', plain,
% 0.58/0.76      (((k3_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B))
% 0.58/0.76         = (k3_subset_1 @ sk_A @ sk_B))),
% 0.58/0.76      inference('demod', [status(thm)], ['115', '116'])).
% 0.58/0.76  thf('132', plain,
% 0.58/0.76      (![X10 : $i, X11 : $i]:
% 0.58/0.76         ((k4_xboole_0 @ X10 @ X11)
% 0.58/0.76           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 0.58/0.76      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.58/0.76  thf('133', plain,
% 0.58/0.76      (((k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B))
% 0.58/0.76         = (k5_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.58/0.76      inference('sup+', [status(thm)], ['131', '132'])).
% 0.58/0.76  thf('134', plain,
% 0.58/0.76      (((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B))
% 0.58/0.76         = (k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.58/0.76      inference('sup-', [status(thm)], ['127', '128'])).
% 0.58/0.76  thf('135', plain,
% 0.58/0.76      (((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B))
% 0.58/0.76         = (k5_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.58/0.76      inference('demod', [status(thm)], ['133', '134'])).
% 0.58/0.76  thf('136', plain,
% 0.58/0.76      (((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)) = (sk_B))),
% 0.58/0.76      inference('sup+', [status(thm)], ['130', '135'])).
% 0.58/0.76  thf('137', plain,
% 0.58/0.76      (((sk_B) = (k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.58/0.76      inference('demod', [status(thm)], ['129', '136'])).
% 0.58/0.76  thf('138', plain,
% 0.58/0.76      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.58/0.76      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.58/0.76  thf('139', plain,
% 0.58/0.76      (((k1_xboole_0) = (k3_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.58/0.76      inference('demod', [status(thm)], ['124', '125', '126', '137', '138'])).
% 0.58/0.76  thf('140', plain,
% 0.58/0.76      (![X0 : $i, X1 : $i]:
% 0.58/0.76         ((k4_xboole_0 @ X0 @ X1)
% 0.58/0.76           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.58/0.76      inference('sup+', [status(thm)], ['6', '7'])).
% 0.58/0.76  thf('141', plain,
% 0.58/0.76      (((k4_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)
% 0.58/0.76         = (k5_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ k1_xboole_0))),
% 0.58/0.76      inference('sup+', [status(thm)], ['139', '140'])).
% 0.58/0.76  thf('142', plain,
% 0.58/0.76      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.58/0.76      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.58/0.76  thf('143', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.58/0.76      inference('sup+', [status(thm)], ['70', '71'])).
% 0.58/0.76  thf('144', plain,
% 0.58/0.76      (((k4_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)
% 0.58/0.76         = (k3_subset_1 @ sk_A @ sk_B))),
% 0.58/0.76      inference('demod', [status(thm)], ['141', '142', '143'])).
% 0.58/0.76  thf('145', plain,
% 0.58/0.76      (![X22 : $i, X23 : $i]:
% 0.58/0.76         ((k3_tarski @ (k2_tarski @ X22 @ X23))
% 0.58/0.76           = (k5_xboole_0 @ X22 @ (k4_xboole_0 @ X23 @ X22)))),
% 0.58/0.76      inference('demod', [status(thm)], ['3', '4', '5', '8'])).
% 0.58/0.76  thf('146', plain,
% 0.58/0.76      (((k3_tarski @ (k2_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))
% 0.58/0.76         = (k5_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.58/0.76      inference('sup+', [status(thm)], ['144', '145'])).
% 0.58/0.76  thf('147', plain,
% 0.58/0.76      (((k3_tarski @ (k2_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))) = (sk_A))),
% 0.58/0.76      inference('sup+', [status(thm)], ['104', '146'])).
% 0.58/0.76  thf('148', plain,
% 0.58/0.76      (((k4_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 0.58/0.76         != (k2_subset_1 @ sk_A))),
% 0.58/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.76  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.58/0.76  thf('149', plain, (![X61 : $i]: ((k2_subset_1 @ X61) = (X61))),
% 0.58/0.76      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.58/0.76  thf('150', plain,
% 0.58/0.76      (((k4_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)) != (sk_A))),
% 0.58/0.76      inference('demod', [status(thm)], ['148', '149'])).
% 0.58/0.76  thf('151', plain,
% 0.58/0.76      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.58/0.76      inference('sup-', [status(thm)], ['105', '106'])).
% 0.58/0.76  thf('152', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.58/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.76  thf(redefinition_k4_subset_1, axiom,
% 0.58/0.76    (![A:$i,B:$i,C:$i]:
% 0.58/0.76     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.58/0.76         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.58/0.76       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.58/0.76  thf('153', plain,
% 0.58/0.76      (![X67 : $i, X68 : $i, X69 : $i]:
% 0.58/0.76         (~ (m1_subset_1 @ X67 @ (k1_zfmisc_1 @ X68))
% 0.58/0.76          | ~ (m1_subset_1 @ X69 @ (k1_zfmisc_1 @ X68))
% 0.58/0.76          | ((k4_subset_1 @ X68 @ X67 @ X69) = (k2_xboole_0 @ X67 @ X69)))),
% 0.58/0.76      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.58/0.76  thf('154', plain,
% 0.58/0.76      (![X56 : $i, X57 : $i]:
% 0.58/0.76         ((k3_tarski @ (k2_tarski @ X56 @ X57)) = (k2_xboole_0 @ X56 @ X57))),
% 0.58/0.76      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.58/0.76  thf('155', plain,
% 0.58/0.76      (![X67 : $i, X68 : $i, X69 : $i]:
% 0.58/0.76         (~ (m1_subset_1 @ X67 @ (k1_zfmisc_1 @ X68))
% 0.58/0.76          | ~ (m1_subset_1 @ X69 @ (k1_zfmisc_1 @ X68))
% 0.58/0.76          | ((k4_subset_1 @ X68 @ X67 @ X69)
% 0.58/0.76              = (k3_tarski @ (k2_tarski @ X67 @ X69))))),
% 0.58/0.76      inference('demod', [status(thm)], ['153', '154'])).
% 0.58/0.76  thf('156', plain,
% 0.58/0.76      (![X0 : $i]:
% 0.58/0.76         (((k4_subset_1 @ sk_A @ sk_B @ X0)
% 0.58/0.76            = (k3_tarski @ (k2_tarski @ sk_B @ X0)))
% 0.58/0.76          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 0.58/0.76      inference('sup-', [status(thm)], ['152', '155'])).
% 0.58/0.76  thf('157', plain,
% 0.58/0.76      (((k4_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 0.58/0.76         = (k3_tarski @ (k2_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))))),
% 0.58/0.76      inference('sup-', [status(thm)], ['151', '156'])).
% 0.58/0.76  thf('158', plain,
% 0.58/0.76      (((k3_tarski @ (k2_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))
% 0.58/0.76         != (sk_A))),
% 0.58/0.76      inference('demod', [status(thm)], ['150', '157'])).
% 0.58/0.76  thf('159', plain, ($false),
% 0.58/0.76      inference('simplify_reflect-', [status(thm)], ['147', '158'])).
% 0.58/0.76  
% 0.58/0.76  % SZS output end Refutation
% 0.58/0.76  
% 0.58/0.76  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
