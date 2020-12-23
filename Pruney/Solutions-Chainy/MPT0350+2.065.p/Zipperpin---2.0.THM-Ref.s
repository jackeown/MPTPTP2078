%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Z4np73fjI0

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:54 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 107 expanded)
%              Number of leaves         :   33 (  46 expanded)
%              Depth                    :   11
%              Number of atoms          :  571 ( 771 expanded)
%              Number of equality atoms :   50 (  66 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

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

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ! [X57: $i,X58: $i] :
      ( ( ( k3_subset_1 @ X57 @ X58 )
        = ( k4_xboole_0 @ X57 @ X58 ) )
      | ~ ( m1_subset_1 @ X58 @ ( k1_zfmisc_1 @ X57 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('2',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('3',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X8 @ X9 ) @ X8 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('4',plain,(
    r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_A ),
    inference('sup+',[status(thm)],['2','3'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('5',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ~ ( r1_tarski @ X46 @ X47 )
      | ( r2_hidden @ X46 @ X48 )
      | ( X48
       != ( k1_zfmisc_1 @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('6',plain,(
    ! [X46: $i,X47: $i] :
      ( ( r2_hidden @ X46 @ ( k1_zfmisc_1 @ X47 ) )
      | ~ ( r1_tarski @ X46 @ X47 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    r2_hidden @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('8',plain,(
    ! [X53: $i,X54: $i] :
      ( ~ ( r2_hidden @ X53 @ X54 )
      | ( m1_subset_1 @ X53 @ X54 )
      | ( v1_xboole_0 @ X54 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('9',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('10',plain,(
    ! [X59: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X59 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('11',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['9','10'])).

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
    ! [X60: $i,X61: $i,X62: $i] :
      ( ~ ( m1_subset_1 @ X60 @ ( k1_zfmisc_1 @ X61 ) )
      | ~ ( m1_subset_1 @ X62 @ ( k1_zfmisc_1 @ X61 ) )
      | ( ( k4_subset_1 @ X61 @ X60 @ X62 )
        = ( k2_xboole_0 @ X60 @ X62 ) ) ) ),
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
    ! [X60: $i,X61: $i,X62: $i] :
      ( ~ ( m1_subset_1 @ X60 @ ( k1_zfmisc_1 @ X61 ) )
      | ~ ( m1_subset_1 @ X62 @ ( k1_zfmisc_1 @ X61 ) )
      | ( ( k4_subset_1 @ X61 @ X60 @ X62 )
        = ( k3_tarski @ ( k2_tarski @ X60 @ X62 ) ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ sk_A @ sk_B @ X0 )
        = ( k3_tarski @ ( k2_tarski @ sk_B @ X0 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k3_tarski @ ( k2_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['11','16'])).

thf('18',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('19',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_xboole_0 @ X10 @ ( k4_xboole_0 @ X11 @ X10 ) )
      = ( k2_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('20',plain,(
    ! [X51: $i,X52: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X51 @ X52 ) )
      = ( k2_xboole_0 @ X51 @ X52 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('21',plain,(
    ! [X51: $i,X52: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X51 @ X52 ) )
      = ( k2_xboole_0 @ X51 @ X52 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('22',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X10 @ ( k4_xboole_0 @ X11 @ X10 ) ) )
      = ( k3_tarski @ ( k2_tarski @ X10 @ X11 ) ) ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('23',plain,
    ( ( k3_tarski @ ( k2_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) )
    = ( k3_tarski @ ( k2_tarski @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['18','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X53: $i,X54: $i] :
      ( ~ ( m1_subset_1 @ X53 @ X54 )
      | ( r2_hidden @ X53 @ X54 )
      | ( v1_xboole_0 @ X54 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('26',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X59: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X59 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('28',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X47: $i,X48: $i,X49: $i] :
      ( ~ ( r2_hidden @ X49 @ X48 )
      | ( r1_tarski @ X49 @ X47 )
      | ( X48
       != ( k1_zfmisc_1 @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('30',plain,(
    ! [X47: $i,X49: $i] :
      ( ( r1_tarski @ X49 @ X47 )
      | ~ ( r2_hidden @ X49 @ ( k1_zfmisc_1 @ X47 ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['28','30'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('32',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_xboole_0 @ X6 @ X7 )
        = X6 )
      | ~ ( r1_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('33',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['31','32'])).

thf(t94_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('34',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X17 @ X18 ) @ ( k3_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t94_xboole_1])).

thf('35',plain,(
    ! [X51: $i,X52: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X51 @ X52 ) )
      = ( k2_xboole_0 @ X51 @ X52 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('36',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k5_xboole_0 @ X13 @ ( k5_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('37',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X17 @ X18 ) )
      = ( k5_xboole_0 @ X17 @ ( k5_xboole_0 @ X18 @ ( k3_xboole_0 @ X17 @ X18 ) ) ) ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('38',plain,
    ( ( k3_tarski @ ( k2_tarski @ sk_B @ sk_A ) )
    = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['33','37'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('39',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('40',plain,(
    ! [X16: $i] :
      ( ( k5_xboole_0 @ X16 @ X16 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('41',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k5_xboole_0 @ X13 @ ( k5_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('44',plain,(
    ! [X12: $i] :
      ( ( k5_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['42','45'])).

thf('47',plain,
    ( ( k3_tarski @ ( k2_tarski @ sk_B @ sk_A ) )
    = sk_A ),
    inference(demod,[status(thm)],['38','39','46'])).

thf('48',plain,
    ( ( k3_tarski @ ( k2_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) )
    = sk_A ),
    inference(demod,[status(thm)],['23','47'])).

thf('49',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = sk_A ),
    inference(demod,[status(thm)],['17','48'])).

thf('50',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
 != ( k2_subset_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('51',plain,(
    ! [X56: $i] :
      ( ( k2_subset_1 @ X56 )
      = X56 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('52',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
 != sk_A ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['49','52'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Z4np73fjI0
% 0.13/0.33  % Computer   : n019.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 10:15:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.39/0.58  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.39/0.58  % Solved by: fo/fo7.sh
% 0.39/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.58  % done 439 iterations in 0.143s
% 0.39/0.58  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.39/0.58  % SZS output start Refutation
% 0.39/0.58  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.39/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.39/0.58  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.39/0.58  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.39/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.39/0.58  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.39/0.58  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.39/0.58  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.39/0.58  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.39/0.58  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.39/0.58  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.39/0.58  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.39/0.58  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.39/0.58  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.39/0.58  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.39/0.58  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.39/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.58  thf(t25_subset_1, conjecture,
% 0.39/0.58    (![A:$i,B:$i]:
% 0.39/0.58     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.39/0.58       ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) ) =
% 0.39/0.58         ( k2_subset_1 @ A ) ) ))).
% 0.39/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.58    (~( ![A:$i,B:$i]:
% 0.39/0.58        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.39/0.58          ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) ) =
% 0.39/0.58            ( k2_subset_1 @ A ) ) ) )),
% 0.39/0.58    inference('cnf.neg', [status(esa)], [t25_subset_1])).
% 0.39/0.58  thf('0', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf(d5_subset_1, axiom,
% 0.39/0.58    (![A:$i,B:$i]:
% 0.39/0.58     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.39/0.58       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.39/0.58  thf('1', plain,
% 0.39/0.58      (![X57 : $i, X58 : $i]:
% 0.39/0.58         (((k3_subset_1 @ X57 @ X58) = (k4_xboole_0 @ X57 @ X58))
% 0.39/0.58          | ~ (m1_subset_1 @ X58 @ (k1_zfmisc_1 @ X57)))),
% 0.39/0.58      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.39/0.58  thf('2', plain,
% 0.39/0.58      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.39/0.58      inference('sup-', [status(thm)], ['0', '1'])).
% 0.39/0.58  thf(t36_xboole_1, axiom,
% 0.39/0.58    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.39/0.58  thf('3', plain,
% 0.39/0.58      (![X8 : $i, X9 : $i]: (r1_tarski @ (k4_xboole_0 @ X8 @ X9) @ X8)),
% 0.39/0.58      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.39/0.58  thf('4', plain, ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_A)),
% 0.39/0.58      inference('sup+', [status(thm)], ['2', '3'])).
% 0.39/0.58  thf(d1_zfmisc_1, axiom,
% 0.39/0.58    (![A:$i,B:$i]:
% 0.39/0.58     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.39/0.58       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.39/0.58  thf('5', plain,
% 0.39/0.58      (![X46 : $i, X47 : $i, X48 : $i]:
% 0.39/0.58         (~ (r1_tarski @ X46 @ X47)
% 0.39/0.58          | (r2_hidden @ X46 @ X48)
% 0.39/0.58          | ((X48) != (k1_zfmisc_1 @ X47)))),
% 0.39/0.58      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.39/0.58  thf('6', plain,
% 0.39/0.58      (![X46 : $i, X47 : $i]:
% 0.39/0.58         ((r2_hidden @ X46 @ (k1_zfmisc_1 @ X47)) | ~ (r1_tarski @ X46 @ X47))),
% 0.39/0.58      inference('simplify', [status(thm)], ['5'])).
% 0.39/0.58  thf('7', plain,
% 0.39/0.58      ((r2_hidden @ (k3_subset_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.39/0.58      inference('sup-', [status(thm)], ['4', '6'])).
% 0.39/0.58  thf(d2_subset_1, axiom,
% 0.39/0.58    (![A:$i,B:$i]:
% 0.39/0.58     ( ( ( v1_xboole_0 @ A ) =>
% 0.39/0.58         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.39/0.58       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.39/0.58         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.39/0.58  thf('8', plain,
% 0.39/0.58      (![X53 : $i, X54 : $i]:
% 0.39/0.58         (~ (r2_hidden @ X53 @ X54)
% 0.39/0.58          | (m1_subset_1 @ X53 @ X54)
% 0.39/0.58          | (v1_xboole_0 @ X54))),
% 0.39/0.58      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.39/0.58  thf('9', plain,
% 0.39/0.58      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.39/0.58        | (m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['7', '8'])).
% 0.39/0.58  thf(fc1_subset_1, axiom,
% 0.39/0.58    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.39/0.58  thf('10', plain, (![X59 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X59))),
% 0.39/0.58      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.39/0.58  thf('11', plain,
% 0.39/0.58      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.39/0.58      inference('clc', [status(thm)], ['9', '10'])).
% 0.39/0.58  thf('12', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf(redefinition_k4_subset_1, axiom,
% 0.39/0.58    (![A:$i,B:$i,C:$i]:
% 0.39/0.58     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.39/0.58         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.39/0.58       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.39/0.58  thf('13', plain,
% 0.39/0.58      (![X60 : $i, X61 : $i, X62 : $i]:
% 0.39/0.58         (~ (m1_subset_1 @ X60 @ (k1_zfmisc_1 @ X61))
% 0.39/0.58          | ~ (m1_subset_1 @ X62 @ (k1_zfmisc_1 @ X61))
% 0.39/0.58          | ((k4_subset_1 @ X61 @ X60 @ X62) = (k2_xboole_0 @ X60 @ X62)))),
% 0.39/0.58      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.39/0.58  thf(l51_zfmisc_1, axiom,
% 0.39/0.58    (![A:$i,B:$i]:
% 0.39/0.58     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.39/0.58  thf('14', plain,
% 0.39/0.58      (![X51 : $i, X52 : $i]:
% 0.39/0.58         ((k3_tarski @ (k2_tarski @ X51 @ X52)) = (k2_xboole_0 @ X51 @ X52))),
% 0.39/0.58      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.39/0.58  thf('15', plain,
% 0.39/0.58      (![X60 : $i, X61 : $i, X62 : $i]:
% 0.39/0.58         (~ (m1_subset_1 @ X60 @ (k1_zfmisc_1 @ X61))
% 0.39/0.58          | ~ (m1_subset_1 @ X62 @ (k1_zfmisc_1 @ X61))
% 0.39/0.58          | ((k4_subset_1 @ X61 @ X60 @ X62)
% 0.39/0.58              = (k3_tarski @ (k2_tarski @ X60 @ X62))))),
% 0.39/0.58      inference('demod', [status(thm)], ['13', '14'])).
% 0.39/0.58  thf('16', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         (((k4_subset_1 @ sk_A @ sk_B @ X0)
% 0.39/0.58            = (k3_tarski @ (k2_tarski @ sk_B @ X0)))
% 0.39/0.58          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['12', '15'])).
% 0.39/0.58  thf('17', plain,
% 0.39/0.58      (((k4_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 0.39/0.58         = (k3_tarski @ (k2_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))))),
% 0.39/0.58      inference('sup-', [status(thm)], ['11', '16'])).
% 0.39/0.58  thf('18', plain,
% 0.39/0.58      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.39/0.58      inference('sup-', [status(thm)], ['0', '1'])).
% 0.39/0.58  thf(t39_xboole_1, axiom,
% 0.39/0.58    (![A:$i,B:$i]:
% 0.39/0.58     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.39/0.58  thf('19', plain,
% 0.39/0.58      (![X10 : $i, X11 : $i]:
% 0.39/0.58         ((k2_xboole_0 @ X10 @ (k4_xboole_0 @ X11 @ X10))
% 0.39/0.58           = (k2_xboole_0 @ X10 @ X11))),
% 0.39/0.58      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.39/0.58  thf('20', plain,
% 0.39/0.58      (![X51 : $i, X52 : $i]:
% 0.39/0.58         ((k3_tarski @ (k2_tarski @ X51 @ X52)) = (k2_xboole_0 @ X51 @ X52))),
% 0.39/0.58      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.39/0.58  thf('21', plain,
% 0.39/0.58      (![X51 : $i, X52 : $i]:
% 0.39/0.58         ((k3_tarski @ (k2_tarski @ X51 @ X52)) = (k2_xboole_0 @ X51 @ X52))),
% 0.39/0.58      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.39/0.58  thf('22', plain,
% 0.39/0.58      (![X10 : $i, X11 : $i]:
% 0.39/0.58         ((k3_tarski @ (k2_tarski @ X10 @ (k4_xboole_0 @ X11 @ X10)))
% 0.39/0.58           = (k3_tarski @ (k2_tarski @ X10 @ X11)))),
% 0.39/0.58      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.39/0.58  thf('23', plain,
% 0.39/0.58      (((k3_tarski @ (k2_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))
% 0.39/0.58         = (k3_tarski @ (k2_tarski @ sk_B @ sk_A)))),
% 0.39/0.58      inference('sup+', [status(thm)], ['18', '22'])).
% 0.39/0.58  thf('24', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('25', plain,
% 0.39/0.58      (![X53 : $i, X54 : $i]:
% 0.39/0.58         (~ (m1_subset_1 @ X53 @ X54)
% 0.39/0.58          | (r2_hidden @ X53 @ X54)
% 0.39/0.58          | (v1_xboole_0 @ X54))),
% 0.39/0.58      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.39/0.58  thf('26', plain,
% 0.39/0.58      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.39/0.58        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['24', '25'])).
% 0.39/0.58  thf('27', plain, (![X59 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X59))),
% 0.39/0.58      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.39/0.58  thf('28', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.39/0.58      inference('clc', [status(thm)], ['26', '27'])).
% 0.39/0.58  thf('29', plain,
% 0.39/0.58      (![X47 : $i, X48 : $i, X49 : $i]:
% 0.39/0.58         (~ (r2_hidden @ X49 @ X48)
% 0.39/0.58          | (r1_tarski @ X49 @ X47)
% 0.39/0.58          | ((X48) != (k1_zfmisc_1 @ X47)))),
% 0.39/0.58      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.39/0.58  thf('30', plain,
% 0.39/0.58      (![X47 : $i, X49 : $i]:
% 0.39/0.58         ((r1_tarski @ X49 @ X47) | ~ (r2_hidden @ X49 @ (k1_zfmisc_1 @ X47)))),
% 0.39/0.58      inference('simplify', [status(thm)], ['29'])).
% 0.39/0.58  thf('31', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.39/0.58      inference('sup-', [status(thm)], ['28', '30'])).
% 0.39/0.58  thf(t28_xboole_1, axiom,
% 0.39/0.58    (![A:$i,B:$i]:
% 0.39/0.58     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.39/0.58  thf('32', plain,
% 0.39/0.58      (![X6 : $i, X7 : $i]:
% 0.39/0.58         (((k3_xboole_0 @ X6 @ X7) = (X6)) | ~ (r1_tarski @ X6 @ X7))),
% 0.39/0.58      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.39/0.58  thf('33', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 0.39/0.58      inference('sup-', [status(thm)], ['31', '32'])).
% 0.39/0.58  thf(t94_xboole_1, axiom,
% 0.39/0.58    (![A:$i,B:$i]:
% 0.39/0.58     ( ( k2_xboole_0 @ A @ B ) =
% 0.39/0.58       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.39/0.58  thf('34', plain,
% 0.39/0.58      (![X17 : $i, X18 : $i]:
% 0.39/0.58         ((k2_xboole_0 @ X17 @ X18)
% 0.39/0.58           = (k5_xboole_0 @ (k5_xboole_0 @ X17 @ X18) @ 
% 0.39/0.58              (k3_xboole_0 @ X17 @ X18)))),
% 0.39/0.58      inference('cnf', [status(esa)], [t94_xboole_1])).
% 0.39/0.58  thf('35', plain,
% 0.39/0.58      (![X51 : $i, X52 : $i]:
% 0.39/0.58         ((k3_tarski @ (k2_tarski @ X51 @ X52)) = (k2_xboole_0 @ X51 @ X52))),
% 0.39/0.58      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.39/0.58  thf(t91_xboole_1, axiom,
% 0.39/0.58    (![A:$i,B:$i,C:$i]:
% 0.39/0.58     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.39/0.58       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.39/0.58  thf('36', plain,
% 0.39/0.58      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.39/0.58         ((k5_xboole_0 @ (k5_xboole_0 @ X13 @ X14) @ X15)
% 0.39/0.58           = (k5_xboole_0 @ X13 @ (k5_xboole_0 @ X14 @ X15)))),
% 0.39/0.58      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.39/0.58  thf('37', plain,
% 0.39/0.58      (![X17 : $i, X18 : $i]:
% 0.39/0.58         ((k3_tarski @ (k2_tarski @ X17 @ X18))
% 0.39/0.58           = (k5_xboole_0 @ X17 @ 
% 0.39/0.58              (k5_xboole_0 @ X18 @ (k3_xboole_0 @ X17 @ X18))))),
% 0.39/0.58      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.39/0.58  thf('38', plain,
% 0.39/0.58      (((k3_tarski @ (k2_tarski @ sk_B @ sk_A))
% 0.39/0.58         = (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_A @ sk_B)))),
% 0.39/0.58      inference('sup+', [status(thm)], ['33', '37'])).
% 0.39/0.58  thf(commutativity_k5_xboole_0, axiom,
% 0.39/0.58    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.39/0.58  thf('39', plain,
% 0.39/0.58      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.39/0.58      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.39/0.58  thf(t92_xboole_1, axiom,
% 0.39/0.58    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.39/0.58  thf('40', plain, (![X16 : $i]: ((k5_xboole_0 @ X16 @ X16) = (k1_xboole_0))),
% 0.39/0.58      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.39/0.58  thf('41', plain,
% 0.39/0.58      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.39/0.58         ((k5_xboole_0 @ (k5_xboole_0 @ X13 @ X14) @ X15)
% 0.39/0.58           = (k5_xboole_0 @ X13 @ (k5_xboole_0 @ X14 @ X15)))),
% 0.39/0.58      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.39/0.58  thf('42', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i]:
% 0.39/0.58         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.39/0.58           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.39/0.58      inference('sup+', [status(thm)], ['40', '41'])).
% 0.39/0.58  thf('43', plain,
% 0.39/0.58      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.39/0.58      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.39/0.58  thf(t5_boole, axiom,
% 0.39/0.58    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.39/0.58  thf('44', plain, (![X12 : $i]: ((k5_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.39/0.58      inference('cnf', [status(esa)], [t5_boole])).
% 0.39/0.58  thf('45', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.39/0.58      inference('sup+', [status(thm)], ['43', '44'])).
% 0.39/0.58  thf('46', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i]:
% 0.39/0.58         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.39/0.58      inference('demod', [status(thm)], ['42', '45'])).
% 0.39/0.58  thf('47', plain, (((k3_tarski @ (k2_tarski @ sk_B @ sk_A)) = (sk_A))),
% 0.39/0.58      inference('demod', [status(thm)], ['38', '39', '46'])).
% 0.39/0.58  thf('48', plain,
% 0.39/0.58      (((k3_tarski @ (k2_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))) = (sk_A))),
% 0.39/0.58      inference('demod', [status(thm)], ['23', '47'])).
% 0.39/0.58  thf('49', plain,
% 0.39/0.58      (((k4_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)) = (sk_A))),
% 0.39/0.58      inference('demod', [status(thm)], ['17', '48'])).
% 0.39/0.58  thf('50', plain,
% 0.39/0.58      (((k4_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 0.39/0.58         != (k2_subset_1 @ sk_A))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.39/0.58  thf('51', plain, (![X56 : $i]: ((k2_subset_1 @ X56) = (X56))),
% 0.39/0.58      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.39/0.58  thf('52', plain,
% 0.39/0.58      (((k4_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)) != (sk_A))),
% 0.39/0.58      inference('demod', [status(thm)], ['50', '51'])).
% 0.39/0.58  thf('53', plain, ($false),
% 0.39/0.58      inference('simplify_reflect-', [status(thm)], ['49', '52'])).
% 0.39/0.58  
% 0.39/0.58  % SZS output end Refutation
% 0.39/0.58  
% 0.39/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
