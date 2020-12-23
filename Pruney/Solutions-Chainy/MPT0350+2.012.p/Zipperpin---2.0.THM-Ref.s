%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.vRBKljPwWb

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:46 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 195 expanded)
%              Number of leaves         :   34 (  71 expanded)
%              Depth                    :   14
%              Number of atoms          :  585 (1472 expanded)
%              Number of equality atoms :   50 ( 100 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

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

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('1',plain,(
    ! [X59: $i,X60: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X59 @ X60 ) @ ( k1_zfmisc_1 @ X59 ) )
      | ~ ( m1_subset_1 @ X60 @ ( k1_zfmisc_1 @ X59 ) ) ) ),
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
    m1_subset_1 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(demod,[status(thm)],['2','5'])).

thf('7',plain,(
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

thf('8',plain,(
    ! [X53: $i,X54: $i] :
      ( ~ ( m1_subset_1 @ X53 @ X54 )
      | ( r2_hidden @ X53 @ X54 )
      | ( v1_xboole_0 @ X54 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('9',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('10',plain,(
    ! [X61: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X61 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('11',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['9','10'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('12',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d4_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k3_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( ( r2_hidden @ D @ A )
              & ( r2_hidden @ C @ D ) ) ) ) )).

thf('13',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ~ ( r2_hidden @ X43 @ X44 )
      | ~ ( r2_hidden @ X45 @ X43 )
      | ( r2_hidden @ X45 @ X46 )
      | ( X46
       != ( k3_tarski @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf('14',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ( r2_hidden @ X45 @ ( k3_tarski @ X44 ) )
      | ~ ( r2_hidden @ X45 @ X43 )
      | ~ ( r2_hidden @ X43 @ X44 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r2_hidden @ X0 @ X2 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k3_tarski @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( k3_tarski @ ( k1_zfmisc_1 @ sk_A ) ) )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','15'])).

thf(t99_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) )
      = A ) )).

thf('17',plain,(
    ! [X52: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ X52 ) )
      = X52 ) ),
    inference(cnf,[status(esa)],[t99_zfmisc_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ sk_A )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ~ ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('20',plain,
    ( ( r1_tarski @ sk_B @ sk_A )
    | ( r1_tarski @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference(simplify,[status(thm)],['20'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('22',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('23',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['21','22'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('25',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ X7 )
      = ( k5_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['23','26'])).

thf('28',plain,(
    m1_subset_1 @ ( k5_xboole_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(demod,[status(thm)],['6','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('30',plain,(
    ! [X62: $i,X63: $i,X64: $i] :
      ( ~ ( m1_subset_1 @ X62 @ ( k1_zfmisc_1 @ X63 ) )
      | ~ ( m1_subset_1 @ X64 @ ( k1_zfmisc_1 @ X63 ) )
      | ( ( k4_subset_1 @ X63 @ X62 @ X64 )
        = ( k2_xboole_0 @ X62 @ X64 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ sk_A @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ ( k5_xboole_0 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['23','26'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('34',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_xboole_0 @ X12 @ ( k4_xboole_0 @ X13 @ X12 ) )
      = ( k2_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('35',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['21','22'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = A ) )).

thf('38',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k2_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) )
      = X8 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference('sup+',[status(thm)],['36','39'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('41',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_tarski @ X15 @ X14 )
      = ( k2_tarski @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('42',plain,(
    ! [X50: $i,X51: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X50 @ X51 ) )
      = ( k2_xboole_0 @ X50 @ X51 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X50: $i,X51: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X50 @ X51 ) )
      = ( k2_xboole_0 @ X50 @ X51 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = sk_A ),
    inference(demod,[status(thm)],['40','45'])).

thf('47',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_A @ sk_B ) )
    = sk_A ),
    inference(demod,[status(thm)],['35','46'])).

thf('48',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ ( k5_xboole_0 @ sk_A @ sk_B ) )
    = sk_A ),
    inference(demod,[status(thm)],['32','47'])).

thf('49',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
 != ( k2_subset_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('50',plain,(
    ! [X56: $i] :
      ( ( k2_subset_1 @ X56 )
      = X56 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('51',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
 != sk_A ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('53',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) )
 != sk_A ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['23','26'])).

thf('55',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ ( k5_xboole_0 @ sk_A @ sk_B ) )
 != sk_A ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['48','55'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.vRBKljPwWb
% 0.13/0.35  % Computer   : n005.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:04:33 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.39/0.58  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.39/0.58  % Solved by: fo/fo7.sh
% 0.39/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.58  % done 228 iterations in 0.118s
% 0.39/0.58  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.39/0.58  % SZS output start Refutation
% 0.39/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.39/0.58  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.39/0.58  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.39/0.58  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.39/0.58  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.39/0.58  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.39/0.58  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.39/0.58  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.39/0.58  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.39/0.58  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.39/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.39/0.58  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.39/0.58  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.39/0.58  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.39/0.58  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.39/0.58  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
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
% 0.39/0.58  thf(dt_k3_subset_1, axiom,
% 0.39/0.58    (![A:$i,B:$i]:
% 0.39/0.58     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.39/0.58       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.39/0.58  thf('1', plain,
% 0.39/0.58      (![X59 : $i, X60 : $i]:
% 0.39/0.58         ((m1_subset_1 @ (k3_subset_1 @ X59 @ X60) @ (k1_zfmisc_1 @ X59))
% 0.39/0.58          | ~ (m1_subset_1 @ X60 @ (k1_zfmisc_1 @ X59)))),
% 0.39/0.58      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.39/0.58  thf('2', plain,
% 0.39/0.58      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.39/0.58      inference('sup-', [status(thm)], ['0', '1'])).
% 0.39/0.58  thf('3', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf(d5_subset_1, axiom,
% 0.39/0.58    (![A:$i,B:$i]:
% 0.39/0.58     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.39/0.58       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.39/0.58  thf('4', plain,
% 0.39/0.58      (![X57 : $i, X58 : $i]:
% 0.39/0.58         (((k3_subset_1 @ X57 @ X58) = (k4_xboole_0 @ X57 @ X58))
% 0.39/0.58          | ~ (m1_subset_1 @ X58 @ (k1_zfmisc_1 @ X57)))),
% 0.39/0.58      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.39/0.58  thf('5', plain,
% 0.39/0.58      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.39/0.58      inference('sup-', [status(thm)], ['3', '4'])).
% 0.39/0.58  thf('6', plain,
% 0.39/0.58      ((m1_subset_1 @ (k4_xboole_0 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.39/0.58      inference('demod', [status(thm)], ['2', '5'])).
% 0.39/0.58  thf('7', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf(d2_subset_1, axiom,
% 0.39/0.58    (![A:$i,B:$i]:
% 0.39/0.58     ( ( ( v1_xboole_0 @ A ) =>
% 0.39/0.58         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.39/0.58       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.39/0.58         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.39/0.58  thf('8', plain,
% 0.39/0.58      (![X53 : $i, X54 : $i]:
% 0.39/0.58         (~ (m1_subset_1 @ X53 @ X54)
% 0.39/0.58          | (r2_hidden @ X53 @ X54)
% 0.39/0.58          | (v1_xboole_0 @ X54))),
% 0.39/0.58      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.39/0.58  thf('9', plain,
% 0.39/0.58      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.39/0.58        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['7', '8'])).
% 0.39/0.58  thf(fc1_subset_1, axiom,
% 0.39/0.58    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.39/0.58  thf('10', plain, (![X61 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X61))),
% 0.39/0.58      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.39/0.58  thf('11', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.39/0.58      inference('clc', [status(thm)], ['9', '10'])).
% 0.39/0.58  thf(d3_tarski, axiom,
% 0.39/0.58    (![A:$i,B:$i]:
% 0.39/0.58     ( ( r1_tarski @ A @ B ) <=>
% 0.39/0.58       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.39/0.58  thf('12', plain,
% 0.39/0.58      (![X3 : $i, X5 : $i]:
% 0.39/0.58         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.39/0.58      inference('cnf', [status(esa)], [d3_tarski])).
% 0.39/0.58  thf(d4_tarski, axiom,
% 0.39/0.58    (![A:$i,B:$i]:
% 0.39/0.58     ( ( ( B ) = ( k3_tarski @ A ) ) <=>
% 0.39/0.58       ( ![C:$i]:
% 0.39/0.58         ( ( r2_hidden @ C @ B ) <=>
% 0.39/0.58           ( ?[D:$i]: ( ( r2_hidden @ D @ A ) & ( r2_hidden @ C @ D ) ) ) ) ) ))).
% 0.39/0.58  thf('13', plain,
% 0.39/0.58      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 0.39/0.58         (~ (r2_hidden @ X43 @ X44)
% 0.39/0.58          | ~ (r2_hidden @ X45 @ X43)
% 0.39/0.58          | (r2_hidden @ X45 @ X46)
% 0.39/0.58          | ((X46) != (k3_tarski @ X44)))),
% 0.39/0.58      inference('cnf', [status(esa)], [d4_tarski])).
% 0.39/0.58  thf('14', plain,
% 0.39/0.58      (![X43 : $i, X44 : $i, X45 : $i]:
% 0.39/0.58         ((r2_hidden @ X45 @ (k3_tarski @ X44))
% 0.39/0.58          | ~ (r2_hidden @ X45 @ X43)
% 0.39/0.58          | ~ (r2_hidden @ X43 @ X44))),
% 0.39/0.58      inference('simplify', [status(thm)], ['13'])).
% 0.39/0.58  thf('15', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.58         ((r1_tarski @ X0 @ X1)
% 0.39/0.58          | ~ (r2_hidden @ X0 @ X2)
% 0.39/0.58          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k3_tarski @ X2)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['12', '14'])).
% 0.39/0.58  thf('16', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         ((r2_hidden @ (sk_C @ X0 @ sk_B) @ (k3_tarski @ (k1_zfmisc_1 @ sk_A)))
% 0.39/0.58          | (r1_tarski @ sk_B @ X0))),
% 0.39/0.58      inference('sup-', [status(thm)], ['11', '15'])).
% 0.39/0.58  thf(t99_zfmisc_1, axiom,
% 0.39/0.58    (![A:$i]: ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) ) = ( A ) ))).
% 0.39/0.58  thf('17', plain, (![X52 : $i]: ((k3_tarski @ (k1_zfmisc_1 @ X52)) = (X52))),
% 0.39/0.58      inference('cnf', [status(esa)], [t99_zfmisc_1])).
% 0.39/0.58  thf('18', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         ((r2_hidden @ (sk_C @ X0 @ sk_B) @ sk_A) | (r1_tarski @ sk_B @ X0))),
% 0.39/0.58      inference('demod', [status(thm)], ['16', '17'])).
% 0.39/0.58  thf('19', plain,
% 0.39/0.58      (![X3 : $i, X5 : $i]:
% 0.39/0.58         ((r1_tarski @ X3 @ X5) | ~ (r2_hidden @ (sk_C @ X5 @ X3) @ X5))),
% 0.39/0.58      inference('cnf', [status(esa)], [d3_tarski])).
% 0.39/0.58  thf('20', plain, (((r1_tarski @ sk_B @ sk_A) | (r1_tarski @ sk_B @ sk_A))),
% 0.39/0.58      inference('sup-', [status(thm)], ['18', '19'])).
% 0.39/0.58  thf('21', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.39/0.58      inference('simplify', [status(thm)], ['20'])).
% 0.39/0.58  thf(t28_xboole_1, axiom,
% 0.39/0.58    (![A:$i,B:$i]:
% 0.39/0.58     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.39/0.58  thf('22', plain,
% 0.39/0.58      (![X10 : $i, X11 : $i]:
% 0.39/0.58         (((k3_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_tarski @ X10 @ X11))),
% 0.39/0.58      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.39/0.58  thf('23', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 0.39/0.58      inference('sup-', [status(thm)], ['21', '22'])).
% 0.39/0.58  thf(commutativity_k3_xboole_0, axiom,
% 0.39/0.58    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.39/0.58  thf('24', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.39/0.58      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.39/0.58  thf(t100_xboole_1, axiom,
% 0.39/0.58    (![A:$i,B:$i]:
% 0.39/0.58     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.39/0.58  thf('25', plain,
% 0.39/0.58      (![X6 : $i, X7 : $i]:
% 0.39/0.58         ((k4_xboole_0 @ X6 @ X7)
% 0.39/0.58           = (k5_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)))),
% 0.39/0.58      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.39/0.58  thf('26', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i]:
% 0.39/0.58         ((k4_xboole_0 @ X0 @ X1)
% 0.39/0.58           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.39/0.58      inference('sup+', [status(thm)], ['24', '25'])).
% 0.39/0.58  thf('27', plain,
% 0.39/0.58      (((k4_xboole_0 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 0.39/0.58      inference('sup+', [status(thm)], ['23', '26'])).
% 0.39/0.58  thf('28', plain,
% 0.39/0.58      ((m1_subset_1 @ (k5_xboole_0 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.39/0.58      inference('demod', [status(thm)], ['6', '27'])).
% 0.39/0.58  thf('29', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf(redefinition_k4_subset_1, axiom,
% 0.39/0.58    (![A:$i,B:$i,C:$i]:
% 0.39/0.58     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.39/0.58         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.39/0.58       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.39/0.58  thf('30', plain,
% 0.39/0.58      (![X62 : $i, X63 : $i, X64 : $i]:
% 0.39/0.58         (~ (m1_subset_1 @ X62 @ (k1_zfmisc_1 @ X63))
% 0.39/0.58          | ~ (m1_subset_1 @ X64 @ (k1_zfmisc_1 @ X63))
% 0.39/0.58          | ((k4_subset_1 @ X63 @ X62 @ X64) = (k2_xboole_0 @ X62 @ X64)))),
% 0.39/0.58      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.39/0.58  thf('31', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         (((k4_subset_1 @ sk_A @ sk_B @ X0) = (k2_xboole_0 @ sk_B @ X0))
% 0.39/0.58          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['29', '30'])).
% 0.39/0.58  thf('32', plain,
% 0.39/0.58      (((k4_subset_1 @ sk_A @ sk_B @ (k5_xboole_0 @ sk_A @ sk_B))
% 0.39/0.58         = (k2_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_A @ sk_B)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['28', '31'])).
% 0.39/0.58  thf('33', plain,
% 0.39/0.58      (((k4_xboole_0 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 0.39/0.58      inference('sup+', [status(thm)], ['23', '26'])).
% 0.39/0.58  thf(t39_xboole_1, axiom,
% 0.39/0.58    (![A:$i,B:$i]:
% 0.39/0.58     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.39/0.58  thf('34', plain,
% 0.39/0.58      (![X12 : $i, X13 : $i]:
% 0.39/0.58         ((k2_xboole_0 @ X12 @ (k4_xboole_0 @ X13 @ X12))
% 0.39/0.58           = (k2_xboole_0 @ X12 @ X13))),
% 0.39/0.58      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.39/0.58  thf('35', plain,
% 0.39/0.58      (((k2_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_A @ sk_B))
% 0.39/0.58         = (k2_xboole_0 @ sk_B @ sk_A))),
% 0.39/0.58      inference('sup+', [status(thm)], ['33', '34'])).
% 0.39/0.58  thf('36', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 0.39/0.58      inference('sup-', [status(thm)], ['21', '22'])).
% 0.39/0.58  thf('37', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.39/0.58      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.39/0.58  thf(t22_xboole_1, axiom,
% 0.39/0.58    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.39/0.58  thf('38', plain,
% 0.39/0.58      (![X8 : $i, X9 : $i]:
% 0.39/0.58         ((k2_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)) = (X8))),
% 0.39/0.58      inference('cnf', [status(esa)], [t22_xboole_1])).
% 0.39/0.58  thf('39', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i]:
% 0.39/0.58         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)) = (X0))),
% 0.39/0.58      inference('sup+', [status(thm)], ['37', '38'])).
% 0.39/0.58  thf('40', plain, (((k2_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 0.39/0.58      inference('sup+', [status(thm)], ['36', '39'])).
% 0.39/0.58  thf(commutativity_k2_tarski, axiom,
% 0.39/0.58    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.39/0.58  thf('41', plain,
% 0.39/0.58      (![X14 : $i, X15 : $i]:
% 0.39/0.58         ((k2_tarski @ X15 @ X14) = (k2_tarski @ X14 @ X15))),
% 0.39/0.58      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.39/0.58  thf(l51_zfmisc_1, axiom,
% 0.39/0.58    (![A:$i,B:$i]:
% 0.39/0.58     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.39/0.58  thf('42', plain,
% 0.39/0.58      (![X50 : $i, X51 : $i]:
% 0.39/0.58         ((k3_tarski @ (k2_tarski @ X50 @ X51)) = (k2_xboole_0 @ X50 @ X51))),
% 0.39/0.58      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.39/0.58  thf('43', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i]:
% 0.39/0.58         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.39/0.58      inference('sup+', [status(thm)], ['41', '42'])).
% 0.39/0.58  thf('44', plain,
% 0.39/0.58      (![X50 : $i, X51 : $i]:
% 0.39/0.58         ((k3_tarski @ (k2_tarski @ X50 @ X51)) = (k2_xboole_0 @ X50 @ X51))),
% 0.39/0.58      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.39/0.58  thf('45', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.39/0.58      inference('sup+', [status(thm)], ['43', '44'])).
% 0.39/0.58  thf('46', plain, (((k2_xboole_0 @ sk_B @ sk_A) = (sk_A))),
% 0.39/0.58      inference('demod', [status(thm)], ['40', '45'])).
% 0.39/0.58  thf('47', plain,
% 0.39/0.58      (((k2_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_A @ sk_B)) = (sk_A))),
% 0.39/0.58      inference('demod', [status(thm)], ['35', '46'])).
% 0.39/0.58  thf('48', plain,
% 0.39/0.58      (((k4_subset_1 @ sk_A @ sk_B @ (k5_xboole_0 @ sk_A @ sk_B)) = (sk_A))),
% 0.39/0.58      inference('demod', [status(thm)], ['32', '47'])).
% 0.39/0.58  thf('49', plain,
% 0.39/0.58      (((k4_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 0.39/0.58         != (k2_subset_1 @ sk_A))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.39/0.58  thf('50', plain, (![X56 : $i]: ((k2_subset_1 @ X56) = (X56))),
% 0.39/0.58      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.39/0.58  thf('51', plain,
% 0.39/0.58      (((k4_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)) != (sk_A))),
% 0.39/0.58      inference('demod', [status(thm)], ['49', '50'])).
% 0.39/0.58  thf('52', plain,
% 0.39/0.58      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.39/0.58      inference('sup-', [status(thm)], ['3', '4'])).
% 0.39/0.58  thf('53', plain,
% 0.39/0.58      (((k4_subset_1 @ sk_A @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B)) != (sk_A))),
% 0.39/0.58      inference('demod', [status(thm)], ['51', '52'])).
% 0.39/0.58  thf('54', plain,
% 0.39/0.58      (((k4_xboole_0 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 0.39/0.58      inference('sup+', [status(thm)], ['23', '26'])).
% 0.39/0.58  thf('55', plain,
% 0.39/0.58      (((k4_subset_1 @ sk_A @ sk_B @ (k5_xboole_0 @ sk_A @ sk_B)) != (sk_A))),
% 0.39/0.58      inference('demod', [status(thm)], ['53', '54'])).
% 0.39/0.58  thf('56', plain, ($false),
% 0.39/0.58      inference('simplify_reflect-', [status(thm)], ['48', '55'])).
% 0.39/0.58  
% 0.39/0.58  % SZS output end Refutation
% 0.39/0.58  
% 0.42/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
