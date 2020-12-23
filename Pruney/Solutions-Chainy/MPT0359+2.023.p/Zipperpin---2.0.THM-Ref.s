%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.kjc3M4vj91

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:34 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 204 expanded)
%              Number of leaves         :   22 (  63 expanded)
%              Depth                    :   14
%              Number of atoms          :  603 (1777 expanded)
%              Number of equality atoms :   58 ( 180 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(t39_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ B )
      <=> ( B
          = ( k2_subset_1 @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ B )
        <=> ( B
            = ( k2_subset_1 @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t39_subset_1])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('1',plain,(
    ! [X45: $i,X46: $i] :
      ( ( ( k3_subset_1 @ X46 @ ( k3_subset_1 @ X46 @ X45 ) )
        = X45 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ X46 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('2',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['0','1'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('3',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('4',plain,
    ( ( sk_B
      = ( k2_subset_1 @ sk_A ) )
    | ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(split,[status(esa)],['4'])).

thf('6',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('7',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ X0 @ sk_B )
        | ~ ( r2_hidden @ X0 @ ( k3_subset_1 @ sk_A @ sk_B ) ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ X0 )
        | ( r2_hidden @ ( sk_C @ X0 @ ( k3_subset_1 @ sk_A @ sk_B ) ) @ sk_B ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['3','7'])).

thf('9',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('10',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('11',plain,(
    ! [X42: $i,X43: $i] :
      ( ( ( k3_subset_1 @ X42 @ X43 )
        = ( k4_xboole_0 @ X42 @ X43 ) )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('12',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('13',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X16 @ X15 )
      | ~ ( r2_hidden @ X16 @ X14 )
      | ( X15
       != ( k4_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('14',plain,(
    ! [X13: $i,X14: $i,X16: $i] :
      ( ~ ( r2_hidden @ X16 @ X14 )
      | ~ ( r2_hidden @ X16 @ ( k4_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k3_subset_1 @ sk_A @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ X0 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ ( k3_subset_1 @ sk_A @ sk_B ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['9','15'])).

thf('17',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ X0 )
        | ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ X0 ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['8','16'])).

thf('18',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ X0 )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(simplify,[status(thm)],['17'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('19',plain,(
    ! [X26: $i] :
      ( r1_tarski @ k1_xboole_0 @ X26 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('20',plain,(
    ! [X18: $i,X20: $i] :
      ( ( X18 = X20 )
      | ~ ( r1_tarski @ X20 @ X18 )
      | ~ ( r1_tarski @ X18 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( ( k3_subset_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,
    ( ( sk_B
     != ( k2_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( sk_B
     != ( k2_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(split,[status(esa)],['23'])).

thf('25',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('26',plain,(
    ! [X41: $i] :
      ( ( k2_subset_1 @ X41 )
      = X41 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('27',plain,
    ( ( sk_B
      = ( k2_subset_1 @ sk_A ) )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['4'])).

thf('28',plain,
    ( ( sk_B = sk_A )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ sk_A ) )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X42: $i,X43: $i] :
      ( ( ( k3_subset_1 @ X42 @ X43 )
        = ( k4_xboole_0 @ X42 @ X43 ) )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('32',plain,
    ( ( ( k3_subset_1 @ sk_A @ sk_A )
      = ( k4_xboole_0 @ sk_A @ sk_A ) )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X16 @ X15 )
      | ( r2_hidden @ X16 @ X13 )
      | ( X15
       != ( k4_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('34',plain,(
    ! [X13: $i,X14: $i,X16: $i] :
      ( ( r2_hidden @ X16 @ X13 )
      | ~ ( r2_hidden @ X16 @ ( k4_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( k3_subset_1 @ sk_A @ sk_A ) )
        | ( r2_hidden @ X0 @ sk_A ) )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['32','34'])).

thf('36',plain,
    ( ( ( k3_subset_1 @ sk_A @ sk_A )
      = ( k4_xboole_0 @ sk_A @ sk_A ) )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('37',plain,(
    ! [X13: $i,X14: $i,X16: $i] :
      ( ~ ( r2_hidden @ X16 @ X14 )
      | ~ ( r2_hidden @ X16 @ ( k4_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('38',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( k3_subset_1 @ sk_A @ sk_A ) )
        | ~ ( r2_hidden @ X0 @ sk_A ) )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ ( k3_subset_1 @ sk_A @ sk_A ) )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['35','38'])).

thf('40',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_A ) @ X0 )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['25','39'])).

thf('41',plain,
    ( ( sk_B = sk_A )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('42',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
   <= ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(split,[status(esa)],['23'])).

thf('43',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_A )
   <= ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
      & ( sk_B
        = ( k2_subset_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( sk_B = sk_A )
   <= ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('45',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_A ) @ sk_A )
   <= ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
      & ( sk_B
        = ( k2_subset_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
    | ( sk_B
     != ( k2_subset_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['40','45'])).

thf('47',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B )
    | ( sk_B
      = ( k2_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['4'])).

thf('48',plain,(
    r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_B ),
    inference('sat_resolution*',[status(thm)],['24','46','47'])).

thf('49',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['22','48'])).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('50',plain,(
    ! [X40: $i] :
      ( ( k1_subset_1 @ X40 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf(t22_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ) )).

thf('51',plain,(
    ! [X47: $i] :
      ( ( k2_subset_1 @ X47 )
      = ( k3_subset_1 @ X47 @ ( k1_subset_1 @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[t22_subset_1])).

thf('52',plain,(
    ! [X41: $i] :
      ( ( k2_subset_1 @ X41 )
      = X41 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('53',plain,(
    ! [X47: $i] :
      ( X47
      = ( k3_subset_1 @ X47 @ ( k1_subset_1 @ X47 ) ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_subset_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['50','53'])).

thf('55',plain,(
    sk_A = sk_B ),
    inference(demod,[status(thm)],['2','49','54'])).

thf('56',plain,
    ( ( sk_B
     != ( k2_subset_1 @ sk_A ) )
   <= ( sk_B
     != ( k2_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['23'])).

thf('57',plain,(
    ! [X41: $i] :
      ( ( k2_subset_1 @ X41 )
      = X41 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('58',plain,
    ( ( sk_B != sk_A )
   <= ( sk_B
     != ( k2_subset_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    sk_B
 != ( k2_subset_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['24','46'])).

thf('60',plain,(
    sk_B != sk_A ),
    inference(simpl_trail,[status(thm)],['58','59'])).

thf('61',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['55','60'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.kjc3M4vj91
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:48:59 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.20/0.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.56  % Solved by: fo/fo7.sh
% 0.20/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.56  % done 410 iterations in 0.111s
% 0.20/0.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.56  % SZS output start Refutation
% 0.20/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.56  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 0.20/0.56  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.20/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.56  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.56  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.20/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.56  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.56  thf(t39_subset_1, conjecture,
% 0.20/0.56    (![A:$i,B:$i]:
% 0.20/0.56     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.56       ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ B ) <=>
% 0.20/0.56         ( ( B ) = ( k2_subset_1 @ A ) ) ) ))).
% 0.20/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.56    (~( ![A:$i,B:$i]:
% 0.20/0.56        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.56          ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ B ) <=>
% 0.20/0.56            ( ( B ) = ( k2_subset_1 @ A ) ) ) ) )),
% 0.20/0.56    inference('cnf.neg', [status(esa)], [t39_subset_1])).
% 0.20/0.56  thf('0', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf(involutiveness_k3_subset_1, axiom,
% 0.20/0.56    (![A:$i,B:$i]:
% 0.20/0.56     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.56       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.20/0.56  thf('1', plain,
% 0.20/0.56      (![X45 : $i, X46 : $i]:
% 0.20/0.56         (((k3_subset_1 @ X46 @ (k3_subset_1 @ X46 @ X45)) = (X45))
% 0.20/0.56          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ X46)))),
% 0.20/0.56      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.20/0.56  thf('2', plain,
% 0.20/0.56      (((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)) = (sk_B))),
% 0.20/0.56      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.56  thf(d3_tarski, axiom,
% 0.20/0.56    (![A:$i,B:$i]:
% 0.20/0.56     ( ( r1_tarski @ A @ B ) <=>
% 0.20/0.56       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.20/0.56  thf('3', plain,
% 0.20/0.56      (![X3 : $i, X5 : $i]:
% 0.20/0.56         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.20/0.56      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.56  thf('4', plain,
% 0.20/0.56      ((((sk_B) = (k2_subset_1 @ sk_A))
% 0.20/0.56        | (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('5', plain,
% 0.20/0.56      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))
% 0.20/0.56         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.20/0.56      inference('split', [status(esa)], ['4'])).
% 0.20/0.56  thf('6', plain,
% 0.20/0.56      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.56         (~ (r2_hidden @ X2 @ X3)
% 0.20/0.56          | (r2_hidden @ X2 @ X4)
% 0.20/0.56          | ~ (r1_tarski @ X3 @ X4))),
% 0.20/0.56      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.56  thf('7', plain,
% 0.20/0.56      ((![X0 : $i]:
% 0.20/0.56          ((r2_hidden @ X0 @ sk_B)
% 0.20/0.56           | ~ (r2_hidden @ X0 @ (k3_subset_1 @ sk_A @ sk_B))))
% 0.20/0.56         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.56  thf('8', plain,
% 0.20/0.56      ((![X0 : $i]:
% 0.20/0.56          ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ X0)
% 0.20/0.56           | (r2_hidden @ (sk_C @ X0 @ (k3_subset_1 @ sk_A @ sk_B)) @ sk_B)))
% 0.20/0.56         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['3', '7'])).
% 0.20/0.56  thf('9', plain,
% 0.20/0.56      (![X3 : $i, X5 : $i]:
% 0.20/0.56         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.20/0.56      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.56  thf('10', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf(d5_subset_1, axiom,
% 0.20/0.56    (![A:$i,B:$i]:
% 0.20/0.56     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.56       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.20/0.56  thf('11', plain,
% 0.20/0.56      (![X42 : $i, X43 : $i]:
% 0.20/0.56         (((k3_subset_1 @ X42 @ X43) = (k4_xboole_0 @ X42 @ X43))
% 0.20/0.56          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ X42)))),
% 0.20/0.56      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.20/0.56  thf('12', plain,
% 0.20/0.56      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.20/0.56      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.56  thf(d5_xboole_0, axiom,
% 0.20/0.56    (![A:$i,B:$i,C:$i]:
% 0.20/0.56     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.20/0.56       ( ![D:$i]:
% 0.20/0.56         ( ( r2_hidden @ D @ C ) <=>
% 0.20/0.56           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.20/0.56  thf('13', plain,
% 0.20/0.56      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.20/0.56         (~ (r2_hidden @ X16 @ X15)
% 0.20/0.56          | ~ (r2_hidden @ X16 @ X14)
% 0.20/0.56          | ((X15) != (k4_xboole_0 @ X13 @ X14)))),
% 0.20/0.56      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.20/0.56  thf('14', plain,
% 0.20/0.56      (![X13 : $i, X14 : $i, X16 : $i]:
% 0.20/0.56         (~ (r2_hidden @ X16 @ X14)
% 0.20/0.56          | ~ (r2_hidden @ X16 @ (k4_xboole_0 @ X13 @ X14)))),
% 0.20/0.56      inference('simplify', [status(thm)], ['13'])).
% 0.20/0.56  thf('15', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         (~ (r2_hidden @ X0 @ (k3_subset_1 @ sk_A @ sk_B))
% 0.20/0.56          | ~ (r2_hidden @ X0 @ sk_B))),
% 0.20/0.56      inference('sup-', [status(thm)], ['12', '14'])).
% 0.20/0.56  thf('16', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ X0)
% 0.20/0.56          | ~ (r2_hidden @ (sk_C @ X0 @ (k3_subset_1 @ sk_A @ sk_B)) @ sk_B))),
% 0.20/0.56      inference('sup-', [status(thm)], ['9', '15'])).
% 0.20/0.56  thf('17', plain,
% 0.20/0.56      ((![X0 : $i]:
% 0.20/0.56          ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ X0)
% 0.20/0.56           | (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ X0)))
% 0.20/0.56         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['8', '16'])).
% 0.20/0.56  thf('18', plain,
% 0.20/0.56      ((![X0 : $i]: (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ X0))
% 0.20/0.56         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.20/0.56      inference('simplify', [status(thm)], ['17'])).
% 0.20/0.56  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.20/0.56  thf('19', plain, (![X26 : $i]: (r1_tarski @ k1_xboole_0 @ X26)),
% 0.20/0.56      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.20/0.56  thf(d10_xboole_0, axiom,
% 0.20/0.56    (![A:$i,B:$i]:
% 0.20/0.56     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.56  thf('20', plain,
% 0.20/0.56      (![X18 : $i, X20 : $i]:
% 0.20/0.56         (((X18) = (X20))
% 0.20/0.56          | ~ (r1_tarski @ X20 @ X18)
% 0.20/0.56          | ~ (r1_tarski @ X18 @ X20))),
% 0.20/0.56      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.56  thf('21', plain,
% 0.20/0.56      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['19', '20'])).
% 0.20/0.56  thf('22', plain,
% 0.20/0.56      ((((k3_subset_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.20/0.56         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['18', '21'])).
% 0.20/0.56  thf('23', plain,
% 0.20/0.56      ((((sk_B) != (k2_subset_1 @ sk_A))
% 0.20/0.56        | ~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('24', plain,
% 0.20/0.56      (~ (((sk_B) = (k2_subset_1 @ sk_A))) | 
% 0.20/0.56       ~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))),
% 0.20/0.56      inference('split', [status(esa)], ['23'])).
% 0.20/0.56  thf('25', plain,
% 0.20/0.56      (![X3 : $i, X5 : $i]:
% 0.20/0.56         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.20/0.56      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.56  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.20/0.56  thf('26', plain, (![X41 : $i]: ((k2_subset_1 @ X41) = (X41))),
% 0.20/0.56      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.20/0.56  thf('27', plain,
% 0.20/0.56      ((((sk_B) = (k2_subset_1 @ sk_A))) <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.20/0.56      inference('split', [status(esa)], ['4'])).
% 0.20/0.56  thf('28', plain,
% 0.20/0.56      ((((sk_B) = (sk_A))) <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.20/0.56      inference('sup+', [status(thm)], ['26', '27'])).
% 0.20/0.56  thf('29', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('30', plain,
% 0.20/0.56      (((m1_subset_1 @ sk_A @ (k1_zfmisc_1 @ sk_A)))
% 0.20/0.56         <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.20/0.56      inference('sup+', [status(thm)], ['28', '29'])).
% 0.20/0.56  thf('31', plain,
% 0.20/0.56      (![X42 : $i, X43 : $i]:
% 0.20/0.56         (((k3_subset_1 @ X42 @ X43) = (k4_xboole_0 @ X42 @ X43))
% 0.20/0.56          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ X42)))),
% 0.20/0.56      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.20/0.56  thf('32', plain,
% 0.20/0.56      ((((k3_subset_1 @ sk_A @ sk_A) = (k4_xboole_0 @ sk_A @ sk_A)))
% 0.20/0.56         <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.20/0.56      inference('sup-', [status(thm)], ['30', '31'])).
% 0.20/0.56  thf('33', plain,
% 0.20/0.56      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.20/0.56         (~ (r2_hidden @ X16 @ X15)
% 0.20/0.56          | (r2_hidden @ X16 @ X13)
% 0.20/0.56          | ((X15) != (k4_xboole_0 @ X13 @ X14)))),
% 0.20/0.56      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.20/0.56  thf('34', plain,
% 0.20/0.56      (![X13 : $i, X14 : $i, X16 : $i]:
% 0.20/0.56         ((r2_hidden @ X16 @ X13)
% 0.20/0.56          | ~ (r2_hidden @ X16 @ (k4_xboole_0 @ X13 @ X14)))),
% 0.20/0.56      inference('simplify', [status(thm)], ['33'])).
% 0.20/0.56  thf('35', plain,
% 0.20/0.56      ((![X0 : $i]:
% 0.20/0.56          (~ (r2_hidden @ X0 @ (k3_subset_1 @ sk_A @ sk_A))
% 0.20/0.56           | (r2_hidden @ X0 @ sk_A)))
% 0.20/0.56         <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.20/0.56      inference('sup-', [status(thm)], ['32', '34'])).
% 0.20/0.56  thf('36', plain,
% 0.20/0.56      ((((k3_subset_1 @ sk_A @ sk_A) = (k4_xboole_0 @ sk_A @ sk_A)))
% 0.20/0.56         <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.20/0.56      inference('sup-', [status(thm)], ['30', '31'])).
% 0.20/0.56  thf('37', plain,
% 0.20/0.56      (![X13 : $i, X14 : $i, X16 : $i]:
% 0.20/0.56         (~ (r2_hidden @ X16 @ X14)
% 0.20/0.56          | ~ (r2_hidden @ X16 @ (k4_xboole_0 @ X13 @ X14)))),
% 0.20/0.56      inference('simplify', [status(thm)], ['13'])).
% 0.20/0.56  thf('38', plain,
% 0.20/0.56      ((![X0 : $i]:
% 0.20/0.56          (~ (r2_hidden @ X0 @ (k3_subset_1 @ sk_A @ sk_A))
% 0.20/0.56           | ~ (r2_hidden @ X0 @ sk_A)))
% 0.20/0.56         <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.20/0.56      inference('sup-', [status(thm)], ['36', '37'])).
% 0.20/0.56  thf('39', plain,
% 0.20/0.56      ((![X0 : $i]: ~ (r2_hidden @ X0 @ (k3_subset_1 @ sk_A @ sk_A)))
% 0.20/0.56         <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.20/0.56      inference('clc', [status(thm)], ['35', '38'])).
% 0.20/0.56  thf('40', plain,
% 0.20/0.56      ((![X0 : $i]: (r1_tarski @ (k3_subset_1 @ sk_A @ sk_A) @ X0))
% 0.20/0.56         <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.20/0.56      inference('sup-', [status(thm)], ['25', '39'])).
% 0.20/0.56  thf('41', plain,
% 0.20/0.56      ((((sk_B) = (sk_A))) <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.20/0.56      inference('sup+', [status(thm)], ['26', '27'])).
% 0.20/0.56  thf('42', plain,
% 0.20/0.56      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))
% 0.20/0.56         <= (~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.20/0.56      inference('split', [status(esa)], ['23'])).
% 0.20/0.56  thf('43', plain,
% 0.20/0.56      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_A))
% 0.20/0.56         <= (~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)) & 
% 0.20/0.56             (((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.20/0.56      inference('sup-', [status(thm)], ['41', '42'])).
% 0.20/0.56  thf('44', plain,
% 0.20/0.56      ((((sk_B) = (sk_A))) <= ((((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.20/0.56      inference('sup+', [status(thm)], ['26', '27'])).
% 0.20/0.56  thf('45', plain,
% 0.20/0.56      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_A) @ sk_A))
% 0.20/0.56         <= (~ ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)) & 
% 0.20/0.56             (((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.20/0.56      inference('demod', [status(thm)], ['43', '44'])).
% 0.20/0.56  thf('46', plain,
% 0.20/0.56      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)) | 
% 0.20/0.56       ~ (((sk_B) = (k2_subset_1 @ sk_A)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['40', '45'])).
% 0.20/0.56  thf('47', plain,
% 0.20/0.56      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B)) | 
% 0.20/0.56       (((sk_B) = (k2_subset_1 @ sk_A)))),
% 0.20/0.56      inference('split', [status(esa)], ['4'])).
% 0.20/0.56  thf('48', plain, (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_B))),
% 0.20/0.56      inference('sat_resolution*', [status(thm)], ['24', '46', '47'])).
% 0.20/0.56  thf('49', plain, (((k3_subset_1 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.20/0.56      inference('simpl_trail', [status(thm)], ['22', '48'])).
% 0.20/0.56  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 0.20/0.56  thf('50', plain, (![X40 : $i]: ((k1_subset_1 @ X40) = (k1_xboole_0))),
% 0.20/0.56      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.20/0.56  thf(t22_subset_1, axiom,
% 0.20/0.56    (![A:$i]:
% 0.20/0.56     ( ( k2_subset_1 @ A ) = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ))).
% 0.20/0.56  thf('51', plain,
% 0.20/0.56      (![X47 : $i]:
% 0.20/0.56         ((k2_subset_1 @ X47) = (k3_subset_1 @ X47 @ (k1_subset_1 @ X47)))),
% 0.20/0.56      inference('cnf', [status(esa)], [t22_subset_1])).
% 0.20/0.56  thf('52', plain, (![X41 : $i]: ((k2_subset_1 @ X41) = (X41))),
% 0.20/0.56      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.20/0.56  thf('53', plain,
% 0.20/0.56      (![X47 : $i]: ((X47) = (k3_subset_1 @ X47 @ (k1_subset_1 @ X47)))),
% 0.20/0.56      inference('demod', [status(thm)], ['51', '52'])).
% 0.20/0.56  thf('54', plain, (![X0 : $i]: ((X0) = (k3_subset_1 @ X0 @ k1_xboole_0))),
% 0.20/0.56      inference('sup+', [status(thm)], ['50', '53'])).
% 0.20/0.56  thf('55', plain, (((sk_A) = (sk_B))),
% 0.20/0.56      inference('demod', [status(thm)], ['2', '49', '54'])).
% 0.20/0.56  thf('56', plain,
% 0.20/0.56      ((((sk_B) != (k2_subset_1 @ sk_A)))
% 0.20/0.56         <= (~ (((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.20/0.56      inference('split', [status(esa)], ['23'])).
% 0.20/0.56  thf('57', plain, (![X41 : $i]: ((k2_subset_1 @ X41) = (X41))),
% 0.20/0.56      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.20/0.56  thf('58', plain,
% 0.20/0.56      ((((sk_B) != (sk_A))) <= (~ (((sk_B) = (k2_subset_1 @ sk_A))))),
% 0.20/0.56      inference('demod', [status(thm)], ['56', '57'])).
% 0.20/0.56  thf('59', plain, (~ (((sk_B) = (k2_subset_1 @ sk_A)))),
% 0.20/0.56      inference('sat_resolution*', [status(thm)], ['24', '46'])).
% 0.20/0.56  thf('60', plain, (((sk_B) != (sk_A))),
% 0.20/0.56      inference('simpl_trail', [status(thm)], ['58', '59'])).
% 0.20/0.56  thf('61', plain, ($false),
% 0.20/0.56      inference('simplify_reflect-', [status(thm)], ['55', '60'])).
% 0.20/0.56  
% 0.20/0.56  % SZS output end Refutation
% 0.20/0.56  
% 0.20/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
