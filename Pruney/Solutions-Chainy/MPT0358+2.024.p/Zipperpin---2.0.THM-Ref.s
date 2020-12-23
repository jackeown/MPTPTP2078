%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.O5PY6Nw9Ha

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:25 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 227 expanded)
%              Number of leaves         :   26 (  72 expanded)
%              Depth                    :   14
%              Number of atoms          :  582 (1822 expanded)
%              Number of equality atoms :   66 ( 195 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t38_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) )
      <=> ( B
          = ( k1_subset_1 @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) )
        <=> ( B
            = ( k1_subset_1 @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t38_subset_1])).

thf('0',plain,
    ( ( sk_B
      = ( k1_subset_1 @ sk_A ) )
    | ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('2',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k3_xboole_0 @ X7 @ X8 )
        = X7 )
      | ~ ( r1_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('3',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,
    ( ( sk_B
     != ( k1_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( sk_B
     != ( k1_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['4'])).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('6',plain,(
    ! [X21: $i] :
      ( ( k1_subset_1 @ X21 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('7',plain,
    ( ( sk_B
      = ( k1_subset_1 @ sk_A ) )
   <= ( sk_B
      = ( k1_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('8',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
      = ( k1_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
   <= ( sk_B
      = ( k1_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('11',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k3_subset_1 @ X22 @ X23 )
        = ( k4_xboole_0 @ X22 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('12',plain,
    ( ( ( k3_subset_1 @ sk_A @ k1_xboole_0 )
      = ( k4_xboole_0 @ sk_A @ k1_xboole_0 ) )
   <= ( sk_B
      = ( k1_subset_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('13',plain,(
    ! [X10: $i] :
      ( ( k4_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('14',plain,
    ( ( ( k3_subset_1 @ sk_A @ k1_xboole_0 )
      = sk_A )
   <= ( sk_B
      = ( k1_subset_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
      = ( k1_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('16',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
   <= ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['4'])).

thf('17',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ k1_xboole_0 ) )
   <= ( ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
      & ( sk_B
        = ( k1_subset_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
      = ( k1_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('19',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ ( k3_subset_1 @ sk_A @ k1_xboole_0 ) )
   <= ( ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
      & ( sk_B
        = ( k1_subset_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ sk_A )
   <= ( ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
      & ( sk_B
        = ( k1_subset_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['14','19'])).

thf('21',plain,
    ( ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
   <= ( sk_B
      = ( k1_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('22',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ X19 )
      | ( r2_hidden @ X18 @ X19 )
      | ( v1_xboole_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('23',plain,
    ( ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ( r2_hidden @ k1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) ) )
   <= ( sk_B
      = ( k1_subset_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('24',plain,(
    ! [X24: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('25',plain,
    ( ( r2_hidden @ k1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
   <= ( sk_B
      = ( k1_subset_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['23','24'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('26',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X16 @ X15 )
      | ( r1_tarski @ X16 @ X14 )
      | ( X15
       != ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('27',plain,(
    ! [X14: $i,X16: $i] :
      ( ( r1_tarski @ X16 @ X14 )
      | ~ ( r2_hidden @ X16 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,
    ( ( r1_tarski @ k1_xboole_0 @ sk_A )
   <= ( sk_B
      = ( k1_subset_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['25','27'])).

thf('29',plain,
    ( ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ( sk_B
     != ( k1_subset_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['20','28'])).

thf('30',plain,
    ( ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ( sk_B
      = ( k1_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('31',plain,(
    r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['5','29','30'])).

thf('32',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference(simpl_trail,[status(thm)],['3','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k3_subset_1 @ X22 @ X23 )
        = ( k4_xboole_0 @ X22 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('35',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ X19 )
      | ( r2_hidden @ X18 @ X19 )
      | ( v1_xboole_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('38',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X24: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('40',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X14: $i,X16: $i] :
      ( ( r1_tarski @ X16 @ X14 )
      | ~ ( r2_hidden @ X16 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('42',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k3_xboole_0 @ X7 @ X8 )
        = X7 )
      | ~ ( r1_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('44',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['42','43'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('46',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['44','45'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('47',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('48',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['35','48'])).

thf('50',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['32','49'])).

thf('51',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('52',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X11 @ X12 ) @ X12 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('53',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_A @ sk_B ) )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['51','56'])).

thf('58',plain,(
    sk_B = k1_xboole_0 ),
    inference('sup+',[status(thm)],['50','57'])).

thf('59',plain,(
    ! [X21: $i] :
      ( ( k1_subset_1 @ X21 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('60',plain,
    ( ( sk_B
     != ( k1_subset_1 @ sk_A ) )
   <= ( sk_B
     != ( k1_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['4'])).

thf('61',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B
     != ( k1_subset_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    sk_B
 != ( k1_subset_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['5','29'])).

thf('63',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['61','62'])).

thf('64',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['58','63'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.O5PY6Nw9Ha
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:06:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.55  % Solved by: fo/fo7.sh
% 0.21/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.55  % done 330 iterations in 0.097s
% 0.21/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.55  % SZS output start Refutation
% 0.21/0.55  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.55  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.55  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 0.21/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.55  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.55  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.55  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.21/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.55  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.21/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.55  thf(t38_subset_1, conjecture,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.55       ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) ) <=>
% 0.21/0.55         ( ( B ) = ( k1_subset_1 @ A ) ) ) ))).
% 0.21/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.55    (~( ![A:$i,B:$i]:
% 0.21/0.55        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.55          ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) ) <=>
% 0.21/0.55            ( ( B ) = ( k1_subset_1 @ A ) ) ) ) )),
% 0.21/0.55    inference('cnf.neg', [status(esa)], [t38_subset_1])).
% 0.21/0.55  thf('0', plain,
% 0.21/0.55      ((((sk_B) = (k1_subset_1 @ sk_A))
% 0.21/0.55        | (r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('1', plain,
% 0.21/0.55      (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))
% 0.21/0.55         <= (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))))),
% 0.21/0.55      inference('split', [status(esa)], ['0'])).
% 0.21/0.55  thf(t28_xboole_1, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.21/0.55  thf('2', plain,
% 0.21/0.55      (![X7 : $i, X8 : $i]:
% 0.21/0.55         (((k3_xboole_0 @ X7 @ X8) = (X7)) | ~ (r1_tarski @ X7 @ X8))),
% 0.21/0.55      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.21/0.55  thf('3', plain,
% 0.21/0.55      ((((k3_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)) = (sk_B)))
% 0.21/0.55         <= (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))))),
% 0.21/0.55      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.55  thf('4', plain,
% 0.21/0.55      ((((sk_B) != (k1_subset_1 @ sk_A))
% 0.21/0.55        | ~ (r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('5', plain,
% 0.21/0.55      (~ (((sk_B) = (k1_subset_1 @ sk_A))) | 
% 0.21/0.55       ~ ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.21/0.55      inference('split', [status(esa)], ['4'])).
% 0.21/0.55  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 0.21/0.55  thf('6', plain, (![X21 : $i]: ((k1_subset_1 @ X21) = (k1_xboole_0))),
% 0.21/0.55      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.21/0.55  thf('7', plain,
% 0.21/0.55      ((((sk_B) = (k1_subset_1 @ sk_A))) <= ((((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.21/0.55      inference('split', [status(esa)], ['0'])).
% 0.21/0.55  thf('8', plain,
% 0.21/0.55      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.21/0.55      inference('sup+', [status(thm)], ['6', '7'])).
% 0.21/0.55  thf('9', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('10', plain,
% 0.21/0.55      (((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ sk_A)))
% 0.21/0.55         <= ((((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.21/0.55      inference('sup+', [status(thm)], ['8', '9'])).
% 0.21/0.55  thf(d5_subset_1, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.55       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.21/0.55  thf('11', plain,
% 0.21/0.55      (![X22 : $i, X23 : $i]:
% 0.21/0.55         (((k3_subset_1 @ X22 @ X23) = (k4_xboole_0 @ X22 @ X23))
% 0.21/0.55          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X22)))),
% 0.21/0.55      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.21/0.55  thf('12', plain,
% 0.21/0.55      ((((k3_subset_1 @ sk_A @ k1_xboole_0)
% 0.21/0.55          = (k4_xboole_0 @ sk_A @ k1_xboole_0)))
% 0.21/0.55         <= ((((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.21/0.55      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.55  thf(t3_boole, axiom,
% 0.21/0.55    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.21/0.55  thf('13', plain, (![X10 : $i]: ((k4_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 0.21/0.55      inference('cnf', [status(esa)], [t3_boole])).
% 0.21/0.55  thf('14', plain,
% 0.21/0.55      ((((k3_subset_1 @ sk_A @ k1_xboole_0) = (sk_A)))
% 0.21/0.55         <= ((((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.21/0.55      inference('demod', [status(thm)], ['12', '13'])).
% 0.21/0.55  thf('15', plain,
% 0.21/0.55      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.21/0.55      inference('sup+', [status(thm)], ['6', '7'])).
% 0.21/0.55  thf('16', plain,
% 0.21/0.55      ((~ (r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))
% 0.21/0.55         <= (~ ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))))),
% 0.21/0.55      inference('split', [status(esa)], ['4'])).
% 0.21/0.55  thf('17', plain,
% 0.21/0.55      ((~ (r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ k1_xboole_0)))
% 0.21/0.55         <= (~ ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))) & 
% 0.21/0.55             (((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.21/0.55      inference('sup-', [status(thm)], ['15', '16'])).
% 0.21/0.55  thf('18', plain,
% 0.21/0.55      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.21/0.55      inference('sup+', [status(thm)], ['6', '7'])).
% 0.21/0.55  thf('19', plain,
% 0.21/0.55      ((~ (r1_tarski @ k1_xboole_0 @ (k3_subset_1 @ sk_A @ k1_xboole_0)))
% 0.21/0.55         <= (~ ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))) & 
% 0.21/0.55             (((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.21/0.55      inference('demod', [status(thm)], ['17', '18'])).
% 0.21/0.55  thf('20', plain,
% 0.21/0.55      ((~ (r1_tarski @ k1_xboole_0 @ sk_A))
% 0.21/0.55         <= (~ ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))) & 
% 0.21/0.55             (((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.21/0.55      inference('sup-', [status(thm)], ['14', '19'])).
% 0.21/0.55  thf('21', plain,
% 0.21/0.55      (((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ sk_A)))
% 0.21/0.55         <= ((((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.21/0.55      inference('sup+', [status(thm)], ['8', '9'])).
% 0.21/0.55  thf(d2_subset_1, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( ( v1_xboole_0 @ A ) =>
% 0.21/0.55         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.21/0.55       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.55         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.21/0.55  thf('22', plain,
% 0.21/0.55      (![X18 : $i, X19 : $i]:
% 0.21/0.55         (~ (m1_subset_1 @ X18 @ X19)
% 0.21/0.55          | (r2_hidden @ X18 @ X19)
% 0.21/0.55          | (v1_xboole_0 @ X19))),
% 0.21/0.55      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.21/0.55  thf('23', plain,
% 0.21/0.55      ((((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.21/0.55         | (r2_hidden @ k1_xboole_0 @ (k1_zfmisc_1 @ sk_A))))
% 0.21/0.55         <= ((((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.21/0.55      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.55  thf(fc1_subset_1, axiom,
% 0.21/0.55    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.21/0.55  thf('24', plain, (![X24 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X24))),
% 0.21/0.55      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.21/0.55  thf('25', plain,
% 0.21/0.55      (((r2_hidden @ k1_xboole_0 @ (k1_zfmisc_1 @ sk_A)))
% 0.21/0.55         <= ((((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.21/0.55      inference('clc', [status(thm)], ['23', '24'])).
% 0.21/0.55  thf(d1_zfmisc_1, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.21/0.55       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.21/0.55  thf('26', plain,
% 0.21/0.55      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.21/0.55         (~ (r2_hidden @ X16 @ X15)
% 0.21/0.55          | (r1_tarski @ X16 @ X14)
% 0.21/0.55          | ((X15) != (k1_zfmisc_1 @ X14)))),
% 0.21/0.55      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.21/0.55  thf('27', plain,
% 0.21/0.55      (![X14 : $i, X16 : $i]:
% 0.21/0.55         ((r1_tarski @ X16 @ X14) | ~ (r2_hidden @ X16 @ (k1_zfmisc_1 @ X14)))),
% 0.21/0.55      inference('simplify', [status(thm)], ['26'])).
% 0.21/0.55  thf('28', plain,
% 0.21/0.55      (((r1_tarski @ k1_xboole_0 @ sk_A))
% 0.21/0.55         <= ((((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.21/0.55      inference('sup-', [status(thm)], ['25', '27'])).
% 0.21/0.55  thf('29', plain,
% 0.21/0.55      (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))) | 
% 0.21/0.55       ~ (((sk_B) = (k1_subset_1 @ sk_A)))),
% 0.21/0.55      inference('demod', [status(thm)], ['20', '28'])).
% 0.21/0.55  thf('30', plain,
% 0.21/0.55      (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))) | 
% 0.21/0.55       (((sk_B) = (k1_subset_1 @ sk_A)))),
% 0.21/0.55      inference('split', [status(esa)], ['0'])).
% 0.21/0.55  thf('31', plain, (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.21/0.55      inference('sat_resolution*', [status(thm)], ['5', '29', '30'])).
% 0.21/0.55  thf('32', plain,
% 0.21/0.55      (((k3_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)) = (sk_B))),
% 0.21/0.55      inference('simpl_trail', [status(thm)], ['3', '31'])).
% 0.21/0.55  thf('33', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('34', plain,
% 0.21/0.55      (![X22 : $i, X23 : $i]:
% 0.21/0.55         (((k3_subset_1 @ X22 @ X23) = (k4_xboole_0 @ X22 @ X23))
% 0.21/0.55          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X22)))),
% 0.21/0.55      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.21/0.55  thf('35', plain,
% 0.21/0.55      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.21/0.55      inference('sup-', [status(thm)], ['33', '34'])).
% 0.21/0.55  thf('36', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('37', plain,
% 0.21/0.55      (![X18 : $i, X19 : $i]:
% 0.21/0.55         (~ (m1_subset_1 @ X18 @ X19)
% 0.21/0.55          | (r2_hidden @ X18 @ X19)
% 0.21/0.55          | (v1_xboole_0 @ X19))),
% 0.21/0.55      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.21/0.55  thf('38', plain,
% 0.21/0.55      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.21/0.55        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['36', '37'])).
% 0.21/0.55  thf('39', plain, (![X24 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X24))),
% 0.21/0.55      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.21/0.55  thf('40', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.55      inference('clc', [status(thm)], ['38', '39'])).
% 0.21/0.55  thf('41', plain,
% 0.21/0.55      (![X14 : $i, X16 : $i]:
% 0.21/0.55         ((r1_tarski @ X16 @ X14) | ~ (r2_hidden @ X16 @ (k1_zfmisc_1 @ X14)))),
% 0.21/0.55      inference('simplify', [status(thm)], ['26'])).
% 0.21/0.55  thf('42', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.21/0.55      inference('sup-', [status(thm)], ['40', '41'])).
% 0.21/0.55  thf('43', plain,
% 0.21/0.55      (![X7 : $i, X8 : $i]:
% 0.21/0.55         (((k3_xboole_0 @ X7 @ X8) = (X7)) | ~ (r1_tarski @ X7 @ X8))),
% 0.21/0.55      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.21/0.55  thf('44', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 0.21/0.55      inference('sup-', [status(thm)], ['42', '43'])).
% 0.21/0.55  thf(commutativity_k3_xboole_0, axiom,
% 0.21/0.55    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.21/0.55  thf('45', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.21/0.55      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.21/0.55  thf('46', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (sk_B))),
% 0.21/0.55      inference('demod', [status(thm)], ['44', '45'])).
% 0.21/0.55  thf(t100_xboole_1, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.21/0.55  thf('47', plain,
% 0.21/0.55      (![X5 : $i, X6 : $i]:
% 0.21/0.55         ((k4_xboole_0 @ X5 @ X6)
% 0.21/0.55           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.21/0.55      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.21/0.55  thf('48', plain,
% 0.21/0.55      (((k4_xboole_0 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 0.21/0.55      inference('sup+', [status(thm)], ['46', '47'])).
% 0.21/0.55  thf('49', plain,
% 0.21/0.55      (((k3_subset_1 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 0.21/0.55      inference('sup+', [status(thm)], ['35', '48'])).
% 0.21/0.55  thf('50', plain,
% 0.21/0.55      (((k3_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_A @ sk_B)) = (sk_B))),
% 0.21/0.55      inference('demod', [status(thm)], ['32', '49'])).
% 0.21/0.55  thf('51', plain,
% 0.21/0.55      (((k4_xboole_0 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 0.21/0.55      inference('sup+', [status(thm)], ['46', '47'])).
% 0.21/0.55  thf(t79_xboole_1, axiom,
% 0.21/0.55    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.21/0.55  thf('52', plain,
% 0.21/0.55      (![X11 : $i, X12 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X11 @ X12) @ X12)),
% 0.21/0.55      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.21/0.55  thf(d7_xboole_0, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.21/0.55       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.21/0.55  thf('53', plain,
% 0.21/0.55      (![X2 : $i, X3 : $i]:
% 0.21/0.55         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.21/0.55      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.21/0.55  thf('54', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0) = (k1_xboole_0))),
% 0.21/0.55      inference('sup-', [status(thm)], ['52', '53'])).
% 0.21/0.55  thf('55', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.21/0.55      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.21/0.55  thf('56', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.21/0.55      inference('demod', [status(thm)], ['54', '55'])).
% 0.21/0.55  thf('57', plain,
% 0.21/0.55      (((k3_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_A @ sk_B)) = (k1_xboole_0))),
% 0.21/0.55      inference('sup+', [status(thm)], ['51', '56'])).
% 0.21/0.55  thf('58', plain, (((sk_B) = (k1_xboole_0))),
% 0.21/0.55      inference('sup+', [status(thm)], ['50', '57'])).
% 0.21/0.55  thf('59', plain, (![X21 : $i]: ((k1_subset_1 @ X21) = (k1_xboole_0))),
% 0.21/0.55      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.21/0.55  thf('60', plain,
% 0.21/0.55      ((((sk_B) != (k1_subset_1 @ sk_A)))
% 0.21/0.55         <= (~ (((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.21/0.55      inference('split', [status(esa)], ['4'])).
% 0.21/0.55  thf('61', plain,
% 0.21/0.55      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.21/0.55      inference('sup-', [status(thm)], ['59', '60'])).
% 0.21/0.55  thf('62', plain, (~ (((sk_B) = (k1_subset_1 @ sk_A)))),
% 0.21/0.55      inference('sat_resolution*', [status(thm)], ['5', '29'])).
% 0.21/0.55  thf('63', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.55      inference('simpl_trail', [status(thm)], ['61', '62'])).
% 0.21/0.55  thf('64', plain, ($false),
% 0.21/0.55      inference('simplify_reflect-', [status(thm)], ['58', '63'])).
% 0.21/0.55  
% 0.21/0.55  % SZS output end Refutation
% 0.21/0.55  
% 0.21/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
