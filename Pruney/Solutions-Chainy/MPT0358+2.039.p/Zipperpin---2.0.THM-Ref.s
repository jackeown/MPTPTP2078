%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.TleyBKLDp5

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:27 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 114 expanded)
%              Number of leaves         :   21 (  39 expanded)
%              Depth                    :   13
%              Number of atoms          :  467 ( 853 expanded)
%              Number of equality atoms :   43 (  75 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
     != ( k1_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ( sk_B
     != ( k1_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('3',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['2'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('4',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ X10 @ X11 )
      | ( r2_hidden @ X10 @ X12 )
      | ( X12
       != ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('5',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r2_hidden @ X10 @ ( k1_zfmisc_1 @ X11 ) )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('7',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X15 @ X16 )
      | ( m1_subset_1 @ X15 @ X16 )
      | ( v1_xboole_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('9',plain,(
    ! [X23: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['8','9'])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('11',plain,(
    ! [X21: $i,X22: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X21 @ X22 ) @ ( k1_zfmisc_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_subset_1 @ X0 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['8','9'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('14',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k3_subset_1 @ X19 @ X20 )
        = ( k4_xboole_0 @ X19 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['2'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('17',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['12','19'])).

thf('21',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ X16 )
      | ( r2_hidden @ X15 @ X16 )
      | ( v1_xboole_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( r2_hidden @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X23: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( r2_hidden @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X13 @ X12 )
      | ( r1_tarski @ X13 @ X11 )
      | ( X12
       != ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('26',plain,(
    ! [X11: $i,X13: $i] :
      ( ( r1_tarski @ X13 @ X11 )
      | ~ ( r2_hidden @ X13 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['24','26'])).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('28',plain,(
    ! [X18: $i] :
      ( ( k1_subset_1 @ X18 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('29',plain,
    ( ( sk_B
      = ( k1_subset_1 @ sk_A ) )
    | ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( sk_B
      = ( k1_subset_1 @ sk_A ) )
   <= ( sk_B
      = ( k1_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['29'])).

thf('31',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
      = ( k1_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['28','30'])).

thf('32',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
   <= ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('33',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ k1_xboole_0 ) )
   <= ( ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
      & ( sk_B
        = ( k1_subset_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
      = ( k1_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['28','30'])).

thf('35',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ ( k3_subset_1 @ sk_A @ k1_xboole_0 ) )
   <= ( ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
      & ( sk_B
        = ( k1_subset_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,
    ( ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ( sk_B
     != ( k1_subset_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','35'])).

thf('37',plain,
    ( ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ( sk_B
      = ( k1_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['29'])).

thf('38',plain,
    ( ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['29'])).

thf('39',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k3_subset_1 @ X19 @ X20 )
        = ( k4_xboole_0 @ X19 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('41',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf(t38_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) )
     => ( A = k1_xboole_0 ) ) )).

thf('42',plain,(
    ! [X8: $i,X9: $i] :
      ( ( X8 = k1_xboole_0 )
      | ~ ( r1_tarski @ X8 @ ( k4_xboole_0 @ X9 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t38_xboole_1])).

thf('43',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['38','43'])).

thf('45',plain,(
    ! [X18: $i] :
      ( ( k1_subset_1 @ X18 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('46',plain,
    ( ( sk_B
     != ( k1_subset_1 @ sk_A ) )
   <= ( sk_B
     != ( k1_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('47',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B
     != ( k1_subset_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( sk_B
       != ( k1_subset_1 @ sk_A ) )
      & ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['44','47'])).

thf('49',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ( sk_B
      = ( k1_subset_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','36','37','49'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.TleyBKLDp5
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:08:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.49  % Solved by: fo/fo7.sh
% 0.20/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.49  % done 160 iterations in 0.040s
% 0.20/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.49  % SZS output start Refutation
% 0.20/0.49  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.49  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.49  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 0.20/0.49  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.20/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.49  thf(t38_subset_1, conjecture,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.49       ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) ) <=>
% 0.20/0.49         ( ( B ) = ( k1_subset_1 @ A ) ) ) ))).
% 0.20/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.49    (~( ![A:$i,B:$i]:
% 0.20/0.49        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.49          ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) ) <=>
% 0.20/0.49            ( ( B ) = ( k1_subset_1 @ A ) ) ) ) )),
% 0.20/0.49    inference('cnf.neg', [status(esa)], [t38_subset_1])).
% 0.20/0.49  thf('0', plain,
% 0.20/0.49      ((((sk_B) != (k1_subset_1 @ sk_A))
% 0.20/0.49        | ~ (r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('1', plain,
% 0.20/0.49      (~ ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))) | 
% 0.20/0.49       ~ (((sk_B) = (k1_subset_1 @ sk_A)))),
% 0.20/0.49      inference('split', [status(esa)], ['0'])).
% 0.20/0.49  thf(d10_xboole_0, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.49  thf('2', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.20/0.49      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.49  thf('3', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.20/0.49      inference('simplify', [status(thm)], ['2'])).
% 0.20/0.49  thf(d1_zfmisc_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.20/0.49       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.20/0.49  thf('4', plain,
% 0.20/0.49      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.49         (~ (r1_tarski @ X10 @ X11)
% 0.20/0.49          | (r2_hidden @ X10 @ X12)
% 0.20/0.49          | ((X12) != (k1_zfmisc_1 @ X11)))),
% 0.20/0.49      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.20/0.49  thf('5', plain,
% 0.20/0.49      (![X10 : $i, X11 : $i]:
% 0.20/0.49         ((r2_hidden @ X10 @ (k1_zfmisc_1 @ X11)) | ~ (r1_tarski @ X10 @ X11))),
% 0.20/0.49      inference('simplify', [status(thm)], ['4'])).
% 0.20/0.49  thf('6', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['3', '5'])).
% 0.20/0.49  thf(d2_subset_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( ( v1_xboole_0 @ A ) =>
% 0.20/0.49         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.20/0.49       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.49         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.20/0.49  thf('7', plain,
% 0.20/0.49      (![X15 : $i, X16 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X15 @ X16)
% 0.20/0.49          | (m1_subset_1 @ X15 @ X16)
% 0.20/0.49          | (v1_xboole_0 @ X16))),
% 0.20/0.49      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.20/0.49  thf('8', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 0.20/0.49          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.49  thf(fc1_subset_1, axiom,
% 0.20/0.49    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.20/0.49  thf('9', plain, (![X23 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X23))),
% 0.20/0.49      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.20/0.49  thf('10', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.20/0.49      inference('clc', [status(thm)], ['8', '9'])).
% 0.20/0.49  thf(dt_k3_subset_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.49       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.20/0.49  thf('11', plain,
% 0.20/0.49      (![X21 : $i, X22 : $i]:
% 0.20/0.49         ((m1_subset_1 @ (k3_subset_1 @ X21 @ X22) @ (k1_zfmisc_1 @ X21))
% 0.20/0.49          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X21)))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.20/0.49  thf('12', plain,
% 0.20/0.49      (![X0 : $i]: (m1_subset_1 @ (k3_subset_1 @ X0 @ X0) @ (k1_zfmisc_1 @ X0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.49  thf('13', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.20/0.49      inference('clc', [status(thm)], ['8', '9'])).
% 0.20/0.49  thf(d5_subset_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.49       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.20/0.49  thf('14', plain,
% 0.20/0.49      (![X19 : $i, X20 : $i]:
% 0.20/0.49         (((k3_subset_1 @ X19 @ X20) = (k4_xboole_0 @ X19 @ X20))
% 0.20/0.49          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X19)))),
% 0.20/0.49      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.20/0.49  thf('15', plain,
% 0.20/0.49      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.49  thf('16', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.20/0.49      inference('simplify', [status(thm)], ['2'])).
% 0.20/0.49  thf(l32_xboole_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.49  thf('17', plain,
% 0.20/0.49      (![X3 : $i, X5 : $i]:
% 0.20/0.49         (((k4_xboole_0 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 0.20/0.49      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.20/0.49  thf('18', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.49  thf('19', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.20/0.49      inference('sup+', [status(thm)], ['15', '18'])).
% 0.20/0.49  thf('20', plain,
% 0.20/0.49      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.20/0.49      inference('demod', [status(thm)], ['12', '19'])).
% 0.20/0.49  thf('21', plain,
% 0.20/0.49      (![X15 : $i, X16 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X15 @ X16)
% 0.20/0.49          | (r2_hidden @ X15 @ X16)
% 0.20/0.49          | (v1_xboole_0 @ X16))),
% 0.20/0.49      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.20/0.49  thf('22', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 0.20/0.49          | (r2_hidden @ k1_xboole_0 @ (k1_zfmisc_1 @ X0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.49  thf('23', plain, (![X23 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X23))),
% 0.20/0.49      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.20/0.49  thf('24', plain,
% 0.20/0.49      (![X0 : $i]: (r2_hidden @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.20/0.49      inference('clc', [status(thm)], ['22', '23'])).
% 0.20/0.49  thf('25', plain,
% 0.20/0.49      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X13 @ X12)
% 0.20/0.49          | (r1_tarski @ X13 @ X11)
% 0.20/0.49          | ((X12) != (k1_zfmisc_1 @ X11)))),
% 0.20/0.49      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.20/0.49  thf('26', plain,
% 0.20/0.49      (![X11 : $i, X13 : $i]:
% 0.20/0.49         ((r1_tarski @ X13 @ X11) | ~ (r2_hidden @ X13 @ (k1_zfmisc_1 @ X11)))),
% 0.20/0.49      inference('simplify', [status(thm)], ['25'])).
% 0.20/0.49  thf('27', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.20/0.49      inference('sup-', [status(thm)], ['24', '26'])).
% 0.20/0.49  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 0.20/0.49  thf('28', plain, (![X18 : $i]: ((k1_subset_1 @ X18) = (k1_xboole_0))),
% 0.20/0.49      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.20/0.49  thf('29', plain,
% 0.20/0.49      ((((sk_B) = (k1_subset_1 @ sk_A))
% 0.20/0.49        | (r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('30', plain,
% 0.20/0.49      ((((sk_B) = (k1_subset_1 @ sk_A))) <= ((((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.20/0.49      inference('split', [status(esa)], ['29'])).
% 0.20/0.49  thf('31', plain,
% 0.20/0.49      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.20/0.49      inference('sup+', [status(thm)], ['28', '30'])).
% 0.20/0.49  thf('32', plain,
% 0.20/0.49      ((~ (r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))
% 0.20/0.49         <= (~ ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))))),
% 0.20/0.49      inference('split', [status(esa)], ['0'])).
% 0.20/0.49  thf('33', plain,
% 0.20/0.49      ((~ (r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ k1_xboole_0)))
% 0.20/0.49         <= (~ ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))) & 
% 0.20/0.49             (((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['31', '32'])).
% 0.20/0.49  thf('34', plain,
% 0.20/0.49      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.20/0.49      inference('sup+', [status(thm)], ['28', '30'])).
% 0.20/0.49  thf('35', plain,
% 0.20/0.49      ((~ (r1_tarski @ k1_xboole_0 @ (k3_subset_1 @ sk_A @ k1_xboole_0)))
% 0.20/0.49         <= (~ ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))) & 
% 0.20/0.49             (((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.20/0.49      inference('demod', [status(thm)], ['33', '34'])).
% 0.20/0.49  thf('36', plain,
% 0.20/0.49      (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))) | 
% 0.20/0.49       ~ (((sk_B) = (k1_subset_1 @ sk_A)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['27', '35'])).
% 0.20/0.49  thf('37', plain,
% 0.20/0.49      (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))) | 
% 0.20/0.49       (((sk_B) = (k1_subset_1 @ sk_A)))),
% 0.20/0.49      inference('split', [status(esa)], ['29'])).
% 0.20/0.49  thf('38', plain,
% 0.20/0.49      (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))
% 0.20/0.49         <= (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))))),
% 0.20/0.49      inference('split', [status(esa)], ['29'])).
% 0.20/0.49  thf('39', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('40', plain,
% 0.20/0.49      (![X19 : $i, X20 : $i]:
% 0.20/0.49         (((k3_subset_1 @ X19 @ X20) = (k4_xboole_0 @ X19 @ X20))
% 0.20/0.49          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X19)))),
% 0.20/0.49      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.20/0.49  thf('41', plain,
% 0.20/0.49      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.20/0.49      inference('sup-', [status(thm)], ['39', '40'])).
% 0.20/0.49  thf(t38_xboole_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) ) =>
% 0.20/0.49       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.49  thf('42', plain,
% 0.20/0.49      (![X8 : $i, X9 : $i]:
% 0.20/0.49         (((X8) = (k1_xboole_0)) | ~ (r1_tarski @ X8 @ (k4_xboole_0 @ X9 @ X8)))),
% 0.20/0.49      inference('cnf', [status(esa)], [t38_xboole_1])).
% 0.20/0.49  thf('43', plain,
% 0.20/0.49      ((~ (r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 0.20/0.49        | ((sk_B) = (k1_xboole_0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['41', '42'])).
% 0.20/0.49  thf('44', plain,
% 0.20/0.49      ((((sk_B) = (k1_xboole_0)))
% 0.20/0.49         <= (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['38', '43'])).
% 0.20/0.49  thf('45', plain, (![X18 : $i]: ((k1_subset_1 @ X18) = (k1_xboole_0))),
% 0.20/0.49      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.20/0.49  thf('46', plain,
% 0.20/0.49      ((((sk_B) != (k1_subset_1 @ sk_A)))
% 0.20/0.49         <= (~ (((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.20/0.49      inference('split', [status(esa)], ['0'])).
% 0.20/0.49  thf('47', plain,
% 0.20/0.49      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['45', '46'])).
% 0.20/0.49  thf('48', plain,
% 0.20/0.49      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.20/0.49         <= (~ (((sk_B) = (k1_subset_1 @ sk_A))) & 
% 0.20/0.49             ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['44', '47'])).
% 0.20/0.49  thf('49', plain,
% 0.20/0.49      (~ ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))) | 
% 0.20/0.49       (((sk_B) = (k1_subset_1 @ sk_A)))),
% 0.20/0.49      inference('simplify', [status(thm)], ['48'])).
% 0.20/0.49  thf('50', plain, ($false),
% 0.20/0.49      inference('sat_resolution*', [status(thm)], ['1', '36', '37', '49'])).
% 0.20/0.49  
% 0.20/0.49  % SZS output end Refutation
% 0.20/0.49  
% 0.20/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
