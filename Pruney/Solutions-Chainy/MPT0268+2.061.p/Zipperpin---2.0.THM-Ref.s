%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ta13FmFsL3

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:00 EST 2020

% Result     : Theorem 0.77s
% Output     : Refutation 0.77s
% Verified   : 
% Statistics : Number of formulae       :   43 (  79 expanded)
%              Number of leaves         :   10 (  22 expanded)
%              Depth                    :   11
%              Number of atoms          :  364 ( 719 expanded)
%              Number of equality atoms :   37 (  72 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t65_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
          = A )
      <=> ~ ( r2_hidden @ B @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t65_zfmisc_1])).

thf('0',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
   <= ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
   <= ( r2_hidden @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf(t64_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) )
    <=> ( ( r2_hidden @ A @ B )
        & ( A != C ) ) ) )).

thf('6',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( X16 != X18 )
      | ~ ( r2_hidden @ X16 @ ( k4_xboole_0 @ X17 @ ( k1_tarski @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('7',plain,(
    ! [X17: $i,X18: $i] :
      ~ ( r2_hidden @ X18 @ ( k4_xboole_0 @ X17 @ ( k1_tarski @ X18 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A )
    | ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['4','8'])).

thf('10',plain,(
    ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['2','9'])).

thf('11',plain,(
    ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','10'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('12',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['12'])).

thf('14',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['12'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['16','17'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('19',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X11 @ X10 )
      | ( X11 = X8 )
      | ( X10
       != ( k1_tarski @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('20',plain,(
    ! [X8: $i,X11: $i] :
      ( ( X11 = X8 )
      | ~ ( r2_hidden @ X11 @ ( k1_tarski @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ( ( sk_D @ X1 @ ( k1_tarski @ X0 ) @ X1 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['18','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['12'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( X1
        = ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ( X1
        = ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('26',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A )
    | ( r2_hidden @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('27',plain,(
    ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
 != sk_A ),
    inference('sat_resolution*',[status(thm)],['2','9','26'])).

thf('28',plain,(
    ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
 != sk_A ),
    inference(simpl_trail,[status(thm)],['25','27'])).

thf('29',plain,
    ( ( sk_A != sk_A )
    | ( r2_hidden @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['24','28'])).

thf('30',plain,(
    r2_hidden @ sk_B @ sk_A ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    $false ),
    inference(demod,[status(thm)],['11','30'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ta13FmFsL3
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:25:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.77/0.95  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.77/0.95  % Solved by: fo/fo7.sh
% 0.77/0.95  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.77/0.95  % done 515 iterations in 0.499s
% 0.77/0.95  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.77/0.95  % SZS output start Refutation
% 0.77/0.95  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.77/0.95  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.77/0.95  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.77/0.95  thf(sk_B_type, type, sk_B: $i).
% 0.77/0.95  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.77/0.95  thf(sk_A_type, type, sk_A: $i).
% 0.77/0.95  thf(t65_zfmisc_1, conjecture,
% 0.77/0.95    (![A:$i,B:$i]:
% 0.77/0.95     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.77/0.95       ( ~( r2_hidden @ B @ A ) ) ))).
% 0.77/0.95  thf(zf_stmt_0, negated_conjecture,
% 0.77/0.95    (~( ![A:$i,B:$i]:
% 0.77/0.95        ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.77/0.95          ( ~( r2_hidden @ B @ A ) ) ) )),
% 0.77/0.95    inference('cnf.neg', [status(esa)], [t65_zfmisc_1])).
% 0.77/0.95  thf('0', plain,
% 0.77/0.95      ((~ (r2_hidden @ sk_B @ sk_A)
% 0.77/0.95        | ((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))),
% 0.77/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.95  thf('1', plain,
% 0.77/0.95      ((~ (r2_hidden @ sk_B @ sk_A)) <= (~ ((r2_hidden @ sk_B @ sk_A)))),
% 0.77/0.95      inference('split', [status(esa)], ['0'])).
% 0.77/0.95  thf('2', plain,
% 0.77/0.95      (~ ((r2_hidden @ sk_B @ sk_A)) | 
% 0.77/0.95       (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))),
% 0.77/0.95      inference('split', [status(esa)], ['0'])).
% 0.77/0.95  thf('3', plain,
% 0.77/0.95      (((r2_hidden @ sk_B @ sk_A)
% 0.77/0.95        | ((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) != (sk_A)))),
% 0.77/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.95  thf('4', plain,
% 0.77/0.95      (((r2_hidden @ sk_B @ sk_A)) <= (((r2_hidden @ sk_B @ sk_A)))),
% 0.77/0.95      inference('split', [status(esa)], ['3'])).
% 0.77/0.95  thf('5', plain,
% 0.77/0.95      ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))
% 0.77/0.95         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 0.77/0.95      inference('split', [status(esa)], ['0'])).
% 0.77/0.95  thf(t64_zfmisc_1, axiom,
% 0.77/0.95    (![A:$i,B:$i,C:$i]:
% 0.77/0.95     ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) ) <=>
% 0.77/0.95       ( ( r2_hidden @ A @ B ) & ( ( A ) != ( C ) ) ) ))).
% 0.77/0.95  thf('6', plain,
% 0.77/0.95      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.77/0.95         (((X16) != (X18))
% 0.77/0.95          | ~ (r2_hidden @ X16 @ (k4_xboole_0 @ X17 @ (k1_tarski @ X18))))),
% 0.77/0.95      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 0.77/0.95  thf('7', plain,
% 0.77/0.95      (![X17 : $i, X18 : $i]:
% 0.77/0.95         ~ (r2_hidden @ X18 @ (k4_xboole_0 @ X17 @ (k1_tarski @ X18)))),
% 0.77/0.95      inference('simplify', [status(thm)], ['6'])).
% 0.77/0.95  thf('8', plain,
% 0.77/0.95      ((~ (r2_hidden @ sk_B @ sk_A))
% 0.77/0.95         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 0.77/0.95      inference('sup-', [status(thm)], ['5', '7'])).
% 0.77/0.95  thf('9', plain,
% 0.77/0.95      (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))) | 
% 0.77/0.95       ~ ((r2_hidden @ sk_B @ sk_A))),
% 0.77/0.95      inference('sup-', [status(thm)], ['4', '8'])).
% 0.77/0.95  thf('10', plain, (~ ((r2_hidden @ sk_B @ sk_A))),
% 0.77/0.95      inference('sat_resolution*', [status(thm)], ['2', '9'])).
% 0.77/0.95  thf('11', plain, (~ (r2_hidden @ sk_B @ sk_A)),
% 0.77/0.95      inference('simpl_trail', [status(thm)], ['1', '10'])).
% 0.77/0.95  thf(d5_xboole_0, axiom,
% 0.77/0.95    (![A:$i,B:$i,C:$i]:
% 0.77/0.95     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.77/0.95       ( ![D:$i]:
% 0.77/0.95         ( ( r2_hidden @ D @ C ) <=>
% 0.77/0.95           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.77/0.95  thf('12', plain,
% 0.77/0.95      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.77/0.95         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 0.77/0.95          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 0.77/0.95          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.77/0.95      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.77/0.95  thf('13', plain,
% 0.77/0.95      (![X0 : $i, X1 : $i]:
% 0.77/0.95         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 0.77/0.95          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 0.77/0.95      inference('eq_fact', [status(thm)], ['12'])).
% 0.77/0.95  thf('14', plain,
% 0.77/0.95      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.77/0.95         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 0.77/0.95          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 0.77/0.95          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 0.77/0.95          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.77/0.95      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.77/0.95  thf('15', plain,
% 0.77/0.95      (![X0 : $i, X1 : $i]:
% 0.77/0.95         (((X0) = (k4_xboole_0 @ X0 @ X1))
% 0.77/0.95          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 0.77/0.95          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1)
% 0.77/0.95          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 0.77/0.95      inference('sup-', [status(thm)], ['13', '14'])).
% 0.77/0.95  thf('16', plain,
% 0.77/0.95      (![X0 : $i, X1 : $i]:
% 0.77/0.95         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1)
% 0.77/0.95          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 0.77/0.95          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 0.77/0.95      inference('simplify', [status(thm)], ['15'])).
% 0.77/0.95  thf('17', plain,
% 0.77/0.95      (![X0 : $i, X1 : $i]:
% 0.77/0.95         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 0.77/0.95          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 0.77/0.95      inference('eq_fact', [status(thm)], ['12'])).
% 0.77/0.95  thf('18', plain,
% 0.77/0.95      (![X0 : $i, X1 : $i]:
% 0.77/0.95         (((X0) = (k4_xboole_0 @ X0 @ X1))
% 0.77/0.95          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1))),
% 0.77/0.95      inference('clc', [status(thm)], ['16', '17'])).
% 0.77/0.95  thf(d1_tarski, axiom,
% 0.77/0.95    (![A:$i,B:$i]:
% 0.77/0.95     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.77/0.95       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.77/0.95  thf('19', plain,
% 0.77/0.95      (![X8 : $i, X10 : $i, X11 : $i]:
% 0.77/0.95         (~ (r2_hidden @ X11 @ X10)
% 0.77/0.95          | ((X11) = (X8))
% 0.77/0.95          | ((X10) != (k1_tarski @ X8)))),
% 0.77/0.95      inference('cnf', [status(esa)], [d1_tarski])).
% 0.77/0.95  thf('20', plain,
% 0.77/0.95      (![X8 : $i, X11 : $i]:
% 0.77/0.95         (((X11) = (X8)) | ~ (r2_hidden @ X11 @ (k1_tarski @ X8)))),
% 0.77/0.95      inference('simplify', [status(thm)], ['19'])).
% 0.77/0.95  thf('21', plain,
% 0.77/0.95      (![X0 : $i, X1 : $i]:
% 0.77/0.95         (((X1) = (k4_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 0.77/0.95          | ((sk_D @ X1 @ (k1_tarski @ X0) @ X1) = (X0)))),
% 0.77/0.95      inference('sup-', [status(thm)], ['18', '20'])).
% 0.77/0.95  thf('22', plain,
% 0.77/0.95      (![X0 : $i, X1 : $i]:
% 0.77/0.95         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 0.77/0.95          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 0.77/0.95      inference('eq_fact', [status(thm)], ['12'])).
% 0.77/0.95  thf('23', plain,
% 0.77/0.95      (![X0 : $i, X1 : $i]:
% 0.77/0.95         ((r2_hidden @ X0 @ X1)
% 0.77/0.95          | ((X1) = (k4_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 0.77/0.95          | ((X1) = (k4_xboole_0 @ X1 @ (k1_tarski @ X0))))),
% 0.77/0.95      inference('sup+', [status(thm)], ['21', '22'])).
% 0.77/0.95  thf('24', plain,
% 0.77/0.95      (![X0 : $i, X1 : $i]:
% 0.77/0.95         (((X1) = (k4_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 0.77/0.95          | (r2_hidden @ X0 @ X1))),
% 0.77/0.95      inference('simplify', [status(thm)], ['23'])).
% 0.77/0.95  thf('25', plain,
% 0.77/0.95      ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) != (sk_A)))
% 0.77/0.95         <= (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 0.77/0.95      inference('split', [status(esa)], ['3'])).
% 0.77/0.95  thf('26', plain,
% 0.77/0.95      (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))) | 
% 0.77/0.95       ((r2_hidden @ sk_B @ sk_A))),
% 0.77/0.95      inference('split', [status(esa)], ['3'])).
% 0.77/0.95  thf('27', plain, (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))),
% 0.77/0.95      inference('sat_resolution*', [status(thm)], ['2', '9', '26'])).
% 0.77/0.95  thf('28', plain, (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) != (sk_A))),
% 0.77/0.95      inference('simpl_trail', [status(thm)], ['25', '27'])).
% 0.77/0.95  thf('29', plain, ((((sk_A) != (sk_A)) | (r2_hidden @ sk_B @ sk_A))),
% 0.77/0.95      inference('sup-', [status(thm)], ['24', '28'])).
% 0.77/0.95  thf('30', plain, ((r2_hidden @ sk_B @ sk_A)),
% 0.77/0.95      inference('simplify', [status(thm)], ['29'])).
% 0.77/0.95  thf('31', plain, ($false), inference('demod', [status(thm)], ['11', '30'])).
% 0.77/0.95  
% 0.77/0.95  % SZS output end Refutation
% 0.77/0.95  
% 0.77/0.96  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
