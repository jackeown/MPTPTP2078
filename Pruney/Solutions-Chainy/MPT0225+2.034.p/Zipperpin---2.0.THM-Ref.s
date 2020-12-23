%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ZA1aJdJxo7

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:49 EST 2020

% Result     : Theorem 1.00s
% Output     : Refutation 1.00s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 103 expanded)
%              Number of leaves         :    9 (  27 expanded)
%              Depth                    :   14
%              Number of atoms          :  484 (1102 expanded)
%              Number of equality atoms :   64 ( 160 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('0',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['0'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('2',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X9 @ X8 )
      | ( X9 = X6 )
      | ( X8
       != ( k1_tarski @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('3',plain,(
    ! [X6: $i,X9: $i] :
      ( ( X9 = X6 )
      | ~ ( r2_hidden @ X9 @ ( k1_tarski @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
        = ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
      | ( ( sk_D @ ( k1_tarski @ X0 ) @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['0'])).

thf('6',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['0'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( ( k1_tarski @ X0 )
        = ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
      | ( ( k1_tarski @ X0 )
        = ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['4','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
        = ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf(t20_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
          = ( k1_tarski @ A ) )
      <=> ( A != B ) ) ),
    inference('cnf.neg',[status(esa)],[t20_zfmisc_1])).

thf('13',plain,
    ( ( sk_A = sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
     != ( k1_tarski @ sk_A ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['13'])).

thf('15',plain,
    ( ( sk_A != sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
      = ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( sk_A != sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
      = ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['15'])).

thf('17',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( X7 != X6 )
      | ( r2_hidden @ X7 @ X8 )
      | ( X8
       != ( k1_tarski @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('18',plain,(
    ! [X6: $i] :
      ( r2_hidden @ X6 @ ( k1_tarski @ X6 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,
    ( ( sk_A = sk_B )
   <= ( sk_A = sk_B ) ),
    inference(split,[status(esa)],['13'])).

thf('20',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
      = ( k1_tarski @ sk_A ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
      = ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['15'])).

thf('21',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_B ) )
      = ( k1_tarski @ sk_A ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
        = ( k1_tarski @ sk_A ) )
      & ( sk_A = sk_B ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( sk_A = sk_B )
   <= ( sk_A = sk_B ) ),
    inference(split,[status(esa)],['13'])).

thf('23',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_B ) )
      = ( k1_tarski @ sk_B ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
        = ( k1_tarski @ sk_A ) )
      & ( sk_A = sk_B ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('25',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_B ) )
        | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_B ) ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
        = ( k1_tarski @ sk_A ) )
      & ( sk_A = sk_B ) ) ),
    inference('sup-',[status(thm)],['23','25'])).

thf('27',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_B ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
        = ( k1_tarski @ sk_A ) )
      & ( sk_A = sk_B ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
     != ( k1_tarski @ sk_A ) )
    | ( sk_A != sk_B ) ),
    inference('sup-',[status(thm)],['18','27'])).

thf('29',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
     != ( k1_tarski @ sk_A ) )
    | ( sk_A = sk_B ) ),
    inference(split,[status(esa)],['13'])).

thf('30',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['16','28','29'])).

thf('31',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['14','30'])).

thf('32',plain,
    ( ( ( k1_tarski @ sk_A )
     != ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['12','31'])).

thf('33',plain,(
    r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X6: $i,X9: $i] :
      ( ( X9 = X6 )
      | ~ ( r2_hidden @ X9 @ ( k1_tarski @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('35',plain,(
    sk_A = sk_B ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( sk_A != sk_B )
   <= ( sk_A != sk_B ) ),
    inference(split,[status(esa)],['15'])).

thf('37',plain,(
    sk_A != sk_B ),
    inference('sat_resolution*',[status(thm)],['16','28'])).

thf('38',plain,(
    sk_A != sk_B ),
    inference(simpl_trail,[status(thm)],['36','37'])).

thf('39',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['35','38'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ZA1aJdJxo7
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:59:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.00/1.23  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.00/1.23  % Solved by: fo/fo7.sh
% 1.00/1.23  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.00/1.23  % done 513 iterations in 0.752s
% 1.00/1.23  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.00/1.23  % SZS output start Refutation
% 1.00/1.23  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.00/1.23  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 1.00/1.23  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.00/1.23  thf(sk_A_type, type, sk_A: $i).
% 1.00/1.23  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.00/1.23  thf(sk_B_type, type, sk_B: $i).
% 1.00/1.23  thf(d5_xboole_0, axiom,
% 1.00/1.23    (![A:$i,B:$i,C:$i]:
% 1.00/1.23     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 1.00/1.23       ( ![D:$i]:
% 1.00/1.23         ( ( r2_hidden @ D @ C ) <=>
% 1.00/1.23           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 1.00/1.23  thf('0', plain,
% 1.00/1.23      (![X1 : $i, X2 : $i, X5 : $i]:
% 1.00/1.23         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 1.00/1.23          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 1.00/1.23          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 1.00/1.23      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.00/1.23  thf('1', plain,
% 1.00/1.23      (![X0 : $i, X1 : $i]:
% 1.00/1.23         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 1.00/1.23          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 1.00/1.23      inference('eq_fact', [status(thm)], ['0'])).
% 1.00/1.23  thf(d1_tarski, axiom,
% 1.00/1.23    (![A:$i,B:$i]:
% 1.00/1.23     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 1.00/1.23       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 1.00/1.23  thf('2', plain,
% 1.00/1.23      (![X6 : $i, X8 : $i, X9 : $i]:
% 1.00/1.23         (~ (r2_hidden @ X9 @ X8) | ((X9) = (X6)) | ((X8) != (k1_tarski @ X6)))),
% 1.00/1.23      inference('cnf', [status(esa)], [d1_tarski])).
% 1.00/1.23  thf('3', plain,
% 1.00/1.23      (![X6 : $i, X9 : $i]:
% 1.00/1.23         (((X9) = (X6)) | ~ (r2_hidden @ X9 @ (k1_tarski @ X6)))),
% 1.00/1.23      inference('simplify', [status(thm)], ['2'])).
% 1.00/1.23  thf('4', plain,
% 1.00/1.23      (![X0 : $i, X1 : $i]:
% 1.00/1.23         (((k1_tarski @ X0) = (k4_xboole_0 @ (k1_tarski @ X0) @ X1))
% 1.00/1.23          | ((sk_D @ (k1_tarski @ X0) @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 1.00/1.23      inference('sup-', [status(thm)], ['1', '3'])).
% 1.00/1.23  thf('5', plain,
% 1.00/1.23      (![X0 : $i, X1 : $i]:
% 1.00/1.23         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 1.00/1.23          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 1.00/1.23      inference('eq_fact', [status(thm)], ['0'])).
% 1.00/1.23  thf('6', plain,
% 1.00/1.23      (![X1 : $i, X2 : $i, X5 : $i]:
% 1.00/1.23         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 1.00/1.23          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 1.00/1.23          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 1.00/1.23          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 1.00/1.23      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.00/1.23  thf('7', plain,
% 1.00/1.23      (![X0 : $i, X1 : $i]:
% 1.00/1.23         (((X0) = (k4_xboole_0 @ X0 @ X1))
% 1.00/1.23          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 1.00/1.23          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1)
% 1.00/1.23          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 1.00/1.23      inference('sup-', [status(thm)], ['5', '6'])).
% 1.00/1.23  thf('8', plain,
% 1.00/1.23      (![X0 : $i, X1 : $i]:
% 1.00/1.23         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1)
% 1.00/1.23          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 1.00/1.23          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 1.00/1.23      inference('simplify', [status(thm)], ['7'])).
% 1.00/1.23  thf('9', plain,
% 1.00/1.23      (![X0 : $i, X1 : $i]:
% 1.00/1.23         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 1.00/1.23          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 1.00/1.23      inference('eq_fact', [status(thm)], ['0'])).
% 1.00/1.23  thf('10', plain,
% 1.00/1.23      (![X0 : $i, X1 : $i]:
% 1.00/1.23         (((X0) = (k4_xboole_0 @ X0 @ X1))
% 1.00/1.23          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1))),
% 1.00/1.23      inference('clc', [status(thm)], ['8', '9'])).
% 1.00/1.23  thf('11', plain,
% 1.00/1.23      (![X0 : $i, X1 : $i]:
% 1.00/1.23         ((r2_hidden @ X0 @ X1)
% 1.00/1.23          | ((k1_tarski @ X0) = (k4_xboole_0 @ (k1_tarski @ X0) @ X1))
% 1.00/1.23          | ((k1_tarski @ X0) = (k4_xboole_0 @ (k1_tarski @ X0) @ X1)))),
% 1.00/1.23      inference('sup+', [status(thm)], ['4', '10'])).
% 1.00/1.23  thf('12', plain,
% 1.00/1.23      (![X0 : $i, X1 : $i]:
% 1.00/1.23         (((k1_tarski @ X0) = (k4_xboole_0 @ (k1_tarski @ X0) @ X1))
% 1.00/1.23          | (r2_hidden @ X0 @ X1))),
% 1.00/1.23      inference('simplify', [status(thm)], ['11'])).
% 1.00/1.23  thf(t20_zfmisc_1, conjecture,
% 1.00/1.23    (![A:$i,B:$i]:
% 1.00/1.23     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 1.00/1.23         ( k1_tarski @ A ) ) <=>
% 1.00/1.23       ( ( A ) != ( B ) ) ))).
% 1.00/1.23  thf(zf_stmt_0, negated_conjecture,
% 1.00/1.23    (~( ![A:$i,B:$i]:
% 1.00/1.23        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 1.00/1.23            ( k1_tarski @ A ) ) <=>
% 1.00/1.23          ( ( A ) != ( B ) ) ) )),
% 1.00/1.23    inference('cnf.neg', [status(esa)], [t20_zfmisc_1])).
% 1.00/1.23  thf('13', plain,
% 1.00/1.23      ((((sk_A) = (sk_B))
% 1.00/1.23        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 1.00/1.23            != (k1_tarski @ sk_A)))),
% 1.00/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.23  thf('14', plain,
% 1.00/1.23      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 1.00/1.23          != (k1_tarski @ sk_A)))
% 1.00/1.23         <= (~
% 1.00/1.23             (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 1.00/1.23                = (k1_tarski @ sk_A))))),
% 1.00/1.23      inference('split', [status(esa)], ['13'])).
% 1.00/1.23  thf('15', plain,
% 1.00/1.23      ((((sk_A) != (sk_B))
% 1.00/1.23        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 1.00/1.23            = (k1_tarski @ sk_A)))),
% 1.00/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.23  thf('16', plain,
% 1.00/1.23      (~ (((sk_A) = (sk_B))) | 
% 1.00/1.23       (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 1.00/1.23          = (k1_tarski @ sk_A)))),
% 1.00/1.23      inference('split', [status(esa)], ['15'])).
% 1.00/1.23  thf('17', plain,
% 1.00/1.23      (![X6 : $i, X7 : $i, X8 : $i]:
% 1.00/1.23         (((X7) != (X6)) | (r2_hidden @ X7 @ X8) | ((X8) != (k1_tarski @ X6)))),
% 1.00/1.23      inference('cnf', [status(esa)], [d1_tarski])).
% 1.00/1.23  thf('18', plain, (![X6 : $i]: (r2_hidden @ X6 @ (k1_tarski @ X6))),
% 1.00/1.23      inference('simplify', [status(thm)], ['17'])).
% 1.00/1.23  thf('19', plain, ((((sk_A) = (sk_B))) <= ((((sk_A) = (sk_B))))),
% 1.00/1.23      inference('split', [status(esa)], ['13'])).
% 1.00/1.23  thf('20', plain,
% 1.00/1.23      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 1.00/1.23          = (k1_tarski @ sk_A)))
% 1.00/1.23         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 1.00/1.23                = (k1_tarski @ sk_A))))),
% 1.00/1.23      inference('split', [status(esa)], ['15'])).
% 1.00/1.23  thf('21', plain,
% 1.00/1.23      ((((k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_B))
% 1.00/1.23          = (k1_tarski @ sk_A)))
% 1.00/1.23         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 1.00/1.23                = (k1_tarski @ sk_A))) & 
% 1.00/1.23             (((sk_A) = (sk_B))))),
% 1.00/1.23      inference('sup+', [status(thm)], ['19', '20'])).
% 1.00/1.23  thf('22', plain, ((((sk_A) = (sk_B))) <= ((((sk_A) = (sk_B))))),
% 1.00/1.23      inference('split', [status(esa)], ['13'])).
% 1.00/1.23  thf('23', plain,
% 1.00/1.23      ((((k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_B))
% 1.00/1.23          = (k1_tarski @ sk_B)))
% 1.00/1.23         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 1.00/1.23                = (k1_tarski @ sk_A))) & 
% 1.00/1.23             (((sk_A) = (sk_B))))),
% 1.00/1.23      inference('demod', [status(thm)], ['21', '22'])).
% 1.00/1.23  thf('24', plain,
% 1.00/1.23      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.00/1.23         (~ (r2_hidden @ X4 @ X3)
% 1.00/1.23          | ~ (r2_hidden @ X4 @ X2)
% 1.00/1.23          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 1.00/1.23      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.00/1.23  thf('25', plain,
% 1.00/1.23      (![X1 : $i, X2 : $i, X4 : $i]:
% 1.00/1.23         (~ (r2_hidden @ X4 @ X2)
% 1.00/1.23          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 1.00/1.23      inference('simplify', [status(thm)], ['24'])).
% 1.00/1.23  thf('26', plain,
% 1.00/1.23      ((![X0 : $i]:
% 1.00/1.23          (~ (r2_hidden @ X0 @ (k1_tarski @ sk_B))
% 1.00/1.23           | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_B))))
% 1.00/1.23         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 1.00/1.23                = (k1_tarski @ sk_A))) & 
% 1.00/1.23             (((sk_A) = (sk_B))))),
% 1.00/1.23      inference('sup-', [status(thm)], ['23', '25'])).
% 1.00/1.23  thf('27', plain,
% 1.00/1.23      ((![X0 : $i]: ~ (r2_hidden @ X0 @ (k1_tarski @ sk_B)))
% 1.00/1.23         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 1.00/1.23                = (k1_tarski @ sk_A))) & 
% 1.00/1.23             (((sk_A) = (sk_B))))),
% 1.00/1.23      inference('simplify', [status(thm)], ['26'])).
% 1.00/1.23  thf('28', plain,
% 1.00/1.23      (~
% 1.00/1.23       (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 1.00/1.23          = (k1_tarski @ sk_A))) | 
% 1.00/1.23       ~ (((sk_A) = (sk_B)))),
% 1.00/1.23      inference('sup-', [status(thm)], ['18', '27'])).
% 1.00/1.23  thf('29', plain,
% 1.00/1.23      (~
% 1.00/1.23       (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 1.00/1.23          = (k1_tarski @ sk_A))) | 
% 1.00/1.23       (((sk_A) = (sk_B)))),
% 1.00/1.23      inference('split', [status(esa)], ['13'])).
% 1.00/1.23  thf('30', plain,
% 1.00/1.23      (~
% 1.00/1.23       (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 1.00/1.23          = (k1_tarski @ sk_A)))),
% 1.00/1.23      inference('sat_resolution*', [status(thm)], ['16', '28', '29'])).
% 1.00/1.23  thf('31', plain,
% 1.00/1.23      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 1.00/1.23         != (k1_tarski @ sk_A))),
% 1.00/1.23      inference('simpl_trail', [status(thm)], ['14', '30'])).
% 1.00/1.23  thf('32', plain,
% 1.00/1.23      ((((k1_tarski @ sk_A) != (k1_tarski @ sk_A))
% 1.00/1.23        | (r2_hidden @ sk_A @ (k1_tarski @ sk_B)))),
% 1.00/1.23      inference('sup-', [status(thm)], ['12', '31'])).
% 1.00/1.23  thf('33', plain, ((r2_hidden @ sk_A @ (k1_tarski @ sk_B))),
% 1.00/1.23      inference('simplify', [status(thm)], ['32'])).
% 1.00/1.23  thf('34', plain,
% 1.00/1.23      (![X6 : $i, X9 : $i]:
% 1.00/1.23         (((X9) = (X6)) | ~ (r2_hidden @ X9 @ (k1_tarski @ X6)))),
% 1.00/1.23      inference('simplify', [status(thm)], ['2'])).
% 1.00/1.23  thf('35', plain, (((sk_A) = (sk_B))),
% 1.00/1.23      inference('sup-', [status(thm)], ['33', '34'])).
% 1.00/1.23  thf('36', plain, ((((sk_A) != (sk_B))) <= (~ (((sk_A) = (sk_B))))),
% 1.00/1.23      inference('split', [status(esa)], ['15'])).
% 1.00/1.23  thf('37', plain, (~ (((sk_A) = (sk_B)))),
% 1.00/1.23      inference('sat_resolution*', [status(thm)], ['16', '28'])).
% 1.00/1.23  thf('38', plain, (((sk_A) != (sk_B))),
% 1.00/1.23      inference('simpl_trail', [status(thm)], ['36', '37'])).
% 1.00/1.23  thf('39', plain, ($false),
% 1.00/1.23      inference('simplify_reflect-', [status(thm)], ['35', '38'])).
% 1.00/1.23  
% 1.00/1.23  % SZS output end Refutation
% 1.00/1.23  
% 1.06/1.24  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
