%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wvxlVN35dE

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:00 EST 2020

% Result     : Theorem 0.76s
% Output     : Refutation 0.76s
% Verified   : 
% Statistics : Number of formulae       :   45 (  87 expanded)
%              Number of leaves         :    9 (  24 expanded)
%              Depth                    :   11
%              Number of atoms          :  383 ( 805 expanded)
%              Number of equality atoms :   39 (  82 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('5',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( X9 != X8 )
      | ( r2_hidden @ X9 @ X10 )
      | ( X10
       != ( k1_tarski @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('6',plain,(
    ! [X8: $i] :
      ( r2_hidden @ X8 @ ( k1_tarski @ X8 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('8',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('9',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ sk_A )
        | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_B ) ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['7','9'])).

thf('11',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['6','10'])).

thf('12',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A )
    | ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['4','11'])).

thf('13',plain,(
    ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['2','12'])).

thf('14',plain,(
    ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','13'])).

thf('15',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['15'])).

thf('17',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['15'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X11 @ X10 )
      | ( X11 = X8 )
      | ( X10
       != ( k1_tarski @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('23',plain,(
    ! [X8: $i,X11: $i] :
      ( ( X11 = X8 )
      | ~ ( r2_hidden @ X11 @ ( k1_tarski @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ( ( sk_D @ X1 @ ( k1_tarski @ X0 ) @ X1 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['21','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['15'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( X1
        = ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ( X1
        = ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('29',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A )
    | ( r2_hidden @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('30',plain,(
    ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
 != sk_A ),
    inference('sat_resolution*',[status(thm)],['2','12','29'])).

thf('31',plain,(
    ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
 != sk_A ),
    inference(simpl_trail,[status(thm)],['28','30'])).

thf('32',plain,
    ( ( sk_A != sk_A )
    | ( r2_hidden @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['27','31'])).

thf('33',plain,(
    r2_hidden @ sk_B @ sk_A ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    $false ),
    inference(demod,[status(thm)],['14','33'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wvxlVN35dE
% 0.12/0.34  % Computer   : n019.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:49:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.76/1.00  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.76/1.00  % Solved by: fo/fo7.sh
% 0.76/1.00  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.76/1.00  % done 636 iterations in 0.557s
% 0.76/1.00  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.76/1.00  % SZS output start Refutation
% 0.76/1.00  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.76/1.00  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.76/1.00  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.76/1.00  thf(sk_A_type, type, sk_A: $i).
% 0.76/1.00  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.76/1.00  thf(sk_B_type, type, sk_B: $i).
% 0.76/1.00  thf(t65_zfmisc_1, conjecture,
% 0.76/1.00    (![A:$i,B:$i]:
% 0.76/1.00     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.76/1.00       ( ~( r2_hidden @ B @ A ) ) ))).
% 0.76/1.00  thf(zf_stmt_0, negated_conjecture,
% 0.76/1.00    (~( ![A:$i,B:$i]:
% 0.76/1.00        ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.76/1.00          ( ~( r2_hidden @ B @ A ) ) ) )),
% 0.76/1.00    inference('cnf.neg', [status(esa)], [t65_zfmisc_1])).
% 0.76/1.00  thf('0', plain,
% 0.76/1.00      ((~ (r2_hidden @ sk_B @ sk_A)
% 0.76/1.00        | ((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))),
% 0.76/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/1.00  thf('1', plain,
% 0.76/1.00      ((~ (r2_hidden @ sk_B @ sk_A)) <= (~ ((r2_hidden @ sk_B @ sk_A)))),
% 0.76/1.00      inference('split', [status(esa)], ['0'])).
% 0.76/1.00  thf('2', plain,
% 0.76/1.00      (~ ((r2_hidden @ sk_B @ sk_A)) | 
% 0.76/1.00       (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))),
% 0.76/1.00      inference('split', [status(esa)], ['0'])).
% 0.76/1.00  thf('3', plain,
% 0.76/1.00      (((r2_hidden @ sk_B @ sk_A)
% 0.76/1.00        | ((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) != (sk_A)))),
% 0.76/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/1.00  thf('4', plain,
% 0.76/1.00      (((r2_hidden @ sk_B @ sk_A)) <= (((r2_hidden @ sk_B @ sk_A)))),
% 0.76/1.00      inference('split', [status(esa)], ['3'])).
% 0.76/1.00  thf(d1_tarski, axiom,
% 0.76/1.00    (![A:$i,B:$i]:
% 0.76/1.00     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.76/1.00       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.76/1.00  thf('5', plain,
% 0.76/1.00      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.76/1.00         (((X9) != (X8)) | (r2_hidden @ X9 @ X10) | ((X10) != (k1_tarski @ X8)))),
% 0.76/1.00      inference('cnf', [status(esa)], [d1_tarski])).
% 0.76/1.00  thf('6', plain, (![X8 : $i]: (r2_hidden @ X8 @ (k1_tarski @ X8))),
% 0.76/1.00      inference('simplify', [status(thm)], ['5'])).
% 0.76/1.00  thf('7', plain,
% 0.76/1.00      ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))
% 0.76/1.00         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 0.76/1.00      inference('split', [status(esa)], ['0'])).
% 0.76/1.00  thf(d5_xboole_0, axiom,
% 0.76/1.00    (![A:$i,B:$i,C:$i]:
% 0.76/1.00     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.76/1.00       ( ![D:$i]:
% 0.76/1.00         ( ( r2_hidden @ D @ C ) <=>
% 0.76/1.00           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.76/1.00  thf('8', plain,
% 0.76/1.00      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.76/1.00         (~ (r2_hidden @ X4 @ X3)
% 0.76/1.00          | ~ (r2_hidden @ X4 @ X2)
% 0.76/1.00          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.76/1.00      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.76/1.00  thf('9', plain,
% 0.76/1.00      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.76/1.00         (~ (r2_hidden @ X4 @ X2)
% 0.76/1.00          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.76/1.00      inference('simplify', [status(thm)], ['8'])).
% 0.76/1.00  thf('10', plain,
% 0.76/1.00      ((![X0 : $i]:
% 0.76/1.00          (~ (r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_B))))
% 0.76/1.00         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 0.76/1.00      inference('sup-', [status(thm)], ['7', '9'])).
% 0.76/1.00  thf('11', plain,
% 0.76/1.00      ((~ (r2_hidden @ sk_B @ sk_A))
% 0.76/1.00         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 0.76/1.00      inference('sup-', [status(thm)], ['6', '10'])).
% 0.76/1.00  thf('12', plain,
% 0.76/1.00      (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))) | 
% 0.76/1.00       ~ ((r2_hidden @ sk_B @ sk_A))),
% 0.76/1.00      inference('sup-', [status(thm)], ['4', '11'])).
% 0.76/1.00  thf('13', plain, (~ ((r2_hidden @ sk_B @ sk_A))),
% 0.76/1.00      inference('sat_resolution*', [status(thm)], ['2', '12'])).
% 0.76/1.00  thf('14', plain, (~ (r2_hidden @ sk_B @ sk_A)),
% 0.76/1.00      inference('simpl_trail', [status(thm)], ['1', '13'])).
% 0.76/1.00  thf('15', plain,
% 0.76/1.00      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.76/1.00         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 0.76/1.00          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 0.76/1.00          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.76/1.00      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.76/1.00  thf('16', plain,
% 0.76/1.00      (![X0 : $i, X1 : $i]:
% 0.76/1.00         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 0.76/1.00          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 0.76/1.00      inference('eq_fact', [status(thm)], ['15'])).
% 0.76/1.00  thf('17', plain,
% 0.76/1.00      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.76/1.00         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 0.76/1.00          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 0.76/1.00          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 0.76/1.00          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.76/1.00      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.76/1.00  thf('18', plain,
% 0.76/1.00      (![X0 : $i, X1 : $i]:
% 0.76/1.00         (((X0) = (k4_xboole_0 @ X0 @ X1))
% 0.76/1.00          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 0.76/1.00          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1)
% 0.76/1.00          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 0.76/1.00      inference('sup-', [status(thm)], ['16', '17'])).
% 0.76/1.00  thf('19', plain,
% 0.76/1.00      (![X0 : $i, X1 : $i]:
% 0.76/1.00         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1)
% 0.76/1.00          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 0.76/1.00          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 0.76/1.00      inference('simplify', [status(thm)], ['18'])).
% 0.76/1.00  thf('20', plain,
% 0.76/1.00      (![X0 : $i, X1 : $i]:
% 0.76/1.00         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 0.76/1.00          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 0.76/1.00      inference('eq_fact', [status(thm)], ['15'])).
% 0.76/1.00  thf('21', plain,
% 0.76/1.00      (![X0 : $i, X1 : $i]:
% 0.76/1.00         (((X0) = (k4_xboole_0 @ X0 @ X1))
% 0.76/1.00          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1))),
% 0.76/1.00      inference('clc', [status(thm)], ['19', '20'])).
% 0.76/1.00  thf('22', plain,
% 0.76/1.00      (![X8 : $i, X10 : $i, X11 : $i]:
% 0.76/1.00         (~ (r2_hidden @ X11 @ X10)
% 0.76/1.00          | ((X11) = (X8))
% 0.76/1.00          | ((X10) != (k1_tarski @ X8)))),
% 0.76/1.00      inference('cnf', [status(esa)], [d1_tarski])).
% 0.76/1.00  thf('23', plain,
% 0.76/1.00      (![X8 : $i, X11 : $i]:
% 0.76/1.00         (((X11) = (X8)) | ~ (r2_hidden @ X11 @ (k1_tarski @ X8)))),
% 0.76/1.00      inference('simplify', [status(thm)], ['22'])).
% 0.76/1.00  thf('24', plain,
% 0.76/1.00      (![X0 : $i, X1 : $i]:
% 0.76/1.00         (((X1) = (k4_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 0.76/1.00          | ((sk_D @ X1 @ (k1_tarski @ X0) @ X1) = (X0)))),
% 0.76/1.00      inference('sup-', [status(thm)], ['21', '23'])).
% 0.76/1.00  thf('25', plain,
% 0.76/1.00      (![X0 : $i, X1 : $i]:
% 0.76/1.00         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 0.76/1.00          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 0.76/1.00      inference('eq_fact', [status(thm)], ['15'])).
% 0.76/1.00  thf('26', plain,
% 0.76/1.00      (![X0 : $i, X1 : $i]:
% 0.76/1.00         ((r2_hidden @ X0 @ X1)
% 0.76/1.00          | ((X1) = (k4_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 0.76/1.00          | ((X1) = (k4_xboole_0 @ X1 @ (k1_tarski @ X0))))),
% 0.76/1.00      inference('sup+', [status(thm)], ['24', '25'])).
% 0.76/1.00  thf('27', plain,
% 0.76/1.00      (![X0 : $i, X1 : $i]:
% 0.76/1.00         (((X1) = (k4_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 0.76/1.00          | (r2_hidden @ X0 @ X1))),
% 0.76/1.00      inference('simplify', [status(thm)], ['26'])).
% 0.76/1.00  thf('28', plain,
% 0.76/1.00      ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) != (sk_A)))
% 0.76/1.00         <= (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 0.76/1.00      inference('split', [status(esa)], ['3'])).
% 0.76/1.00  thf('29', plain,
% 0.76/1.00      (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))) | 
% 0.76/1.00       ((r2_hidden @ sk_B @ sk_A))),
% 0.76/1.00      inference('split', [status(esa)], ['3'])).
% 0.76/1.00  thf('30', plain, (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))),
% 0.76/1.00      inference('sat_resolution*', [status(thm)], ['2', '12', '29'])).
% 0.76/1.00  thf('31', plain, (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) != (sk_A))),
% 0.76/1.00      inference('simpl_trail', [status(thm)], ['28', '30'])).
% 0.76/1.00  thf('32', plain, ((((sk_A) != (sk_A)) | (r2_hidden @ sk_B @ sk_A))),
% 0.76/1.00      inference('sup-', [status(thm)], ['27', '31'])).
% 0.76/1.00  thf('33', plain, ((r2_hidden @ sk_B @ sk_A)),
% 0.76/1.00      inference('simplify', [status(thm)], ['32'])).
% 0.76/1.00  thf('34', plain, ($false), inference('demod', [status(thm)], ['14', '33'])).
% 0.76/1.00  
% 0.76/1.00  % SZS output end Refutation
% 0.76/1.00  
% 0.76/1.01  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
