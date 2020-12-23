%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.aJgEBNJO1k

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:40 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   25 (  31 expanded)
%              Number of leaves         :    8 (  10 expanded)
%              Depth                    :    7
%              Number of atoms          :  216 ( 288 expanded)
%              Number of equality atoms :   41 (  53 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(t7_mcart_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) )
        = A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) )
          = B )
        & ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) )
          = A ) ) ),
    inference('cnf.neg',[status(esa)],[t7_mcart_1])).

thf('0',plain,
    ( ( ( k2_mcart_1 @ ( k4_tarski @ sk_A @ sk_B ) )
     != sk_B )
    | ( ( k1_mcart_1 @ ( k4_tarski @ sk_A @ sk_B ) )
     != sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( k2_mcart_1 @ ( k4_tarski @ sk_A @ sk_B ) )
     != sk_B )
   <= ( ( k2_mcart_1 @ ( k4_tarski @ sk_A @ sk_B ) )
     != sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf(d2_mcart_1,axiom,(
    ! [A: $i] :
      ( ? [B: $i,C: $i] :
          ( A
          = ( k4_tarski @ B @ C ) )
     => ! [B: $i] :
          ( ( B
            = ( k2_mcart_1 @ A ) )
        <=> ! [C: $i,D: $i] :
              ( ( A
                = ( k4_tarski @ C @ D ) )
             => ( B = D ) ) ) ) )).

thf('2',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( X11
       != ( k2_mcart_1 @ X8 ) )
      | ( X11 = X12 )
      | ( X8
       != ( k4_tarski @ X13 @ X12 ) )
      | ( X8
       != ( k4_tarski @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d2_mcart_1])).

thf('3',plain,(
    ! [X9: $i,X10: $i,X12: $i,X13: $i] :
      ( ( ( k4_tarski @ X13 @ X12 )
       != ( k4_tarski @ X9 @ X10 ) )
      | ( ( k2_mcart_1 @ ( k4_tarski @ X13 @ X12 ) )
        = X12 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X1 @ X0 ) )
      = X0 ) ),
    inference(eq_res,[status(thm)],['3'])).

thf('5',plain,
    ( ( sk_B != sk_B )
   <= ( ( k2_mcart_1 @ ( k4_tarski @ sk_A @ sk_B ) )
     != sk_B ) ),
    inference(demod,[status(thm)],['1','4'])).

thf('6',plain,
    ( $false
   <= ( ( k2_mcart_1 @ ( k4_tarski @ sk_A @ sk_B ) )
     != sk_B ) ),
    inference(simplify,[status(thm)],['5'])).

thf(d1_mcart_1,axiom,(
    ! [A: $i] :
      ( ? [B: $i,C: $i] :
          ( A
          = ( k4_tarski @ B @ C ) )
     => ! [B: $i] :
          ( ( B
            = ( k1_mcart_1 @ A ) )
        <=> ! [C: $i,D: $i] :
              ( ( A
                = ( k4_tarski @ C @ D ) )
             => ( B = C ) ) ) ) )).

thf('7',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( X4
       != ( k1_mcart_1 @ X1 ) )
      | ( X4 = X5 )
      | ( X1
       != ( k4_tarski @ X5 @ X6 ) )
      | ( X1
       != ( k4_tarski @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d1_mcart_1])).

thf('8',plain,(
    ! [X2: $i,X3: $i,X5: $i,X6: $i] :
      ( ( ( k4_tarski @ X5 @ X6 )
       != ( k4_tarski @ X2 @ X3 ) )
      | ( ( k1_mcart_1 @ ( k4_tarski @ X5 @ X6 ) )
        = X5 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X1 @ X0 ) )
      = X1 ) ),
    inference(eq_res,[status(thm)],['8'])).

thf('10',plain,
    ( ( ( k1_mcart_1 @ ( k4_tarski @ sk_A @ sk_B ) )
     != sk_A )
   <= ( ( k1_mcart_1 @ ( k4_tarski @ sk_A @ sk_B ) )
     != sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('11',plain,
    ( ( sk_A != sk_A )
   <= ( ( k1_mcart_1 @ ( k4_tarski @ sk_A @ sk_B ) )
     != sk_A ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( k1_mcart_1 @ ( k4_tarski @ sk_A @ sk_B ) )
    = sk_A ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,
    ( ( ( k2_mcart_1 @ ( k4_tarski @ sk_A @ sk_B ) )
     != sk_B )
    | ( ( k1_mcart_1 @ ( k4_tarski @ sk_A @ sk_B ) )
     != sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('14',plain,(
    ( k2_mcart_1 @ ( k4_tarski @ sk_A @ sk_B ) )
 != sk_B ),
    inference('sat_resolution*',[status(thm)],['12','13'])).

thf('15',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['6','14'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.aJgEBNJO1k
% 0.14/0.35  % Computer   : n006.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:24:23 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.22/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.48  % Solved by: fo/fo7.sh
% 0.22/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.48  % done 9 iterations in 0.010s
% 0.22/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.48  % SZS output start Refutation
% 0.22/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.48  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.22/0.48  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.22/0.48  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.22/0.48  thf(t7_mcart_1, conjecture,
% 0.22/0.48    (![A:$i,B:$i]:
% 0.22/0.48     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 0.22/0.48       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 0.22/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.48    (~( ![A:$i,B:$i]:
% 0.22/0.48        ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 0.22/0.48          ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ) )),
% 0.22/0.48    inference('cnf.neg', [status(esa)], [t7_mcart_1])).
% 0.22/0.48  thf('0', plain,
% 0.22/0.48      ((((k2_mcart_1 @ (k4_tarski @ sk_A @ sk_B)) != (sk_B))
% 0.22/0.48        | ((k1_mcart_1 @ (k4_tarski @ sk_A @ sk_B)) != (sk_A)))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('1', plain,
% 0.22/0.48      ((((k2_mcart_1 @ (k4_tarski @ sk_A @ sk_B)) != (sk_B)))
% 0.22/0.48         <= (~ (((k2_mcart_1 @ (k4_tarski @ sk_A @ sk_B)) = (sk_B))))),
% 0.22/0.48      inference('split', [status(esa)], ['0'])).
% 0.22/0.48  thf(d2_mcart_1, axiom,
% 0.22/0.48    (![A:$i]:
% 0.22/0.48     ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 0.22/0.48       ( ![B:$i]:
% 0.22/0.48         ( ( ( B ) = ( k2_mcart_1 @ A ) ) <=>
% 0.22/0.48           ( ![C:$i,D:$i]:
% 0.22/0.48             ( ( ( A ) = ( k4_tarski @ C @ D ) ) => ( ( B ) = ( D ) ) ) ) ) ) ))).
% 0.22/0.48  thf('2', plain,
% 0.22/0.48      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.22/0.48         (((X11) != (k2_mcart_1 @ X8))
% 0.22/0.48          | ((X11) = (X12))
% 0.22/0.48          | ((X8) != (k4_tarski @ X13 @ X12))
% 0.22/0.48          | ((X8) != (k4_tarski @ X9 @ X10)))),
% 0.22/0.48      inference('cnf', [status(esa)], [d2_mcart_1])).
% 0.22/0.48  thf('3', plain,
% 0.22/0.48      (![X9 : $i, X10 : $i, X12 : $i, X13 : $i]:
% 0.22/0.48         (((k4_tarski @ X13 @ X12) != (k4_tarski @ X9 @ X10))
% 0.22/0.48          | ((k2_mcart_1 @ (k4_tarski @ X13 @ X12)) = (X12)))),
% 0.22/0.48      inference('simplify', [status(thm)], ['2'])).
% 0.22/0.48  thf('4', plain,
% 0.22/0.48      (![X0 : $i, X1 : $i]: ((k2_mcart_1 @ (k4_tarski @ X1 @ X0)) = (X0))),
% 0.22/0.48      inference('eq_res', [status(thm)], ['3'])).
% 0.22/0.48  thf('5', plain,
% 0.22/0.48      ((((sk_B) != (sk_B)))
% 0.22/0.48         <= (~ (((k2_mcart_1 @ (k4_tarski @ sk_A @ sk_B)) = (sk_B))))),
% 0.22/0.48      inference('demod', [status(thm)], ['1', '4'])).
% 0.22/0.48  thf('6', plain,
% 0.22/0.48      (($false) <= (~ (((k2_mcart_1 @ (k4_tarski @ sk_A @ sk_B)) = (sk_B))))),
% 0.22/0.48      inference('simplify', [status(thm)], ['5'])).
% 0.22/0.48  thf(d1_mcart_1, axiom,
% 0.22/0.48    (![A:$i]:
% 0.22/0.48     ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 0.22/0.48       ( ![B:$i]:
% 0.22/0.48         ( ( ( B ) = ( k1_mcart_1 @ A ) ) <=>
% 0.22/0.48           ( ![C:$i,D:$i]:
% 0.22/0.48             ( ( ( A ) = ( k4_tarski @ C @ D ) ) => ( ( B ) = ( C ) ) ) ) ) ) ))).
% 0.22/0.48  thf('7', plain,
% 0.22/0.48      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.22/0.48         (((X4) != (k1_mcart_1 @ X1))
% 0.22/0.48          | ((X4) = (X5))
% 0.22/0.48          | ((X1) != (k4_tarski @ X5 @ X6))
% 0.22/0.48          | ((X1) != (k4_tarski @ X2 @ X3)))),
% 0.22/0.48      inference('cnf', [status(esa)], [d1_mcart_1])).
% 0.22/0.48  thf('8', plain,
% 0.22/0.48      (![X2 : $i, X3 : $i, X5 : $i, X6 : $i]:
% 0.22/0.48         (((k4_tarski @ X5 @ X6) != (k4_tarski @ X2 @ X3))
% 0.22/0.48          | ((k1_mcart_1 @ (k4_tarski @ X5 @ X6)) = (X5)))),
% 0.22/0.48      inference('simplify', [status(thm)], ['7'])).
% 0.22/0.48  thf('9', plain,
% 0.22/0.48      (![X0 : $i, X1 : $i]: ((k1_mcart_1 @ (k4_tarski @ X1 @ X0)) = (X1))),
% 0.22/0.48      inference('eq_res', [status(thm)], ['8'])).
% 0.22/0.48  thf('10', plain,
% 0.22/0.48      ((((k1_mcart_1 @ (k4_tarski @ sk_A @ sk_B)) != (sk_A)))
% 0.22/0.48         <= (~ (((k1_mcart_1 @ (k4_tarski @ sk_A @ sk_B)) = (sk_A))))),
% 0.22/0.48      inference('split', [status(esa)], ['0'])).
% 0.22/0.48  thf('11', plain,
% 0.22/0.48      ((((sk_A) != (sk_A)))
% 0.22/0.48         <= (~ (((k1_mcart_1 @ (k4_tarski @ sk_A @ sk_B)) = (sk_A))))),
% 0.22/0.48      inference('sup-', [status(thm)], ['9', '10'])).
% 0.22/0.48  thf('12', plain, ((((k1_mcart_1 @ (k4_tarski @ sk_A @ sk_B)) = (sk_A)))),
% 0.22/0.48      inference('simplify', [status(thm)], ['11'])).
% 0.22/0.48  thf('13', plain,
% 0.22/0.48      (~ (((k2_mcart_1 @ (k4_tarski @ sk_A @ sk_B)) = (sk_B))) | 
% 0.22/0.48       ~ (((k1_mcart_1 @ (k4_tarski @ sk_A @ sk_B)) = (sk_A)))),
% 0.22/0.48      inference('split', [status(esa)], ['0'])).
% 0.22/0.48  thf('14', plain, (~ (((k2_mcart_1 @ (k4_tarski @ sk_A @ sk_B)) = (sk_B)))),
% 0.22/0.48      inference('sat_resolution*', [status(thm)], ['12', '13'])).
% 0.22/0.48  thf('15', plain, ($false),
% 0.22/0.48      inference('simpl_trail', [status(thm)], ['6', '14'])).
% 0.22/0.48  
% 0.22/0.48  % SZS output end Refutation
% 0.22/0.48  
% 0.22/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
