%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.b6upDiCjny

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:30:56 EST 2020

% Result     : Theorem 0.33s
% Output     : Refutation 0.33s
% Verified   : 
% Statistics : Number of formulae       :   31 (  33 expanded)
%              Number of leaves         :   14 (  15 expanded)
%              Depth                    :    7
%              Number of atoms          :  204 ( 228 expanded)
%              Number of equality atoms :   29 (  33 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(l33_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = ( k1_tarski @ A ) )
    <=> ~ ( r2_hidden @ A @ B ) ) )).

thf('0',plain,(
    ! [X18: $i,X20: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X18 ) @ X20 )
        = ( k1_tarski @ X18 ) )
      | ( r2_hidden @ X18 @ X20 ) ) ),
    inference(cnf,[status(esa)],[l33_zfmisc_1])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k4_xboole_0 @ X3 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
        = ( k5_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(t29_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( A != B )
     => ( ( k5_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k2_tarski @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( A != B )
       => ( ( k5_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
          = ( k2_tarski @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t29_zfmisc_1])).

thf('3',plain,(
    ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
     != ( k2_tarski @ sk_A @ sk_B ) )
    | ( r2_hidden @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('5',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_tarski @ X10 @ X11 )
      = ( k2_xboole_0 @ ( k1_tarski @ X10 ) @ ( k1_tarski @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('6',plain,
    ( ( ( k2_tarski @ sk_A @ sk_B )
     != ( k2_tarski @ sk_A @ sk_B ) )
    | ( r2_hidden @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    r2_hidden @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference(simplify,[status(thm)],['6'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('8',plain,(
    ! [X12: $i] :
      ( ( k2_tarski @ X12 @ X12 )
      = ( k1_tarski @ X12 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('9',plain,(
    ! [X4: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ( X8 = X7 )
      | ( X8 = X4 )
      | ( X6
       != ( k2_tarski @ X7 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('10',plain,(
    ! [X4: $i,X7: $i,X8: $i] :
      ( ( X8 = X4 )
      | ( X8 = X7 )
      | ~ ( r2_hidden @ X8 @ ( k2_tarski @ X7 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1 = X0 )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    sk_B = sk_A ),
    inference('sup-',[status(thm)],['7','12'])).

thf('14',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['13','14'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.b6upDiCjny
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:41:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.33/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.33/0.52  % Solved by: fo/fo7.sh
% 0.33/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.33/0.52  % done 50 iterations in 0.034s
% 0.33/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.33/0.52  % SZS output start Refutation
% 0.33/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.33/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.33/0.52  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.33/0.52  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.33/0.52  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.33/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.33/0.52  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.33/0.52  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.33/0.52  thf(l33_zfmisc_1, axiom,
% 0.33/0.52    (![A:$i,B:$i]:
% 0.33/0.52     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) <=>
% 0.33/0.52       ( ~( r2_hidden @ A @ B ) ) ))).
% 0.33/0.52  thf('0', plain,
% 0.33/0.52      (![X18 : $i, X20 : $i]:
% 0.33/0.52         (((k4_xboole_0 @ (k1_tarski @ X18) @ X20) = (k1_tarski @ X18))
% 0.33/0.52          | (r2_hidden @ X18 @ X20))),
% 0.33/0.52      inference('cnf', [status(esa)], [l33_zfmisc_1])).
% 0.33/0.52  thf(t98_xboole_1, axiom,
% 0.33/0.52    (![A:$i,B:$i]:
% 0.33/0.52     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.33/0.52  thf('1', plain,
% 0.33/0.52      (![X2 : $i, X3 : $i]:
% 0.33/0.52         ((k2_xboole_0 @ X2 @ X3)
% 0.33/0.52           = (k5_xboole_0 @ X2 @ (k4_xboole_0 @ X3 @ X2)))),
% 0.33/0.52      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.33/0.52  thf('2', plain,
% 0.33/0.52      (![X0 : $i, X1 : $i]:
% 0.33/0.52         (((k2_xboole_0 @ X1 @ (k1_tarski @ X0))
% 0.33/0.52            = (k5_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 0.33/0.52          | (r2_hidden @ X0 @ X1))),
% 0.33/0.52      inference('sup+', [status(thm)], ['0', '1'])).
% 0.33/0.52  thf(t29_zfmisc_1, conjecture,
% 0.33/0.52    (![A:$i,B:$i]:
% 0.33/0.52     ( ( ( A ) != ( B ) ) =>
% 0.33/0.52       ( ( k5_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.33/0.52         ( k2_tarski @ A @ B ) ) ))).
% 0.33/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.33/0.52    (~( ![A:$i,B:$i]:
% 0.33/0.52        ( ( ( A ) != ( B ) ) =>
% 0.33/0.52          ( ( k5_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.33/0.52            ( k2_tarski @ A @ B ) ) ) )),
% 0.33/0.52    inference('cnf.neg', [status(esa)], [t29_zfmisc_1])).
% 0.33/0.52  thf('3', plain,
% 0.33/0.52      (((k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.33/0.52         != (k2_tarski @ sk_A @ sk_B))),
% 0.33/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.52  thf('4', plain,
% 0.33/0.52      ((((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.33/0.52          != (k2_tarski @ sk_A @ sk_B))
% 0.33/0.52        | (r2_hidden @ sk_B @ (k1_tarski @ sk_A)))),
% 0.33/0.52      inference('sup-', [status(thm)], ['2', '3'])).
% 0.33/0.52  thf(t41_enumset1, axiom,
% 0.33/0.52    (![A:$i,B:$i]:
% 0.33/0.52     ( ( k2_tarski @ A @ B ) =
% 0.33/0.52       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.33/0.52  thf('5', plain,
% 0.33/0.52      (![X10 : $i, X11 : $i]:
% 0.33/0.52         ((k2_tarski @ X10 @ X11)
% 0.33/0.52           = (k2_xboole_0 @ (k1_tarski @ X10) @ (k1_tarski @ X11)))),
% 0.33/0.52      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.33/0.52  thf('6', plain,
% 0.33/0.52      ((((k2_tarski @ sk_A @ sk_B) != (k2_tarski @ sk_A @ sk_B))
% 0.33/0.52        | (r2_hidden @ sk_B @ (k1_tarski @ sk_A)))),
% 0.33/0.52      inference('demod', [status(thm)], ['4', '5'])).
% 0.33/0.52  thf('7', plain, ((r2_hidden @ sk_B @ (k1_tarski @ sk_A))),
% 0.33/0.52      inference('simplify', [status(thm)], ['6'])).
% 0.33/0.52  thf(t69_enumset1, axiom,
% 0.33/0.52    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.33/0.52  thf('8', plain, (![X12 : $i]: ((k2_tarski @ X12 @ X12) = (k1_tarski @ X12))),
% 0.33/0.52      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.33/0.52  thf(d2_tarski, axiom,
% 0.33/0.52    (![A:$i,B:$i,C:$i]:
% 0.33/0.52     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.33/0.52       ( ![D:$i]:
% 0.33/0.52         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.33/0.52  thf('9', plain,
% 0.33/0.52      (![X4 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.33/0.52         (~ (r2_hidden @ X8 @ X6)
% 0.33/0.52          | ((X8) = (X7))
% 0.33/0.52          | ((X8) = (X4))
% 0.33/0.52          | ((X6) != (k2_tarski @ X7 @ X4)))),
% 0.33/0.52      inference('cnf', [status(esa)], [d2_tarski])).
% 0.33/0.52  thf('10', plain,
% 0.33/0.52      (![X4 : $i, X7 : $i, X8 : $i]:
% 0.33/0.52         (((X8) = (X4))
% 0.33/0.52          | ((X8) = (X7))
% 0.33/0.52          | ~ (r2_hidden @ X8 @ (k2_tarski @ X7 @ X4)))),
% 0.33/0.52      inference('simplify', [status(thm)], ['9'])).
% 0.33/0.52  thf('11', plain,
% 0.33/0.52      (![X0 : $i, X1 : $i]:
% 0.33/0.52         (~ (r2_hidden @ X1 @ (k1_tarski @ X0)) | ((X1) = (X0)) | ((X1) = (X0)))),
% 0.33/0.52      inference('sup-', [status(thm)], ['8', '10'])).
% 0.33/0.52  thf('12', plain,
% 0.33/0.52      (![X0 : $i, X1 : $i]:
% 0.33/0.52         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.33/0.52      inference('simplify', [status(thm)], ['11'])).
% 0.33/0.52  thf('13', plain, (((sk_B) = (sk_A))),
% 0.33/0.52      inference('sup-', [status(thm)], ['7', '12'])).
% 0.33/0.52  thf('14', plain, (((sk_A) != (sk_B))),
% 0.33/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.52  thf('15', plain, ($false),
% 0.33/0.52      inference('simplify_reflect-', [status(thm)], ['13', '14'])).
% 0.33/0.52  
% 0.33/0.52  % SZS output end Refutation
% 0.33/0.52  
% 0.33/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
