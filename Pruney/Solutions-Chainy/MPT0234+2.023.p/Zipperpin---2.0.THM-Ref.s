%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.FgFpUkl4vt

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:30:57 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   22 (  24 expanded)
%              Number of leaves         :   11 (  12 expanded)
%              Depth                    :    6
%              Number of atoms          :  134 ( 158 expanded)
%              Number of equality atoms :   21 (  25 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('0',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X7 ) @ ( k1_tarski @ X8 ) )
        = ( k1_tarski @ X7 ) )
      | ( X7 = X8 ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

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
      ( ( ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
        = ( k5_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) )
      | ( X0 = X1 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('3',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_tarski @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k1_tarski @ X4 ) @ ( k1_tarski @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_tarski @ X1 @ X0 )
        = ( k5_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) )
      | ( X0 = X1 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

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

thf('5',plain,(
    ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( ( k2_tarski @ sk_A @ sk_B )
     != ( k2_tarski @ sk_A @ sk_B ) )
    | ( sk_B = sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    sk_B = sk_A ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['7','8'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.FgFpUkl4vt
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:49:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.44  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.44  % Solved by: fo/fo7.sh
% 0.21/0.44  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.44  % done 7 iterations in 0.009s
% 0.21/0.44  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.44  % SZS output start Refutation
% 0.21/0.44  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.44  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.44  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.21/0.44  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.44  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.44  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.44  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.44  thf(t20_zfmisc_1, axiom,
% 0.21/0.44    (![A:$i,B:$i]:
% 0.21/0.44     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.21/0.44         ( k1_tarski @ A ) ) <=>
% 0.21/0.44       ( ( A ) != ( B ) ) ))).
% 0.21/0.44  thf('0', plain,
% 0.21/0.44      (![X7 : $i, X8 : $i]:
% 0.21/0.44         (((k4_xboole_0 @ (k1_tarski @ X7) @ (k1_tarski @ X8))
% 0.21/0.44            = (k1_tarski @ X7))
% 0.21/0.44          | ((X7) = (X8)))),
% 0.21/0.44      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.21/0.44  thf(t98_xboole_1, axiom,
% 0.21/0.44    (![A:$i,B:$i]:
% 0.21/0.44     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.21/0.44  thf('1', plain,
% 0.21/0.44      (![X2 : $i, X3 : $i]:
% 0.21/0.44         ((k2_xboole_0 @ X2 @ X3)
% 0.21/0.44           = (k5_xboole_0 @ X2 @ (k4_xboole_0 @ X3 @ X2)))),
% 0.21/0.44      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.21/0.44  thf('2', plain,
% 0.21/0.44      (![X0 : $i, X1 : $i]:
% 0.21/0.44         (((k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 0.21/0.44            = (k5_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0)))
% 0.21/0.44          | ((X0) = (X1)))),
% 0.21/0.44      inference('sup+', [status(thm)], ['0', '1'])).
% 0.21/0.44  thf(t41_enumset1, axiom,
% 0.21/0.44    (![A:$i,B:$i]:
% 0.21/0.44     ( ( k2_tarski @ A @ B ) =
% 0.21/0.44       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.21/0.44  thf('3', plain,
% 0.21/0.44      (![X4 : $i, X5 : $i]:
% 0.21/0.44         ((k2_tarski @ X4 @ X5)
% 0.21/0.44           = (k2_xboole_0 @ (k1_tarski @ X4) @ (k1_tarski @ X5)))),
% 0.21/0.44      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.21/0.44  thf('4', plain,
% 0.21/0.44      (![X0 : $i, X1 : $i]:
% 0.21/0.44         (((k2_tarski @ X1 @ X0)
% 0.21/0.44            = (k5_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0)))
% 0.21/0.44          | ((X0) = (X1)))),
% 0.21/0.44      inference('demod', [status(thm)], ['2', '3'])).
% 0.21/0.44  thf(t29_zfmisc_1, conjecture,
% 0.21/0.44    (![A:$i,B:$i]:
% 0.21/0.44     ( ( ( A ) != ( B ) ) =>
% 0.21/0.44       ( ( k5_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.21/0.44         ( k2_tarski @ A @ B ) ) ))).
% 0.21/0.44  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.44    (~( ![A:$i,B:$i]:
% 0.21/0.44        ( ( ( A ) != ( B ) ) =>
% 0.21/0.44          ( ( k5_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.21/0.44            ( k2_tarski @ A @ B ) ) ) )),
% 0.21/0.44    inference('cnf.neg', [status(esa)], [t29_zfmisc_1])).
% 0.21/0.44  thf('5', plain,
% 0.21/0.44      (((k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.21/0.44         != (k2_tarski @ sk_A @ sk_B))),
% 0.21/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.44  thf('6', plain,
% 0.21/0.44      ((((k2_tarski @ sk_A @ sk_B) != (k2_tarski @ sk_A @ sk_B))
% 0.21/0.44        | ((sk_B) = (sk_A)))),
% 0.21/0.44      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.44  thf('7', plain, (((sk_B) = (sk_A))),
% 0.21/0.44      inference('simplify', [status(thm)], ['6'])).
% 0.21/0.44  thf('8', plain, (((sk_A) != (sk_B))),
% 0.21/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.44  thf('9', plain, ($false),
% 0.21/0.44      inference('simplify_reflect-', [status(thm)], ['7', '8'])).
% 0.21/0.44  
% 0.21/0.44  % SZS output end Refutation
% 0.21/0.44  
% 0.21/0.45  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
