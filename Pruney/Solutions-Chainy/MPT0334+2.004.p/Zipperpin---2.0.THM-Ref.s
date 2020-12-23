%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0qRyeIbPJV

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:10 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   36 (  39 expanded)
%              Number of leaves         :   15 (  17 expanded)
%              Depth                    :   10
%              Number of atoms          :  291 ( 334 expanded)
%              Number of equality atoms :   29 (  34 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t141_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( ( k4_xboole_0 @ ( k2_xboole_0 @ B @ ( k1_tarski @ A ) ) @ ( k1_tarski @ A ) )
        = B ) ) )).

thf('0',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k4_xboole_0 @ ( k2_xboole_0 @ X20 @ ( k1_tarski @ X21 ) ) @ ( k1_tarski @ X21 ) )
        = X20 )
      | ( r2_hidden @ X21 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t141_zfmisc_1])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X4 @ X5 ) @ X5 )
      = ( k4_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('2',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k4_xboole_0 @ X20 @ ( k1_tarski @ X21 ) )
        = X20 )
      | ( r2_hidden @ X21 @ X20 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('3',plain,(
    ! [X6: $i,X8: $i] :
      ( ( r1_xboole_0 @ X6 @ X8 )
      | ( ( k4_xboole_0 @ X6 @ X8 )
       != X6 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ ( k1_tarski @ X1 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf(t87_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( ( k2_xboole_0 @ ( k4_xboole_0 @ C @ A ) @ B )
        = ( k4_xboole_0 @ ( k2_xboole_0 @ C @ B ) @ A ) ) ) )).

thf('6',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r1_xboole_0 @ X9 @ X10 )
      | ( ( k2_xboole_0 @ ( k4_xboole_0 @ X11 @ X9 ) @ X10 )
        = ( k4_xboole_0 @ ( k2_xboole_0 @ X11 @ X10 ) @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t87_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
        = ( k4_xboole_0 @ ( k2_xboole_0 @ X2 @ ( k1_tarski @ X0 ) ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t147_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( A != B )
     => ( ( k4_xboole_0 @ ( k2_xboole_0 @ C @ ( k1_tarski @ A ) ) @ ( k1_tarski @ B ) )
        = ( k2_xboole_0 @ ( k4_xboole_0 @ C @ ( k1_tarski @ B ) ) @ ( k1_tarski @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( A != B )
       => ( ( k4_xboole_0 @ ( k2_xboole_0 @ C @ ( k1_tarski @ A ) ) @ ( k1_tarski @ B ) )
          = ( k2_xboole_0 @ ( k4_xboole_0 @ C @ ( k1_tarski @ B ) ) @ ( k1_tarski @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t147_zfmisc_1])).

thf('8',plain,(
    ( k4_xboole_0 @ ( k2_xboole_0 @ sk_C_1 @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_B ) )
 != ( k2_xboole_0 @ ( k4_xboole_0 @ sk_C_1 @ ( k1_tarski @ sk_B ) ) @ ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('10',plain,(
    ( k4_xboole_0 @ ( k2_xboole_0 @ sk_C_1 @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_B ) )
 != ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ sk_C_1 @ ( k1_tarski @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,
    ( ( ( k2_xboole_0 @ ( k4_xboole_0 @ sk_C_1 @ ( k1_tarski @ sk_B ) ) @ ( k1_tarski @ sk_A ) )
     != ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ sk_C_1 @ ( k1_tarski @ sk_B ) ) ) )
    | ( r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('13',plain,
    ( ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ sk_C_1 @ ( k1_tarski @ sk_B ) ) )
     != ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ sk_C_1 @ ( k1_tarski @ sk_B ) ) ) )
    | ( r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference(simplify,[status(thm)],['13'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('15',plain,(
    ! [X12: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X15 @ X14 )
      | ( X15 = X12 )
      | ( X14
       != ( k1_tarski @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('16',plain,(
    ! [X12: $i,X15: $i] :
      ( ( X15 = X12 )
      | ~ ( r2_hidden @ X15 @ ( k1_tarski @ X12 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    sk_A = sk_B ),
    inference('sup-',[status(thm)],['14','16'])).

thf('18',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['17','18'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0qRyeIbPJV
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:43:38 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.52  % Solved by: fo/fo7.sh
% 0.21/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.52  % done 103 iterations in 0.067s
% 0.21/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.52  % SZS output start Refutation
% 0.21/0.52  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.52  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.52  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.52  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.52  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.52  thf(t141_zfmisc_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( ~( r2_hidden @ A @ B ) ) =>
% 0.21/0.52       ( ( k4_xboole_0 @
% 0.21/0.52           ( k2_xboole_0 @ B @ ( k1_tarski @ A ) ) @ ( k1_tarski @ A ) ) =
% 0.21/0.52         ( B ) ) ))).
% 0.21/0.52  thf('0', plain,
% 0.21/0.52      (![X20 : $i, X21 : $i]:
% 0.21/0.52         (((k4_xboole_0 @ (k2_xboole_0 @ X20 @ (k1_tarski @ X21)) @ 
% 0.21/0.52            (k1_tarski @ X21)) = (X20))
% 0.21/0.52          | (r2_hidden @ X21 @ X20))),
% 0.21/0.52      inference('cnf', [status(esa)], [t141_zfmisc_1])).
% 0.21/0.52  thf(t40_xboole_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.21/0.52  thf('1', plain,
% 0.21/0.52      (![X4 : $i, X5 : $i]:
% 0.21/0.52         ((k4_xboole_0 @ (k2_xboole_0 @ X4 @ X5) @ X5)
% 0.21/0.52           = (k4_xboole_0 @ X4 @ X5))),
% 0.21/0.52      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.21/0.52  thf('2', plain,
% 0.21/0.52      (![X20 : $i, X21 : $i]:
% 0.21/0.52         (((k4_xboole_0 @ X20 @ (k1_tarski @ X21)) = (X20))
% 0.21/0.52          | (r2_hidden @ X21 @ X20))),
% 0.21/0.52      inference('demod', [status(thm)], ['0', '1'])).
% 0.21/0.52  thf(t83_xboole_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.21/0.52  thf('3', plain,
% 0.21/0.52      (![X6 : $i, X8 : $i]:
% 0.21/0.52         ((r1_xboole_0 @ X6 @ X8) | ((k4_xboole_0 @ X6 @ X8) != (X6)))),
% 0.21/0.52      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.21/0.52  thf('4', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         (((X0) != (X0))
% 0.21/0.52          | (r2_hidden @ X1 @ X0)
% 0.21/0.52          | (r1_xboole_0 @ X0 @ (k1_tarski @ X1)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.52  thf('5', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         ((r1_xboole_0 @ X0 @ (k1_tarski @ X1)) | (r2_hidden @ X1 @ X0))),
% 0.21/0.52      inference('simplify', [status(thm)], ['4'])).
% 0.21/0.52  thf(t87_xboole_1, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i]:
% 0.21/0.52     ( ( r1_xboole_0 @ A @ B ) =>
% 0.21/0.52       ( ( k2_xboole_0 @ ( k4_xboole_0 @ C @ A ) @ B ) =
% 0.21/0.52         ( k4_xboole_0 @ ( k2_xboole_0 @ C @ B ) @ A ) ) ))).
% 0.21/0.52  thf('6', plain,
% 0.21/0.52      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.52         (~ (r1_xboole_0 @ X9 @ X10)
% 0.21/0.52          | ((k2_xboole_0 @ (k4_xboole_0 @ X11 @ X9) @ X10)
% 0.21/0.52              = (k4_xboole_0 @ (k2_xboole_0 @ X11 @ X10) @ X9)))),
% 0.21/0.52      inference('cnf', [status(esa)], [t87_xboole_1])).
% 0.21/0.52  thf('7', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.52         ((r2_hidden @ X0 @ X1)
% 0.21/0.52          | ((k2_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ (k1_tarski @ X0))
% 0.21/0.52              = (k4_xboole_0 @ (k2_xboole_0 @ X2 @ (k1_tarski @ X0)) @ X1)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.52  thf(t147_zfmisc_1, conjecture,
% 0.21/0.52    (![A:$i,B:$i,C:$i]:
% 0.21/0.52     ( ( ( A ) != ( B ) ) =>
% 0.21/0.52       ( ( k4_xboole_0 @
% 0.21/0.52           ( k2_xboole_0 @ C @ ( k1_tarski @ A ) ) @ ( k1_tarski @ B ) ) =
% 0.21/0.52         ( k2_xboole_0 @
% 0.21/0.52           ( k4_xboole_0 @ C @ ( k1_tarski @ B ) ) @ ( k1_tarski @ A ) ) ) ))).
% 0.21/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.52    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.52        ( ( ( A ) != ( B ) ) =>
% 0.21/0.52          ( ( k4_xboole_0 @
% 0.21/0.52              ( k2_xboole_0 @ C @ ( k1_tarski @ A ) ) @ ( k1_tarski @ B ) ) =
% 0.21/0.52            ( k2_xboole_0 @
% 0.21/0.52              ( k4_xboole_0 @ C @ ( k1_tarski @ B ) ) @ ( k1_tarski @ A ) ) ) ) )),
% 0.21/0.52    inference('cnf.neg', [status(esa)], [t147_zfmisc_1])).
% 0.21/0.52  thf('8', plain,
% 0.21/0.52      (((k4_xboole_0 @ (k2_xboole_0 @ sk_C_1 @ (k1_tarski @ sk_A)) @ 
% 0.21/0.52         (k1_tarski @ sk_B))
% 0.21/0.52         != (k2_xboole_0 @ (k4_xboole_0 @ sk_C_1 @ (k1_tarski @ sk_B)) @ 
% 0.21/0.52             (k1_tarski @ sk_A)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(commutativity_k2_xboole_0, axiom,
% 0.21/0.52    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.21/0.52  thf('9', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.21/0.52      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.21/0.52  thf('10', plain,
% 0.21/0.52      (((k4_xboole_0 @ (k2_xboole_0 @ sk_C_1 @ (k1_tarski @ sk_A)) @ 
% 0.21/0.52         (k1_tarski @ sk_B))
% 0.21/0.52         != (k2_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.21/0.52             (k4_xboole_0 @ sk_C_1 @ (k1_tarski @ sk_B))))),
% 0.21/0.52      inference('demod', [status(thm)], ['8', '9'])).
% 0.21/0.52  thf('11', plain,
% 0.21/0.52      ((((k2_xboole_0 @ (k4_xboole_0 @ sk_C_1 @ (k1_tarski @ sk_B)) @ 
% 0.21/0.52          (k1_tarski @ sk_A))
% 0.21/0.52          != (k2_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.21/0.52              (k4_xboole_0 @ sk_C_1 @ (k1_tarski @ sk_B))))
% 0.21/0.52        | (r2_hidden @ sk_A @ (k1_tarski @ sk_B)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['7', '10'])).
% 0.21/0.52  thf('12', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.21/0.52      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.21/0.52  thf('13', plain,
% 0.21/0.52      ((((k2_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.21/0.52          (k4_xboole_0 @ sk_C_1 @ (k1_tarski @ sk_B)))
% 0.21/0.52          != (k2_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.21/0.52              (k4_xboole_0 @ sk_C_1 @ (k1_tarski @ sk_B))))
% 0.21/0.52        | (r2_hidden @ sk_A @ (k1_tarski @ sk_B)))),
% 0.21/0.52      inference('demod', [status(thm)], ['11', '12'])).
% 0.21/0.52  thf('14', plain, ((r2_hidden @ sk_A @ (k1_tarski @ sk_B))),
% 0.21/0.52      inference('simplify', [status(thm)], ['13'])).
% 0.21/0.52  thf(d1_tarski, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.21/0.52       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.21/0.52  thf('15', plain,
% 0.21/0.52      (![X12 : $i, X14 : $i, X15 : $i]:
% 0.21/0.52         (~ (r2_hidden @ X15 @ X14)
% 0.21/0.52          | ((X15) = (X12))
% 0.21/0.52          | ((X14) != (k1_tarski @ X12)))),
% 0.21/0.52      inference('cnf', [status(esa)], [d1_tarski])).
% 0.21/0.52  thf('16', plain,
% 0.21/0.52      (![X12 : $i, X15 : $i]:
% 0.21/0.52         (((X15) = (X12)) | ~ (r2_hidden @ X15 @ (k1_tarski @ X12)))),
% 0.21/0.52      inference('simplify', [status(thm)], ['15'])).
% 0.21/0.52  thf('17', plain, (((sk_A) = (sk_B))),
% 0.21/0.52      inference('sup-', [status(thm)], ['14', '16'])).
% 0.21/0.52  thf('18', plain, (((sk_A) != (sk_B))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('19', plain, ($false),
% 0.21/0.52      inference('simplify_reflect-', [status(thm)], ['17', '18'])).
% 0.21/0.52  
% 0.21/0.52  % SZS output end Refutation
% 0.21/0.52  
% 0.21/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
