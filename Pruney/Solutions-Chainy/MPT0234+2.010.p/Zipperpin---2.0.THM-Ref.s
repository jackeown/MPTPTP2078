%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.q0eh2zVqti

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:30:55 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   41 (  51 expanded)
%              Number of leaves         :   14 (  20 expanded)
%              Depth                    :   13
%              Number of atoms          :  326 ( 437 expanded)
%              Number of equality atoms :   36 (  54 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('0',plain,(
    ! [X9: $i] :
      ( ( k2_tarski @ X9 @ X9 )
      = ( k1_tarski @ X9 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('1',plain,(
    ! [X9: $i] :
      ( ( k2_tarski @ X9 @ X9 )
      = ( k1_tarski @ X9 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        = ( k1_tarski @ A ) )
    <=> ( ~ ( r2_hidden @ A @ C )
        & ( ( r2_hidden @ B @ C )
          | ( A = B ) ) ) ) )).

thf('2',plain,(
    ! [X15: $i,X17: $i,X18: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ X15 @ X17 ) @ X18 )
        = ( k1_tarski @ X15 ) )
      | ( X15 != X17 )
      | ( r2_hidden @ X15 @ X18 ) ) ),
    inference(cnf,[status(esa)],[l38_zfmisc_1])).

thf('3',plain,(
    ! [X17: $i,X18: $i] :
      ( ( r2_hidden @ X17 @ X18 )
      | ( ( k4_xboole_0 @ ( k2_tarski @ X17 @ X17 ) @ X18 )
        = ( k1_tarski @ X17 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['1','3'])).

thf('5',plain,(
    ! [X9: $i] :
      ( ( k2_tarski @ X9 @ X9 )
      = ( k1_tarski @ X9 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('6',plain,(
    ! [X17: $i,X18: $i] :
      ( ( r2_hidden @ X17 @ X18 )
      | ( ( k4_xboole_0 @ ( k2_tarski @ X17 @ X17 ) @ X18 )
        = ( k1_tarski @ X17 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf(d6_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ X1 )
        = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k4_xboole_0 @ X1 @ ( k2_tarski @ X0 @ X0 ) ) ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ X1 )
        = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['5','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_xboole_0 @ ( k2_tarski @ X1 @ X1 ) @ ( k1_tarski @ X0 ) )
        = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X1 ) )
      | ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['4','9'])).

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('11',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_tarski @ X7 @ X8 )
      = ( k2_xboole_0 @ ( k1_tarski @ X7 ) @ ( k1_tarski @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_xboole_0 @ ( k2_tarski @ X1 @ X1 ) @ ( k1_tarski @ X0 ) )
        = ( k2_tarski @ X1 @ X0 ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X1 ) )
      | ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) )
        = ( k2_tarski @ X0 @ X1 ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X1 ) )
      | ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['0','12'])).

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

thf('14',plain,(
    ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( ( k2_tarski @ sk_A @ sk_B )
     != ( k2_tarski @ sk_A @ sk_B ) )
    | ( r2_hidden @ sk_B @ ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) )
    | ( r2_hidden @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('17',plain,(
    ! [X2: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X5 @ X4 )
      | ( X5 = X2 )
      | ( X4
       != ( k1_tarski @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('18',plain,(
    ! [X2: $i,X5: $i] :
      ( ( X5 = X2 )
      | ~ ( r2_hidden @ X5 @ ( k1_tarski @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,
    ( ( r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) )
    | ( sk_B = sk_A ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X2: $i,X5: $i] :
      ( ( X5 = X2 )
      | ~ ( r2_hidden @ X5 @ ( k1_tarski @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('23',plain,(
    sk_A = sk_B ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['23','24'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.q0eh2zVqti
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:22:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.21/0.58  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.58  % Solved by: fo/fo7.sh
% 0.21/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.58  % done 255 iterations in 0.115s
% 0.21/0.58  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.58  % SZS output start Refutation
% 0.21/0.58  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.58  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.58  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.21/0.58  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.58  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.58  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.58  thf(t69_enumset1, axiom,
% 0.21/0.58    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.21/0.58  thf('0', plain, (![X9 : $i]: ((k2_tarski @ X9 @ X9) = (k1_tarski @ X9))),
% 0.21/0.58      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.58  thf('1', plain, (![X9 : $i]: ((k2_tarski @ X9 @ X9) = (k1_tarski @ X9))),
% 0.21/0.58      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.58  thf(l38_zfmisc_1, axiom,
% 0.21/0.58    (![A:$i,B:$i,C:$i]:
% 0.21/0.58     ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k1_tarski @ A ) ) <=>
% 0.21/0.58       ( ( ~( r2_hidden @ A @ C ) ) & 
% 0.21/0.58         ( ( r2_hidden @ B @ C ) | ( ( A ) = ( B ) ) ) ) ))).
% 0.21/0.58  thf('2', plain,
% 0.21/0.58      (![X15 : $i, X17 : $i, X18 : $i]:
% 0.21/0.58         (((k4_xboole_0 @ (k2_tarski @ X15 @ X17) @ X18) = (k1_tarski @ X15))
% 0.21/0.58          | ((X15) != (X17))
% 0.21/0.58          | (r2_hidden @ X15 @ X18))),
% 0.21/0.58      inference('cnf', [status(esa)], [l38_zfmisc_1])).
% 0.21/0.58  thf('3', plain,
% 0.21/0.58      (![X17 : $i, X18 : $i]:
% 0.21/0.58         ((r2_hidden @ X17 @ X18)
% 0.21/0.58          | ((k4_xboole_0 @ (k2_tarski @ X17 @ X17) @ X18) = (k1_tarski @ X17)))),
% 0.21/0.58      inference('simplify', [status(thm)], ['2'])).
% 0.21/0.58  thf('4', plain,
% 0.21/0.58      (![X0 : $i, X1 : $i]:
% 0.21/0.58         (((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_tarski @ X0))
% 0.21/0.58          | (r2_hidden @ X0 @ X1))),
% 0.21/0.58      inference('sup+', [status(thm)], ['1', '3'])).
% 0.21/0.58  thf('5', plain, (![X9 : $i]: ((k2_tarski @ X9 @ X9) = (k1_tarski @ X9))),
% 0.21/0.58      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.58  thf('6', plain,
% 0.21/0.58      (![X17 : $i, X18 : $i]:
% 0.21/0.58         ((r2_hidden @ X17 @ X18)
% 0.21/0.58          | ((k4_xboole_0 @ (k2_tarski @ X17 @ X17) @ X18) = (k1_tarski @ X17)))),
% 0.21/0.58      inference('simplify', [status(thm)], ['2'])).
% 0.21/0.58  thf(d6_xboole_0, axiom,
% 0.21/0.58    (![A:$i,B:$i]:
% 0.21/0.58     ( ( k5_xboole_0 @ A @ B ) =
% 0.21/0.58       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.21/0.58  thf('7', plain,
% 0.21/0.58      (![X0 : $i, X1 : $i]:
% 0.21/0.58         ((k5_xboole_0 @ X0 @ X1)
% 0.21/0.58           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0)))),
% 0.21/0.58      inference('cnf', [status(esa)], [d6_xboole_0])).
% 0.21/0.58  thf('8', plain,
% 0.21/0.58      (![X0 : $i, X1 : $i]:
% 0.21/0.58         (((k5_xboole_0 @ (k2_tarski @ X0 @ X0) @ X1)
% 0.21/0.58            = (k2_xboole_0 @ (k1_tarski @ X0) @ 
% 0.21/0.58               (k4_xboole_0 @ X1 @ (k2_tarski @ X0 @ X0))))
% 0.21/0.58          | (r2_hidden @ X0 @ X1))),
% 0.21/0.58      inference('sup+', [status(thm)], ['6', '7'])).
% 0.21/0.58  thf('9', plain,
% 0.21/0.58      (![X0 : $i, X1 : $i]:
% 0.21/0.58         (((k5_xboole_0 @ (k2_tarski @ X0 @ X0) @ X1)
% 0.21/0.58            = (k2_xboole_0 @ (k1_tarski @ X0) @ 
% 0.21/0.58               (k4_xboole_0 @ X1 @ (k1_tarski @ X0))))
% 0.21/0.58          | (r2_hidden @ X0 @ X1))),
% 0.21/0.58      inference('sup+', [status(thm)], ['5', '8'])).
% 0.21/0.58  thf('10', plain,
% 0.21/0.58      (![X0 : $i, X1 : $i]:
% 0.21/0.58         (((k5_xboole_0 @ (k2_tarski @ X1 @ X1) @ (k1_tarski @ X0))
% 0.21/0.58            = (k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0)))
% 0.21/0.58          | (r2_hidden @ X0 @ (k1_tarski @ X1))
% 0.21/0.58          | (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.21/0.58      inference('sup+', [status(thm)], ['4', '9'])).
% 0.21/0.58  thf(t41_enumset1, axiom,
% 0.21/0.58    (![A:$i,B:$i]:
% 0.21/0.58     ( ( k2_tarski @ A @ B ) =
% 0.21/0.58       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.21/0.58  thf('11', plain,
% 0.21/0.58      (![X7 : $i, X8 : $i]:
% 0.21/0.58         ((k2_tarski @ X7 @ X8)
% 0.21/0.58           = (k2_xboole_0 @ (k1_tarski @ X7) @ (k1_tarski @ X8)))),
% 0.21/0.58      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.21/0.58  thf('12', plain,
% 0.21/0.58      (![X0 : $i, X1 : $i]:
% 0.21/0.58         (((k5_xboole_0 @ (k2_tarski @ X1 @ X1) @ (k1_tarski @ X0))
% 0.21/0.58            = (k2_tarski @ X1 @ X0))
% 0.21/0.58          | (r2_hidden @ X0 @ (k1_tarski @ X1))
% 0.21/0.58          | (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.21/0.58      inference('demod', [status(thm)], ['10', '11'])).
% 0.21/0.58  thf('13', plain,
% 0.21/0.58      (![X0 : $i, X1 : $i]:
% 0.21/0.58         (((k5_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1))
% 0.21/0.58            = (k2_tarski @ X0 @ X1))
% 0.21/0.58          | (r2_hidden @ X0 @ (k1_tarski @ X1))
% 0.21/0.58          | (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.21/0.58      inference('sup+', [status(thm)], ['0', '12'])).
% 0.21/0.58  thf(t29_zfmisc_1, conjecture,
% 0.21/0.58    (![A:$i,B:$i]:
% 0.21/0.58     ( ( ( A ) != ( B ) ) =>
% 0.21/0.58       ( ( k5_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.21/0.58         ( k2_tarski @ A @ B ) ) ))).
% 0.21/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.58    (~( ![A:$i,B:$i]:
% 0.21/0.58        ( ( ( A ) != ( B ) ) =>
% 0.21/0.58          ( ( k5_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.21/0.58            ( k2_tarski @ A @ B ) ) ) )),
% 0.21/0.58    inference('cnf.neg', [status(esa)], [t29_zfmisc_1])).
% 0.21/0.58  thf('14', plain,
% 0.21/0.58      (((k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.21/0.58         != (k2_tarski @ sk_A @ sk_B))),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('15', plain,
% 0.21/0.58      ((((k2_tarski @ sk_A @ sk_B) != (k2_tarski @ sk_A @ sk_B))
% 0.21/0.58        | (r2_hidden @ sk_B @ (k1_tarski @ sk_A))
% 0.21/0.58        | (r2_hidden @ sk_A @ (k1_tarski @ sk_B)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.58  thf('16', plain,
% 0.21/0.58      (((r2_hidden @ sk_A @ (k1_tarski @ sk_B))
% 0.21/0.58        | (r2_hidden @ sk_B @ (k1_tarski @ sk_A)))),
% 0.21/0.58      inference('simplify', [status(thm)], ['15'])).
% 0.21/0.58  thf(d1_tarski, axiom,
% 0.21/0.58    (![A:$i,B:$i]:
% 0.21/0.58     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.21/0.58       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.21/0.58  thf('17', plain,
% 0.21/0.58      (![X2 : $i, X4 : $i, X5 : $i]:
% 0.21/0.58         (~ (r2_hidden @ X5 @ X4) | ((X5) = (X2)) | ((X4) != (k1_tarski @ X2)))),
% 0.21/0.58      inference('cnf', [status(esa)], [d1_tarski])).
% 0.21/0.58  thf('18', plain,
% 0.21/0.58      (![X2 : $i, X5 : $i]:
% 0.21/0.58         (((X5) = (X2)) | ~ (r2_hidden @ X5 @ (k1_tarski @ X2)))),
% 0.21/0.58      inference('simplify', [status(thm)], ['17'])).
% 0.21/0.58  thf('19', plain,
% 0.21/0.58      (((r2_hidden @ sk_A @ (k1_tarski @ sk_B)) | ((sk_B) = (sk_A)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['16', '18'])).
% 0.21/0.58  thf('20', plain, (((sk_A) != (sk_B))),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('21', plain, ((r2_hidden @ sk_A @ (k1_tarski @ sk_B))),
% 0.21/0.58      inference('simplify_reflect-', [status(thm)], ['19', '20'])).
% 0.21/0.58  thf('22', plain,
% 0.21/0.58      (![X2 : $i, X5 : $i]:
% 0.21/0.58         (((X5) = (X2)) | ~ (r2_hidden @ X5 @ (k1_tarski @ X2)))),
% 0.21/0.58      inference('simplify', [status(thm)], ['17'])).
% 0.21/0.58  thf('23', plain, (((sk_A) = (sk_B))),
% 0.21/0.58      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.58  thf('24', plain, (((sk_A) != (sk_B))),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('25', plain, ($false),
% 0.21/0.58      inference('simplify_reflect-', [status(thm)], ['23', '24'])).
% 0.21/0.58  
% 0.21/0.58  % SZS output end Refutation
% 0.21/0.58  
% 0.21/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
