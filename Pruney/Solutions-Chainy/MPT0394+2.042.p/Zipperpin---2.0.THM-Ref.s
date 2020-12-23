%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.bZbg5eiZR9

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:50 EST 2020

% Result     : Theorem 0.41s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :   40 (  74 expanded)
%              Number of leaves         :   16 (  28 expanded)
%              Depth                    :   10
%              Number of atoms          :  248 ( 533 expanded)
%              Number of equality atoms :   38 (  83 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('0',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k2_tarski @ X9 @ X10 )
      = ( k2_xboole_0 @ ( k1_tarski @ X9 ) @ ( k1_tarski @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf(t11_setfam_1,axiom,(
    ! [A: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ A ) )
      = A ) )).

thf('1',plain,(
    ! [X23: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X23 ) )
      = X23 ) ),
    inference(cnf,[status(esa)],[t11_setfam_1])).

thf(t10_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( ( k1_setfam_1 @ ( k2_xboole_0 @ A @ B ) )
         != ( k3_xboole_0 @ ( k1_setfam_1 @ A ) @ ( k1_setfam_1 @ B ) ) ) ) )).

thf('2',plain,(
    ! [X21: $i,X22: $i] :
      ( ( X21 = k1_xboole_0 )
      | ( ( k1_setfam_1 @ ( k2_xboole_0 @ X21 @ X22 ) )
        = ( k3_xboole_0 @ ( k1_setfam_1 @ X21 ) @ ( k1_setfam_1 @ X22 ) ) )
      | ( X22 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t10_setfam_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_setfam_1 @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
        = ( k3_xboole_0 @ X0 @ ( k1_setfam_1 @ X1 ) ) )
      | ( X1 = k1_xboole_0 )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
        = ( k3_xboole_0 @ X1 @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) ) )
      | ( ( k1_tarski @ X1 )
        = k1_xboole_0 )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['0','3'])).

thf('5',plain,(
    ! [X23: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X23 ) )
      = X23 ) ),
    inference(cnf,[status(esa)],[t11_setfam_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ( ( k1_tarski @ X1 )
        = k1_xboole_0 )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(t12_setfam_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
        = ( k3_xboole_0 @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t12_setfam_1])).

thf('7',plain,(
    ( k1_setfam_1 @ ( k2_tarski @ sk_A @ sk_B ) )
 != ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( ( k3_xboole_0 @ sk_A @ sk_B )
     != ( k3_xboole_0 @ sk_A @ sk_B ) )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['8'])).

thf(t16_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        & ( A = B ) ) )).

thf('10',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X19 ) @ ( k1_tarski @ X20 ) )
      | ( X19 != X20 ) ) ),
    inference(cnf,[status(esa)],[t16_zfmisc_1])).

thf('11',plain,(
    ! [X20: $i] :
      ~ ( r1_xboole_0 @ ( k1_tarski @ X20 ) @ ( k1_tarski @ X20 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,
    ( ~ ( r1_xboole_0 @ ( k1_tarski @ sk_B ) @ k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('13',plain,(
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('14',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ( ( k3_xboole_0 @ X0 @ X2 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['12','16'])).

thf('18',plain,(
    ! [X20: $i] :
      ~ ( r1_xboole_0 @ ( k1_tarski @ X20 ) @ ( k1_tarski @ X20 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('19',plain,(
    ~ ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['12','16'])).

thf('21',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['15'])).

thf('22',plain,(
    $false ),
    inference(demod,[status(thm)],['19','20','21'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.bZbg5eiZR9
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:25:49 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.35  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.41/0.58  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.41/0.58  % Solved by: fo/fo7.sh
% 0.41/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.41/0.58  % done 313 iterations in 0.132s
% 0.41/0.58  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.41/0.58  % SZS output start Refutation
% 0.41/0.58  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.41/0.58  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.41/0.58  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.41/0.58  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.41/0.58  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.41/0.58  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.41/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.41/0.58  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.41/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.41/0.58  thf(t41_enumset1, axiom,
% 0.41/0.58    (![A:$i,B:$i]:
% 0.41/0.58     ( ( k2_tarski @ A @ B ) =
% 0.41/0.58       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.41/0.58  thf('0', plain,
% 0.41/0.58      (![X9 : $i, X10 : $i]:
% 0.41/0.58         ((k2_tarski @ X9 @ X10)
% 0.41/0.58           = (k2_xboole_0 @ (k1_tarski @ X9) @ (k1_tarski @ X10)))),
% 0.41/0.58      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.41/0.58  thf(t11_setfam_1, axiom,
% 0.41/0.58    (![A:$i]: ( ( k1_setfam_1 @ ( k1_tarski @ A ) ) = ( A ) ))).
% 0.41/0.58  thf('1', plain, (![X23 : $i]: ((k1_setfam_1 @ (k1_tarski @ X23)) = (X23))),
% 0.41/0.58      inference('cnf', [status(esa)], [t11_setfam_1])).
% 0.41/0.58  thf(t10_setfam_1, axiom,
% 0.41/0.58    (![A:$i,B:$i]:
% 0.41/0.58     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.41/0.58          ( ( k1_setfam_1 @ ( k2_xboole_0 @ A @ B ) ) !=
% 0.41/0.58            ( k3_xboole_0 @ ( k1_setfam_1 @ A ) @ ( k1_setfam_1 @ B ) ) ) ) ))).
% 0.41/0.58  thf('2', plain,
% 0.41/0.58      (![X21 : $i, X22 : $i]:
% 0.41/0.58         (((X21) = (k1_xboole_0))
% 0.41/0.58          | ((k1_setfam_1 @ (k2_xboole_0 @ X21 @ X22))
% 0.41/0.58              = (k3_xboole_0 @ (k1_setfam_1 @ X21) @ (k1_setfam_1 @ X22)))
% 0.41/0.58          | ((X22) = (k1_xboole_0)))),
% 0.41/0.58      inference('cnf', [status(esa)], [t10_setfam_1])).
% 0.41/0.58  thf('3', plain,
% 0.41/0.58      (![X0 : $i, X1 : $i]:
% 0.41/0.58         (((k1_setfam_1 @ (k2_xboole_0 @ (k1_tarski @ X0) @ X1))
% 0.41/0.58            = (k3_xboole_0 @ X0 @ (k1_setfam_1 @ X1)))
% 0.41/0.58          | ((X1) = (k1_xboole_0))
% 0.41/0.58          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.41/0.58      inference('sup+', [status(thm)], ['1', '2'])).
% 0.41/0.58  thf('4', plain,
% 0.41/0.58      (![X0 : $i, X1 : $i]:
% 0.41/0.58         (((k1_setfam_1 @ (k2_tarski @ X1 @ X0))
% 0.41/0.58            = (k3_xboole_0 @ X1 @ (k1_setfam_1 @ (k1_tarski @ X0))))
% 0.41/0.58          | ((k1_tarski @ X1) = (k1_xboole_0))
% 0.41/0.58          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.41/0.58      inference('sup+', [status(thm)], ['0', '3'])).
% 0.41/0.58  thf('5', plain, (![X23 : $i]: ((k1_setfam_1 @ (k1_tarski @ X23)) = (X23))),
% 0.41/0.58      inference('cnf', [status(esa)], [t11_setfam_1])).
% 0.41/0.58  thf('6', plain,
% 0.41/0.58      (![X0 : $i, X1 : $i]:
% 0.41/0.58         (((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X1 @ X0))
% 0.41/0.58          | ((k1_tarski @ X1) = (k1_xboole_0))
% 0.41/0.58          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.41/0.58      inference('demod', [status(thm)], ['4', '5'])).
% 0.41/0.58  thf(t12_setfam_1, conjecture,
% 0.41/0.58    (![A:$i,B:$i]:
% 0.41/0.58     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.41/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.41/0.58    (~( ![A:$i,B:$i]:
% 0.41/0.58        ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ) )),
% 0.41/0.58    inference('cnf.neg', [status(esa)], [t12_setfam_1])).
% 0.41/0.58  thf('7', plain,
% 0.41/0.58      (((k1_setfam_1 @ (k2_tarski @ sk_A @ sk_B))
% 0.41/0.58         != (k3_xboole_0 @ sk_A @ sk_B))),
% 0.41/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.58  thf('8', plain,
% 0.41/0.58      ((((k3_xboole_0 @ sk_A @ sk_B) != (k3_xboole_0 @ sk_A @ sk_B))
% 0.41/0.58        | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.41/0.58        | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.41/0.58      inference('sup-', [status(thm)], ['6', '7'])).
% 0.41/0.58  thf('9', plain,
% 0.41/0.58      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.41/0.58        | ((k1_tarski @ sk_B) = (k1_xboole_0)))),
% 0.41/0.58      inference('simplify', [status(thm)], ['8'])).
% 0.41/0.58  thf(t16_zfmisc_1, axiom,
% 0.41/0.58    (![A:$i,B:$i]:
% 0.41/0.58     ( ~( ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) & 
% 0.41/0.58          ( ( A ) = ( B ) ) ) ))).
% 0.41/0.58  thf('10', plain,
% 0.41/0.58      (![X19 : $i, X20 : $i]:
% 0.41/0.58         (~ (r1_xboole_0 @ (k1_tarski @ X19) @ (k1_tarski @ X20))
% 0.41/0.58          | ((X19) != (X20)))),
% 0.41/0.58      inference('cnf', [status(esa)], [t16_zfmisc_1])).
% 0.41/0.58  thf('11', plain,
% 0.41/0.58      (![X20 : $i]: ~ (r1_xboole_0 @ (k1_tarski @ X20) @ (k1_tarski @ X20))),
% 0.41/0.58      inference('simplify', [status(thm)], ['10'])).
% 0.41/0.58  thf('12', plain,
% 0.41/0.58      ((~ (r1_xboole_0 @ (k1_tarski @ sk_B) @ k1_xboole_0)
% 0.41/0.58        | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.41/0.58      inference('sup-', [status(thm)], ['9', '11'])).
% 0.41/0.58  thf(t2_boole, axiom,
% 0.41/0.58    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.41/0.58  thf('13', plain,
% 0.41/0.58      (![X3 : $i]: ((k3_xboole_0 @ X3 @ k1_xboole_0) = (k1_xboole_0))),
% 0.41/0.58      inference('cnf', [status(esa)], [t2_boole])).
% 0.41/0.58  thf(d7_xboole_0, axiom,
% 0.41/0.58    (![A:$i,B:$i]:
% 0.41/0.58     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.41/0.58       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.41/0.58  thf('14', plain,
% 0.41/0.58      (![X0 : $i, X2 : $i]:
% 0.41/0.58         ((r1_xboole_0 @ X0 @ X2) | ((k3_xboole_0 @ X0 @ X2) != (k1_xboole_0)))),
% 0.41/0.58      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.41/0.58  thf('15', plain,
% 0.41/0.58      (![X0 : $i]:
% 0.41/0.58         (((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.41/0.58      inference('sup-', [status(thm)], ['13', '14'])).
% 0.41/0.58  thf('16', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.41/0.58      inference('simplify', [status(thm)], ['15'])).
% 0.41/0.58  thf('17', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.41/0.58      inference('demod', [status(thm)], ['12', '16'])).
% 0.41/0.58  thf('18', plain,
% 0.41/0.58      (![X20 : $i]: ~ (r1_xboole_0 @ (k1_tarski @ X20) @ (k1_tarski @ X20))),
% 0.41/0.58      inference('simplify', [status(thm)], ['10'])).
% 0.41/0.58  thf('19', plain, (~ (r1_xboole_0 @ (k1_tarski @ sk_A) @ k1_xboole_0)),
% 0.41/0.58      inference('sup-', [status(thm)], ['17', '18'])).
% 0.41/0.58  thf('20', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.41/0.58      inference('demod', [status(thm)], ['12', '16'])).
% 0.41/0.58  thf('21', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.41/0.58      inference('simplify', [status(thm)], ['15'])).
% 0.41/0.58  thf('22', plain, ($false),
% 0.41/0.58      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.41/0.58  
% 0.41/0.58  % SZS output end Refutation
% 0.41/0.58  
% 0.41/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
