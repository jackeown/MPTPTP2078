%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.PMWv5RjEP0

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:52 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :   48 (  56 expanded)
%              Number of leaves         :   19 (  24 expanded)
%              Depth                    :   11
%              Number of atoms          :  287 ( 348 expanded)
%              Number of equality atoms :   32 (  43 expanded)
%              Maximal formula depth    :    9 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('0',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( X20 != X19 )
      | ( r2_hidden @ X20 @ X21 )
      | ( X21
       != ( k1_tarski @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('1',plain,(
    ! [X19: $i] :
      ( r2_hidden @ X19 @ ( k1_tarski @ X19 ) ) ),
    inference(simplify,[status(thm)],['0'])).

thf(t1_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) )
    <=> ~ ( ( r2_hidden @ A @ B )
        <=> ( r2_hidden @ A @ C ) ) ) )).

thf('2',plain,(
    ! [X2: $i,X3: $i,X5: $i] :
      ( ( r2_hidden @ X2 @ ( k5_xboole_0 @ X3 @ X5 ) )
      | ( r2_hidden @ X2 @ X5 )
      | ~ ( r2_hidden @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ ( k5_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t21_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = k1_xboole_0 )
     => ( A = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
          = k1_xboole_0 )
       => ( A = B ) ) ),
    inference('cnf.neg',[status(esa)],[t21_zfmisc_1])).

thf('4',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('5',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('6',plain,(
    ! [X14: $i] :
      ( ( k5_xboole_0 @ X14 @ X14 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('7',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k5_xboole_0 @ X11 @ ( k5_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('10',plain,(
    ! [X10: $i] :
      ( ( k5_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['8','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['5','12'])).

thf('14',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['4','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('17',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf(l97_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k5_xboole_0 @ A @ B ) ) )).

thf('18',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X6 @ X7 ) @ ( k5_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l97_xboole_1])).

thf('19',plain,(
    r1_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf(l24_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B )
        & ( r2_hidden @ A @ B ) ) )).

thf('20',plain,(
    ! [X38: $i,X39: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X38 ) @ X39 )
      | ~ ( r2_hidden @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[l24_zfmisc_1])).

thf('21',plain,(
    ~ ( r2_hidden @ sk_A @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['3','21'])).

thf('23',plain,(
    ! [X19: $i,X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ X22 @ X21 )
      | ( X22 = X19 )
      | ( X21
       != ( k1_tarski @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('24',plain,(
    ! [X19: $i,X22: $i] :
      ( ( X22 = X19 )
      | ~ ( r2_hidden @ X22 @ ( k1_tarski @ X19 ) ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    sk_A = sk_B ),
    inference('sup-',[status(thm)],['22','24'])).

thf('26',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['25','26'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.PMWv5RjEP0
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:50:32 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.19/0.35  % Number of cores: 8
% 0.19/0.35  % Python version: Python 3.6.8
% 0.19/0.35  % Running in FO mode
% 0.40/0.58  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.40/0.58  % Solved by: fo/fo7.sh
% 0.40/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.40/0.58  % done 221 iterations in 0.132s
% 0.40/0.58  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.40/0.58  % SZS output start Refutation
% 0.40/0.58  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.40/0.58  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.40/0.58  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.40/0.58  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.40/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.40/0.58  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.40/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.40/0.58  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.40/0.58  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.40/0.58  thf(d1_tarski, axiom,
% 0.40/0.58    (![A:$i,B:$i]:
% 0.40/0.58     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.40/0.58       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.40/0.58  thf('0', plain,
% 0.40/0.58      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.40/0.58         (((X20) != (X19))
% 0.40/0.58          | (r2_hidden @ X20 @ X21)
% 0.40/0.58          | ((X21) != (k1_tarski @ X19)))),
% 0.40/0.58      inference('cnf', [status(esa)], [d1_tarski])).
% 0.40/0.58  thf('1', plain, (![X19 : $i]: (r2_hidden @ X19 @ (k1_tarski @ X19))),
% 0.40/0.58      inference('simplify', [status(thm)], ['0'])).
% 0.40/0.58  thf(t1_xboole_0, axiom,
% 0.40/0.58    (![A:$i,B:$i,C:$i]:
% 0.40/0.58     ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 0.40/0.58       ( ~( ( r2_hidden @ A @ B ) <=> ( r2_hidden @ A @ C ) ) ) ))).
% 0.40/0.58  thf('2', plain,
% 0.40/0.58      (![X2 : $i, X3 : $i, X5 : $i]:
% 0.40/0.58         ((r2_hidden @ X2 @ (k5_xboole_0 @ X3 @ X5))
% 0.40/0.58          | (r2_hidden @ X2 @ X5)
% 0.40/0.58          | ~ (r2_hidden @ X2 @ X3))),
% 0.40/0.58      inference('cnf', [status(esa)], [t1_xboole_0])).
% 0.40/0.58  thf('3', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i]:
% 0.40/0.58         ((r2_hidden @ X0 @ X1)
% 0.40/0.58          | (r2_hidden @ X0 @ (k5_xboole_0 @ (k1_tarski @ X0) @ X1)))),
% 0.40/0.58      inference('sup-', [status(thm)], ['1', '2'])).
% 0.40/0.58  thf(t21_zfmisc_1, conjecture,
% 0.40/0.58    (![A:$i,B:$i]:
% 0.40/0.58     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.40/0.58         ( k1_xboole_0 ) ) =>
% 0.40/0.58       ( ( A ) = ( B ) ) ))).
% 0.40/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.40/0.58    (~( ![A:$i,B:$i]:
% 0.40/0.58        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.40/0.58            ( k1_xboole_0 ) ) =>
% 0.40/0.58          ( ( A ) = ( B ) ) ) )),
% 0.40/0.58    inference('cnf.neg', [status(esa)], [t21_zfmisc_1])).
% 0.40/0.58  thf('4', plain,
% 0.40/0.58      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)) = (k1_xboole_0))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf(t100_xboole_1, axiom,
% 0.40/0.58    (![A:$i,B:$i]:
% 0.40/0.58     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.40/0.58  thf('5', plain,
% 0.40/0.58      (![X8 : $i, X9 : $i]:
% 0.40/0.58         ((k4_xboole_0 @ X8 @ X9)
% 0.40/0.58           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.40/0.58      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.40/0.58  thf(t92_xboole_1, axiom,
% 0.40/0.58    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.40/0.58  thf('6', plain, (![X14 : $i]: ((k5_xboole_0 @ X14 @ X14) = (k1_xboole_0))),
% 0.40/0.58      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.40/0.58  thf(t91_xboole_1, axiom,
% 0.40/0.58    (![A:$i,B:$i,C:$i]:
% 0.40/0.58     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.40/0.58       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.40/0.58  thf('7', plain,
% 0.40/0.58      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.40/0.58         ((k5_xboole_0 @ (k5_xboole_0 @ X11 @ X12) @ X13)
% 0.40/0.58           = (k5_xboole_0 @ X11 @ (k5_xboole_0 @ X12 @ X13)))),
% 0.40/0.58      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.40/0.58  thf('8', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i]:
% 0.40/0.58         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.40/0.58           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.40/0.58      inference('sup+', [status(thm)], ['6', '7'])).
% 0.40/0.58  thf(commutativity_k5_xboole_0, axiom,
% 0.40/0.58    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.40/0.58  thf('9', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.40/0.58      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.40/0.58  thf(t5_boole, axiom,
% 0.40/0.58    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.40/0.58  thf('10', plain, (![X10 : $i]: ((k5_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 0.40/0.58      inference('cnf', [status(esa)], [t5_boole])).
% 0.40/0.58  thf('11', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.40/0.58      inference('sup+', [status(thm)], ['9', '10'])).
% 0.40/0.58  thf('12', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i]:
% 0.40/0.58         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.40/0.58      inference('demod', [status(thm)], ['8', '11'])).
% 0.40/0.58  thf('13', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i]:
% 0.40/0.58         ((k3_xboole_0 @ X1 @ X0)
% 0.40/0.58           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.40/0.58      inference('sup+', [status(thm)], ['5', '12'])).
% 0.40/0.58  thf('14', plain,
% 0.40/0.58      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.40/0.58         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ k1_xboole_0))),
% 0.40/0.58      inference('sup+', [status(thm)], ['4', '13'])).
% 0.40/0.58  thf('15', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.40/0.58      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.40/0.58  thf('16', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.40/0.58      inference('sup+', [status(thm)], ['9', '10'])).
% 0.40/0.58  thf('17', plain,
% 0.40/0.58      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.40/0.58         = (k1_tarski @ sk_A))),
% 0.40/0.58      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.40/0.58  thf(l97_xboole_1, axiom,
% 0.40/0.58    (![A:$i,B:$i]:
% 0.40/0.58     ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k5_xboole_0 @ A @ B ) ))).
% 0.40/0.58  thf('18', plain,
% 0.40/0.58      (![X6 : $i, X7 : $i]:
% 0.40/0.58         (r1_xboole_0 @ (k3_xboole_0 @ X6 @ X7) @ (k5_xboole_0 @ X6 @ X7))),
% 0.40/0.58      inference('cnf', [status(esa)], [l97_xboole_1])).
% 0.40/0.58  thf('19', plain,
% 0.40/0.58      ((r1_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.40/0.58        (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)))),
% 0.40/0.58      inference('sup+', [status(thm)], ['17', '18'])).
% 0.40/0.58  thf(l24_zfmisc_1, axiom,
% 0.40/0.58    (![A:$i,B:$i]:
% 0.40/0.58     ( ~( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) & ( r2_hidden @ A @ B ) ) ))).
% 0.40/0.58  thf('20', plain,
% 0.40/0.58      (![X38 : $i, X39 : $i]:
% 0.40/0.58         (~ (r1_xboole_0 @ (k1_tarski @ X38) @ X39) | ~ (r2_hidden @ X38 @ X39))),
% 0.40/0.58      inference('cnf', [status(esa)], [l24_zfmisc_1])).
% 0.40/0.58  thf('21', plain,
% 0.40/0.58      (~ (r2_hidden @ sk_A @ 
% 0.40/0.58          (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)))),
% 0.40/0.58      inference('sup-', [status(thm)], ['19', '20'])).
% 0.40/0.58  thf('22', plain, ((r2_hidden @ sk_A @ (k1_tarski @ sk_B))),
% 0.40/0.58      inference('sup-', [status(thm)], ['3', '21'])).
% 0.40/0.58  thf('23', plain,
% 0.40/0.58      (![X19 : $i, X21 : $i, X22 : $i]:
% 0.40/0.58         (~ (r2_hidden @ X22 @ X21)
% 0.40/0.58          | ((X22) = (X19))
% 0.40/0.58          | ((X21) != (k1_tarski @ X19)))),
% 0.40/0.58      inference('cnf', [status(esa)], [d1_tarski])).
% 0.40/0.58  thf('24', plain,
% 0.40/0.58      (![X19 : $i, X22 : $i]:
% 0.40/0.58         (((X22) = (X19)) | ~ (r2_hidden @ X22 @ (k1_tarski @ X19)))),
% 0.40/0.58      inference('simplify', [status(thm)], ['23'])).
% 0.40/0.58  thf('25', plain, (((sk_A) = (sk_B))),
% 0.40/0.58      inference('sup-', [status(thm)], ['22', '24'])).
% 0.40/0.58  thf('26', plain, (((sk_A) != (sk_B))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('27', plain, ($false),
% 0.40/0.58      inference('simplify_reflect-', [status(thm)], ['25', '26'])).
% 0.40/0.58  
% 0.40/0.58  % SZS output end Refutation
% 0.40/0.58  
% 0.40/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
