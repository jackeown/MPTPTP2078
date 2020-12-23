%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.NOMggH0BdZ

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:43 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :   38 (  40 expanded)
%              Number of leaves         :   16 (  18 expanded)
%              Depth                    :    8
%              Number of atoms          :  235 ( 253 expanded)
%              Number of equality atoms :   17 (  19 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t19_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) )
      = ( k1_tarski @ A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) )
        = ( k1_tarski @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t19_zfmisc_1])).

thf('0',plain,(
    ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_A @ sk_B ) )
 != ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t77_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_enumset1 @ A @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('1',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k2_enumset1 @ X21 @ X21 @ X21 @ X22 )
      = ( k2_tarski @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t77_enumset1])).

thf(t45_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ) )).

thf('2',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( k2_enumset1 @ X17 @ X18 @ X19 @ X20 )
      = ( k2_xboole_0 @ ( k2_tarski @ X17 @ X18 ) @ ( k2_tarski @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t45_enumset1])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_tarski @ X15 @ ( k2_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( r1_tarski @ ( k2_tarski @ X3 @ X2 ) @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_tarski @ X1 @ X1 ) @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','4'])).

thf('6',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k2_enumset1 @ X21 @ X21 @ X21 @ X22 )
      = ( k2_tarski @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t77_enumset1])).

thf(t82_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_enumset1 @ A @ A @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('7',plain,(
    ! [X23: $i] :
      ( ( k2_enumset1 @ X23 @ X23 @ X23 @ X23 )
      = ( k1_tarski @ X23 ) ) ),
    inference(cnf,[status(esa)],[t82_enumset1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['5','8'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('10',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('11',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['10'])).

thf(t19_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('12',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r1_tarski @ X9 @ X10 )
      | ~ ( r1_tarski @ X9 @ X11 )
      | ( r1_tarski @ X9 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_tarski @ X1 ) @ ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['9','13'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('15',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X7 @ X8 ) @ X7 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('16',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_tarski @ X1 )
      = ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,(
    ( k1_tarski @ sk_A )
 != ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['0','18'])).

thf('20',plain,(
    $false ),
    inference(simplify,[status(thm)],['19'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.NOMggH0BdZ
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:31:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.40/0.60  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.40/0.60  % Solved by: fo/fo7.sh
% 0.40/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.40/0.60  % done 151 iterations in 0.110s
% 0.40/0.60  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.40/0.60  % SZS output start Refutation
% 0.40/0.60  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.40/0.60  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.40/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.40/0.60  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.40/0.60  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.40/0.60  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.40/0.60  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.40/0.60  thf(sk_B_type, type, sk_B: $i).
% 0.40/0.60  thf(t19_zfmisc_1, conjecture,
% 0.40/0.60    (![A:$i,B:$i]:
% 0.40/0.60     ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) =
% 0.40/0.60       ( k1_tarski @ A ) ))).
% 0.40/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.40/0.60    (~( ![A:$i,B:$i]:
% 0.40/0.60        ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) =
% 0.40/0.60          ( k1_tarski @ A ) ) )),
% 0.40/0.60    inference('cnf.neg', [status(esa)], [t19_zfmisc_1])).
% 0.40/0.60  thf('0', plain,
% 0.40/0.60      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_A @ sk_B))
% 0.40/0.60         != (k1_tarski @ sk_A))),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf(t77_enumset1, axiom,
% 0.40/0.60    (![A:$i,B:$i]: ( ( k2_enumset1 @ A @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.40/0.60  thf('1', plain,
% 0.40/0.60      (![X21 : $i, X22 : $i]:
% 0.40/0.60         ((k2_enumset1 @ X21 @ X21 @ X21 @ X22) = (k2_tarski @ X21 @ X22))),
% 0.40/0.60      inference('cnf', [status(esa)], [t77_enumset1])).
% 0.40/0.60  thf(t45_enumset1, axiom,
% 0.40/0.60    (![A:$i,B:$i,C:$i,D:$i]:
% 0.40/0.60     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.40/0.60       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ))).
% 0.40/0.60  thf('2', plain,
% 0.40/0.60      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.40/0.60         ((k2_enumset1 @ X17 @ X18 @ X19 @ X20)
% 0.40/0.60           = (k2_xboole_0 @ (k2_tarski @ X17 @ X18) @ (k2_tarski @ X19 @ X20)))),
% 0.40/0.60      inference('cnf', [status(esa)], [t45_enumset1])).
% 0.40/0.60  thf(t7_xboole_1, axiom,
% 0.40/0.60    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.40/0.60  thf('3', plain,
% 0.40/0.60      (![X15 : $i, X16 : $i]: (r1_tarski @ X15 @ (k2_xboole_0 @ X15 @ X16))),
% 0.40/0.60      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.40/0.60  thf('4', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.40/0.60         (r1_tarski @ (k2_tarski @ X3 @ X2) @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.40/0.60      inference('sup+', [status(thm)], ['2', '3'])).
% 0.40/0.60  thf('5', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i]:
% 0.40/0.60         (r1_tarski @ (k2_tarski @ X1 @ X1) @ (k2_tarski @ X1 @ X0))),
% 0.40/0.60      inference('sup+', [status(thm)], ['1', '4'])).
% 0.40/0.60  thf('6', plain,
% 0.40/0.60      (![X21 : $i, X22 : $i]:
% 0.40/0.60         ((k2_enumset1 @ X21 @ X21 @ X21 @ X22) = (k2_tarski @ X21 @ X22))),
% 0.40/0.60      inference('cnf', [status(esa)], [t77_enumset1])).
% 0.40/0.60  thf(t82_enumset1, axiom,
% 0.40/0.60    (![A:$i]: ( ( k2_enumset1 @ A @ A @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.40/0.60  thf('7', plain,
% 0.40/0.60      (![X23 : $i]: ((k2_enumset1 @ X23 @ X23 @ X23 @ X23) = (k1_tarski @ X23))),
% 0.40/0.60      inference('cnf', [status(esa)], [t82_enumset1])).
% 0.40/0.60  thf('8', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 0.40/0.60      inference('sup+', [status(thm)], ['6', '7'])).
% 0.40/0.60  thf('9', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i]:
% 0.40/0.60         (r1_tarski @ (k1_tarski @ X1) @ (k2_tarski @ X1 @ X0))),
% 0.40/0.60      inference('demod', [status(thm)], ['5', '8'])).
% 0.40/0.60  thf(d10_xboole_0, axiom,
% 0.40/0.60    (![A:$i,B:$i]:
% 0.40/0.60     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.40/0.60  thf('10', plain,
% 0.40/0.60      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 0.40/0.60      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.40/0.60  thf('11', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.40/0.60      inference('simplify', [status(thm)], ['10'])).
% 0.40/0.60  thf(t19_xboole_1, axiom,
% 0.40/0.60    (![A:$i,B:$i,C:$i]:
% 0.40/0.60     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 0.40/0.60       ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 0.40/0.60  thf('12', plain,
% 0.40/0.60      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.40/0.60         (~ (r1_tarski @ X9 @ X10)
% 0.40/0.60          | ~ (r1_tarski @ X9 @ X11)
% 0.40/0.60          | (r1_tarski @ X9 @ (k3_xboole_0 @ X10 @ X11)))),
% 0.40/0.60      inference('cnf', [status(esa)], [t19_xboole_1])).
% 0.40/0.60  thf('13', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i]:
% 0.40/0.60         ((r1_tarski @ X0 @ (k3_xboole_0 @ X0 @ X1)) | ~ (r1_tarski @ X0 @ X1))),
% 0.40/0.60      inference('sup-', [status(thm)], ['11', '12'])).
% 0.40/0.60  thf('14', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i]:
% 0.40/0.60         (r1_tarski @ (k1_tarski @ X1) @ 
% 0.40/0.60          (k3_xboole_0 @ (k1_tarski @ X1) @ (k2_tarski @ X1 @ X0)))),
% 0.40/0.60      inference('sup-', [status(thm)], ['9', '13'])).
% 0.40/0.60  thf(t17_xboole_1, axiom,
% 0.40/0.60    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.40/0.60  thf('15', plain,
% 0.40/0.60      (![X7 : $i, X8 : $i]: (r1_tarski @ (k3_xboole_0 @ X7 @ X8) @ X7)),
% 0.40/0.60      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.40/0.60  thf('16', plain,
% 0.40/0.60      (![X4 : $i, X6 : $i]:
% 0.40/0.60         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.40/0.60      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.40/0.60  thf('17', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i]:
% 0.40/0.60         (~ (r1_tarski @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 0.40/0.60          | ((X0) = (k3_xboole_0 @ X0 @ X1)))),
% 0.40/0.60      inference('sup-', [status(thm)], ['15', '16'])).
% 0.40/0.60  thf('18', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i]:
% 0.40/0.60         ((k1_tarski @ X1)
% 0.40/0.60           = (k3_xboole_0 @ (k1_tarski @ X1) @ (k2_tarski @ X1 @ X0)))),
% 0.40/0.60      inference('sup-', [status(thm)], ['14', '17'])).
% 0.40/0.60  thf('19', plain, (((k1_tarski @ sk_A) != (k1_tarski @ sk_A))),
% 0.40/0.60      inference('demod', [status(thm)], ['0', '18'])).
% 0.40/0.60  thf('20', plain, ($false), inference('simplify', [status(thm)], ['19'])).
% 0.40/0.60  
% 0.40/0.60  % SZS output end Refutation
% 0.40/0.60  
% 0.40/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
