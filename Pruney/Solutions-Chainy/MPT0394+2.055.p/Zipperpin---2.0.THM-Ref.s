%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BLr9AL02Oe

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:52 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   40 (  45 expanded)
%              Number of leaves         :   15 (  20 expanded)
%              Depth                    :    9
%              Number of atoms          :  261 ( 292 expanded)
%              Number of equality atoms :   40 (  45 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(t12_setfam_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
        = ( k3_xboole_0 @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t12_setfam_1])).

thf('0',plain,(
    ( k1_setfam_1 @ ( k2_tarski @ sk_A @ sk_B ) )
 != ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('1',plain,(
    ! [X4: $i] :
      ( ( k2_tarski @ X4 @ X4 )
      = ( k1_tarski @ X4 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('2',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k2_tarski @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k1_tarski @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t11_setfam_1,axiom,(
    ! [A: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ A ) )
      = A ) )).

thf('4',plain,(
    ! [X10: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X10 ) )
      = X10 ) ),
    inference(cnf,[status(esa)],[t11_setfam_1])).

thf(t10_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( ( k1_setfam_1 @ ( k2_xboole_0 @ A @ B ) )
         != ( k3_xboole_0 @ ( k1_setfam_1 @ A ) @ ( k1_setfam_1 @ B ) ) ) ) )).

thf('5',plain,(
    ! [X8: $i,X9: $i] :
      ( ( X8 = k1_xboole_0 )
      | ( ( k1_setfam_1 @ ( k2_xboole_0 @ X8 @ X9 ) )
        = ( k3_xboole_0 @ ( k1_setfam_1 @ X8 ) @ ( k1_setfam_1 @ X9 ) ) )
      | ( X9 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t10_setfam_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_setfam_1 @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
        = ( k3_xboole_0 @ X0 @ ( k1_setfam_1 @ X1 ) ) )
      | ( X1 = k1_xboole_0 )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = A ) )).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('8',plain,(
    ! [X4: $i] :
      ( ( k2_tarski @ X4 @ X4 )
      = ( k1_tarski @ X4 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t50_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
     != k1_xboole_0 ) )).

thf('9',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X5 @ X6 ) @ X7 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t50_zfmisc_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_setfam_1 @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
        = ( k3_xboole_0 @ X0 @ ( k1_setfam_1 @ X1 ) ) )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['6','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
        = ( k3_xboole_0 @ X1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X0 ) ) ) )
      | ( ( k2_tarski @ X0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['3','12'])).

thf('14',plain,(
    ! [X4: $i] :
      ( ( k2_tarski @ X4 @ X4 )
      = ( k1_tarski @ X4 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('15',plain,(
    ! [X10: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X10 ) )
      = X10 ) ),
    inference(cnf,[status(esa)],[t11_setfam_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X0 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ( ( k2_tarski @ X0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('19',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X5 @ X6 ) @ X7 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t50_zfmisc_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['17','20'])).

thf('22',plain,(
    ( k3_xboole_0 @ sk_A @ sk_B )
 != ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','21'])).

thf('23',plain,(
    $false ),
    inference(simplify,[status(thm)],['22'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.16  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.17  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BLr9AL02Oe
% 0.17/0.37  % Computer   : n011.cluster.edu
% 0.17/0.37  % Model      : x86_64 x86_64
% 0.17/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.17/0.37  % Memory     : 8042.1875MB
% 0.17/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.17/0.37  % CPULimit   : 60
% 0.17/0.37  % DateTime   : Tue Dec  1 14:54:12 EST 2020
% 0.17/0.38  % CPUTime    : 
% 0.17/0.38  % Running portfolio for 600 s
% 0.17/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.17/0.38  % Number of cores: 8
% 0.17/0.38  % Python version: Python 3.6.8
% 0.17/0.38  % Running in FO mode
% 0.23/0.46  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.46  % Solved by: fo/fo7.sh
% 0.23/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.46  % done 29 iterations in 0.010s
% 0.23/0.46  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.46  % SZS output start Refutation
% 0.23/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.23/0.46  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.23/0.46  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.23/0.46  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.23/0.46  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.23/0.46  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.23/0.46  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.23/0.46  thf(t12_setfam_1, conjecture,
% 0.23/0.46    (![A:$i,B:$i]:
% 0.23/0.46     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.23/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.46    (~( ![A:$i,B:$i]:
% 0.23/0.46        ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ) )),
% 0.23/0.46    inference('cnf.neg', [status(esa)], [t12_setfam_1])).
% 0.23/0.46  thf('0', plain,
% 0.23/0.46      (((k1_setfam_1 @ (k2_tarski @ sk_A @ sk_B))
% 0.23/0.46         != (k3_xboole_0 @ sk_A @ sk_B))),
% 0.23/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.46  thf(t69_enumset1, axiom,
% 0.23/0.46    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.23/0.46  thf('1', plain, (![X4 : $i]: ((k2_tarski @ X4 @ X4) = (k1_tarski @ X4))),
% 0.23/0.46      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.23/0.46  thf(t41_enumset1, axiom,
% 0.23/0.46    (![A:$i,B:$i]:
% 0.23/0.46     ( ( k2_tarski @ A @ B ) =
% 0.23/0.46       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.23/0.46  thf('2', plain,
% 0.23/0.46      (![X2 : $i, X3 : $i]:
% 0.23/0.46         ((k2_tarski @ X2 @ X3)
% 0.23/0.46           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k1_tarski @ X3)))),
% 0.23/0.46      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.23/0.46  thf('3', plain,
% 0.23/0.46      (![X0 : $i, X1 : $i]:
% 0.23/0.46         ((k2_tarski @ X1 @ X0)
% 0.23/0.46           = (k2_xboole_0 @ (k1_tarski @ X1) @ (k2_tarski @ X0 @ X0)))),
% 0.23/0.46      inference('sup+', [status(thm)], ['1', '2'])).
% 0.23/0.46  thf(t11_setfam_1, axiom,
% 0.23/0.46    (![A:$i]: ( ( k1_setfam_1 @ ( k1_tarski @ A ) ) = ( A ) ))).
% 0.23/0.46  thf('4', plain, (![X10 : $i]: ((k1_setfam_1 @ (k1_tarski @ X10)) = (X10))),
% 0.23/0.46      inference('cnf', [status(esa)], [t11_setfam_1])).
% 0.23/0.46  thf(t10_setfam_1, axiom,
% 0.23/0.46    (![A:$i,B:$i]:
% 0.23/0.46     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.23/0.46          ( ( k1_setfam_1 @ ( k2_xboole_0 @ A @ B ) ) !=
% 0.23/0.46            ( k3_xboole_0 @ ( k1_setfam_1 @ A ) @ ( k1_setfam_1 @ B ) ) ) ) ))).
% 0.23/0.46  thf('5', plain,
% 0.23/0.46      (![X8 : $i, X9 : $i]:
% 0.23/0.46         (((X8) = (k1_xboole_0))
% 0.23/0.46          | ((k1_setfam_1 @ (k2_xboole_0 @ X8 @ X9))
% 0.23/0.46              = (k3_xboole_0 @ (k1_setfam_1 @ X8) @ (k1_setfam_1 @ X9)))
% 0.23/0.46          | ((X9) = (k1_xboole_0)))),
% 0.23/0.46      inference('cnf', [status(esa)], [t10_setfam_1])).
% 0.23/0.46  thf('6', plain,
% 0.23/0.46      (![X0 : $i, X1 : $i]:
% 0.23/0.46         (((k1_setfam_1 @ (k2_xboole_0 @ (k1_tarski @ X0) @ X1))
% 0.23/0.46            = (k3_xboole_0 @ X0 @ (k1_setfam_1 @ X1)))
% 0.23/0.46          | ((X1) = (k1_xboole_0))
% 0.23/0.46          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.23/0.46      inference('sup+', [status(thm)], ['4', '5'])).
% 0.23/0.46  thf(t22_xboole_1, axiom,
% 0.23/0.46    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.23/0.46  thf('7', plain,
% 0.23/0.46      (![X0 : $i, X1 : $i]:
% 0.23/0.46         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)) = (X0))),
% 0.23/0.46      inference('cnf', [status(esa)], [t22_xboole_1])).
% 0.23/0.46  thf('8', plain, (![X4 : $i]: ((k2_tarski @ X4 @ X4) = (k1_tarski @ X4))),
% 0.23/0.46      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.23/0.46  thf(t50_zfmisc_1, axiom,
% 0.23/0.46    (![A:$i,B:$i,C:$i]:
% 0.23/0.46     ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) != ( k1_xboole_0 ) ))).
% 0.23/0.46  thf('9', plain,
% 0.23/0.46      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.23/0.46         ((k2_xboole_0 @ (k2_tarski @ X5 @ X6) @ X7) != (k1_xboole_0))),
% 0.23/0.46      inference('cnf', [status(esa)], [t50_zfmisc_1])).
% 0.23/0.46  thf('10', plain,
% 0.23/0.46      (![X0 : $i, X1 : $i]:
% 0.23/0.46         ((k2_xboole_0 @ (k1_tarski @ X0) @ X1) != (k1_xboole_0))),
% 0.23/0.46      inference('sup-', [status(thm)], ['8', '9'])).
% 0.23/0.46  thf('11', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 0.23/0.46      inference('sup-', [status(thm)], ['7', '10'])).
% 0.23/0.46  thf('12', plain,
% 0.23/0.46      (![X0 : $i, X1 : $i]:
% 0.23/0.46         (((k1_setfam_1 @ (k2_xboole_0 @ (k1_tarski @ X0) @ X1))
% 0.23/0.46            = (k3_xboole_0 @ X0 @ (k1_setfam_1 @ X1)))
% 0.23/0.46          | ((X1) = (k1_xboole_0)))),
% 0.23/0.46      inference('simplify_reflect-', [status(thm)], ['6', '11'])).
% 0.23/0.46  thf('13', plain,
% 0.23/0.46      (![X0 : $i, X1 : $i]:
% 0.23/0.46         (((k1_setfam_1 @ (k2_tarski @ X1 @ X0))
% 0.23/0.46            = (k3_xboole_0 @ X1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X0))))
% 0.23/0.46          | ((k2_tarski @ X0 @ X0) = (k1_xboole_0)))),
% 0.23/0.46      inference('sup+', [status(thm)], ['3', '12'])).
% 0.23/0.46  thf('14', plain, (![X4 : $i]: ((k2_tarski @ X4 @ X4) = (k1_tarski @ X4))),
% 0.23/0.46      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.23/0.46  thf('15', plain, (![X10 : $i]: ((k1_setfam_1 @ (k1_tarski @ X10)) = (X10))),
% 0.23/0.46      inference('cnf', [status(esa)], [t11_setfam_1])).
% 0.23/0.46  thf('16', plain,
% 0.23/0.46      (![X0 : $i]: ((k1_setfam_1 @ (k2_tarski @ X0 @ X0)) = (X0))),
% 0.23/0.46      inference('sup+', [status(thm)], ['14', '15'])).
% 0.23/0.46  thf('17', plain,
% 0.23/0.46      (![X0 : $i, X1 : $i]:
% 0.23/0.46         (((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X1 @ X0))
% 0.23/0.46          | ((k2_tarski @ X0 @ X0) = (k1_xboole_0)))),
% 0.23/0.46      inference('demod', [status(thm)], ['13', '16'])).
% 0.23/0.46  thf('18', plain,
% 0.23/0.46      (![X0 : $i, X1 : $i]:
% 0.23/0.46         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)) = (X0))),
% 0.23/0.46      inference('cnf', [status(esa)], [t22_xboole_1])).
% 0.23/0.46  thf('19', plain,
% 0.23/0.46      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.23/0.46         ((k2_xboole_0 @ (k2_tarski @ X5 @ X6) @ X7) != (k1_xboole_0))),
% 0.23/0.46      inference('cnf', [status(esa)], [t50_zfmisc_1])).
% 0.23/0.46  thf('20', plain,
% 0.23/0.46      (![X0 : $i, X1 : $i]: ((k2_tarski @ X1 @ X0) != (k1_xboole_0))),
% 0.23/0.46      inference('sup-', [status(thm)], ['18', '19'])).
% 0.23/0.46  thf('21', plain,
% 0.23/0.46      (![X0 : $i, X1 : $i]:
% 0.23/0.46         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X1 @ X0))),
% 0.23/0.46      inference('simplify_reflect-', [status(thm)], ['17', '20'])).
% 0.23/0.46  thf('22', plain,
% 0.23/0.46      (((k3_xboole_0 @ sk_A @ sk_B) != (k3_xboole_0 @ sk_A @ sk_B))),
% 0.23/0.46      inference('demod', [status(thm)], ['0', '21'])).
% 0.23/0.46  thf('23', plain, ($false), inference('simplify', [status(thm)], ['22'])).
% 0.23/0.46  
% 0.23/0.46  % SZS output end Refutation
% 0.23/0.46  
% 0.23/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
