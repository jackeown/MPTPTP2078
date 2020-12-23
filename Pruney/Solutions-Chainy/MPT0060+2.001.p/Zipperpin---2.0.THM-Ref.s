%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.br3mgLYb4o

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:21 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :   38 (  41 expanded)
%              Number of leaves         :   16 (  19 expanded)
%              Depth                    :    7
%              Number of atoms          :  282 ( 315 expanded)
%              Number of equality atoms :   27 (  30 expanded)
%              Maximal formula depth    :   11 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(t53_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
        = ( k3_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t53_xboole_1])).

thf('0',plain,(
    ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
 != ( k3_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ ( k4_xboole_0 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('1',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k3_xboole_0 @ X11 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X11 @ X12 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('2',plain,(
    ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
 != ( k4_xboole_0 @ ( k3_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_A ) @ sk_C ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X14: $i,X15: $i] :
      ( r1_tarski @ X14 @ ( k2_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('5',plain,(
    ! [X2: $i,X4: $i] :
      ( ( ( k4_xboole_0 @ X2 @ X4 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['3','6'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('8',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('9',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X6 @ X7 ) @ X8 )
      = ( k4_xboole_0 @ X6 @ ( k2_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X6 @ X7 ) @ X8 )
      = ( k4_xboole_0 @ X6 @ ( k2_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['7','12'])).

thf('14',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X6 @ X7 ) @ X8 )
      = ( k4_xboole_0 @ X6 @ ( k2_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('15',plain,(
    ! [X5: $i] :
      ( ( k4_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X6 @ X7 ) @ X8 )
      = ( k4_xboole_0 @ X6 @ ( k2_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('19',plain,(
    ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
 != ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['2','17','18'])).

thf('20',plain,(
    $false ),
    inference(simplify,[status(thm)],['19'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.br3mgLYb4o
% 0.14/0.33  % Computer   : n021.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 10:04:34 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.14/0.33  % Running portfolio for 600 s
% 0.14/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.34  % Running in FO mode
% 0.40/0.59  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.40/0.59  % Solved by: fo/fo7.sh
% 0.40/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.40/0.59  % done 313 iterations in 0.156s
% 0.40/0.59  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.40/0.59  % SZS output start Refutation
% 0.40/0.59  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.40/0.59  thf(sk_C_type, type, sk_C: $i).
% 0.40/0.59  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.40/0.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.40/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.40/0.59  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.40/0.59  thf(sk_B_type, type, sk_B: $i).
% 0.40/0.59  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.40/0.59  thf(t53_xboole_1, conjecture,
% 0.40/0.59    (![A:$i,B:$i,C:$i]:
% 0.40/0.59     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) =
% 0.40/0.59       ( k3_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ C ) ) ))).
% 0.40/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.40/0.59    (~( ![A:$i,B:$i,C:$i]:
% 0.40/0.59        ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) =
% 0.40/0.59          ( k3_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ C ) ) ) )),
% 0.40/0.59    inference('cnf.neg', [status(esa)], [t53_xboole_1])).
% 0.40/0.59  thf('0', plain,
% 0.40/0.59      (((k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))
% 0.40/0.59         != (k3_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ 
% 0.40/0.59             (k4_xboole_0 @ sk_A @ sk_C)))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf(t49_xboole_1, axiom,
% 0.40/0.59    (![A:$i,B:$i,C:$i]:
% 0.40/0.59     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.40/0.59       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 0.40/0.59  thf('1', plain,
% 0.40/0.59      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.40/0.59         ((k3_xboole_0 @ X11 @ (k4_xboole_0 @ X12 @ X13))
% 0.40/0.59           = (k4_xboole_0 @ (k3_xboole_0 @ X11 @ X12) @ X13))),
% 0.40/0.59      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.40/0.59  thf('2', plain,
% 0.40/0.59      (((k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))
% 0.40/0.59         != (k4_xboole_0 @ 
% 0.40/0.59             (k3_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_A) @ sk_C))),
% 0.40/0.59      inference('demod', [status(thm)], ['0', '1'])).
% 0.40/0.59  thf(commutativity_k2_xboole_0, axiom,
% 0.40/0.59    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.40/0.59  thf('3', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.40/0.59      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.40/0.59  thf(t7_xboole_1, axiom,
% 0.40/0.59    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.40/0.59  thf('4', plain,
% 0.40/0.59      (![X14 : $i, X15 : $i]: (r1_tarski @ X14 @ (k2_xboole_0 @ X14 @ X15))),
% 0.40/0.59      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.40/0.59  thf(l32_xboole_1, axiom,
% 0.40/0.59    (![A:$i,B:$i]:
% 0.40/0.59     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.40/0.59  thf('5', plain,
% 0.40/0.59      (![X2 : $i, X4 : $i]:
% 0.40/0.59         (((k4_xboole_0 @ X2 @ X4) = (k1_xboole_0)) | ~ (r1_tarski @ X2 @ X4))),
% 0.40/0.59      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.40/0.59  thf('6', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i]:
% 0.40/0.59         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.40/0.59      inference('sup-', [status(thm)], ['4', '5'])).
% 0.40/0.59  thf('7', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i]:
% 0.40/0.59         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.40/0.59      inference('sup+', [status(thm)], ['3', '6'])).
% 0.40/0.59  thf(t48_xboole_1, axiom,
% 0.40/0.59    (![A:$i,B:$i]:
% 0.40/0.59     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.40/0.59  thf('8', plain,
% 0.40/0.59      (![X9 : $i, X10 : $i]:
% 0.40/0.59         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 0.40/0.59           = (k3_xboole_0 @ X9 @ X10))),
% 0.40/0.59      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.40/0.59  thf(t41_xboole_1, axiom,
% 0.40/0.59    (![A:$i,B:$i,C:$i]:
% 0.40/0.59     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.40/0.59       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.40/0.59  thf('9', plain,
% 0.40/0.59      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.40/0.59         ((k4_xboole_0 @ (k4_xboole_0 @ X6 @ X7) @ X8)
% 0.40/0.59           = (k4_xboole_0 @ X6 @ (k2_xboole_0 @ X7 @ X8)))),
% 0.40/0.59      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.40/0.59  thf('10', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.59         ((k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)
% 0.40/0.59           = (k4_xboole_0 @ X2 @ 
% 0.40/0.59              (k2_xboole_0 @ X1 @ (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))))),
% 0.40/0.59      inference('sup+', [status(thm)], ['8', '9'])).
% 0.40/0.59  thf('11', plain,
% 0.40/0.59      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.40/0.59         ((k4_xboole_0 @ (k4_xboole_0 @ X6 @ X7) @ X8)
% 0.40/0.59           = (k4_xboole_0 @ X6 @ (k2_xboole_0 @ X7 @ X8)))),
% 0.40/0.59      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.40/0.59  thf('12', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.59         ((k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)
% 0.40/0.59           = (k4_xboole_0 @ X2 @ 
% 0.40/0.59              (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))))),
% 0.40/0.59      inference('demod', [status(thm)], ['10', '11'])).
% 0.40/0.59  thf('13', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i]:
% 0.40/0.59         ((k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0)
% 0.40/0.59           = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ k1_xboole_0)))),
% 0.40/0.59      inference('sup+', [status(thm)], ['7', '12'])).
% 0.40/0.59  thf('14', plain,
% 0.40/0.59      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.40/0.59         ((k4_xboole_0 @ (k4_xboole_0 @ X6 @ X7) @ X8)
% 0.40/0.59           = (k4_xboole_0 @ X6 @ (k2_xboole_0 @ X7 @ X8)))),
% 0.40/0.59      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.40/0.59  thf(t3_boole, axiom,
% 0.40/0.59    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.40/0.59  thf('15', plain, (![X5 : $i]: ((k4_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 0.40/0.59      inference('cnf', [status(esa)], [t3_boole])).
% 0.40/0.59  thf('16', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i]:
% 0.40/0.59         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ k1_xboole_0))
% 0.40/0.59           = (k4_xboole_0 @ X1 @ X0))),
% 0.40/0.59      inference('sup+', [status(thm)], ['14', '15'])).
% 0.40/0.59  thf('17', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i]:
% 0.40/0.59         ((k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0)
% 0.40/0.59           = (k4_xboole_0 @ X0 @ X1))),
% 0.40/0.59      inference('demod', [status(thm)], ['13', '16'])).
% 0.40/0.59  thf('18', plain,
% 0.40/0.59      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.40/0.59         ((k4_xboole_0 @ (k4_xboole_0 @ X6 @ X7) @ X8)
% 0.40/0.59           = (k4_xboole_0 @ X6 @ (k2_xboole_0 @ X7 @ X8)))),
% 0.40/0.59      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.40/0.59  thf('19', plain,
% 0.40/0.59      (((k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))
% 0.40/0.59         != (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 0.40/0.59      inference('demod', [status(thm)], ['2', '17', '18'])).
% 0.40/0.59  thf('20', plain, ($false), inference('simplify', [status(thm)], ['19'])).
% 0.40/0.59  
% 0.40/0.59  % SZS output end Refutation
% 0.40/0.59  
% 0.40/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
