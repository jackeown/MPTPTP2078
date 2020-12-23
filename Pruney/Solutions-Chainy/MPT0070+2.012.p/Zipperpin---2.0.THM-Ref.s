%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.nWTE0cLr6r

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:33 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   64 (  77 expanded)
%              Number of leaves         :   20 (  31 expanded)
%              Depth                    :   13
%              Number of atoms          :  365 ( 465 expanded)
%              Number of equality atoms :   42 (  50 expanded)
%              Maximal formula depth    :    9 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t63_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( r1_tarski @ A @ B )
          & ( r1_xboole_0 @ B @ C ) )
       => ( r1_xboole_0 @ A @ C ) ) ),
    inference('cnf.neg',[status(esa)],[t63_xboole_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_xboole_0 @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('2',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('3',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','2'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('5',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X20 @ X21 ) @ ( k4_xboole_0 @ X20 @ X21 ) )
      = X20 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_C @ sk_B ) )
    = sk_C ),
    inference('sup+',[status(thm)],['3','6'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('8',plain,(
    ! [X9: $i] :
      ( ( k3_xboole_0 @ X9 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('9',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X20 @ X21 ) @ ( k4_xboole_0 @ X20 @ X21 ) )
      = X20 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('11',plain,(
    ! [X14: $i] :
      ( ( k4_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,
    ( ( k4_xboole_0 @ sk_C @ sk_B )
    = sk_C ),
    inference(demod,[status(thm)],['7','12'])).

thf('14',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('15',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_xboole_0 @ X8 @ X7 )
        = X7 )
      | ~ ( r1_tarski @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('16',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B )
    = sk_B ),
    inference('sup-',[status(thm)],['14','15'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('17',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X15 @ X16 ) @ X17 )
      = ( k4_xboole_0 @ X15 @ ( k2_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('18',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X10 @ X11 ) @ X10 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ ( k4_xboole_0 @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ sk_B ) @ ( k4_xboole_0 @ X0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['16','19'])).

thf('21',plain,(
    r1_tarski @ sk_C @ ( k4_xboole_0 @ sk_C @ sk_A ) ),
    inference('sup+',[status(thm)],['13','20'])).

thf('22',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_xboole_0 @ X8 @ X7 )
        = X7 )
      | ~ ( r1_tarski @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('23',plain,
    ( ( k2_xboole_0 @ sk_C @ ( k4_xboole_0 @ sk_C @ sk_A ) )
    = ( k4_xboole_0 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X10 @ X11 ) @ X10 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('25',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_xboole_0 @ X8 @ X7 )
        = X7 )
      | ~ ( r1_tarski @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( sk_C
    = ( k4_xboole_0 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['23','28'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('30',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('31',plain,
    ( ( k4_xboole_0 @ sk_C @ sk_C )
    = ( k3_xboole_0 @ sk_C @ sk_A ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X14: $i] :
      ( ( k4_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('33',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X9: $i] :
      ( ( k3_xboole_0 @ X9 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('38',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['31','36','37'])).

thf('39',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_xboole_0 @ X4 @ X6 )
      | ( ( k3_xboole_0 @ X4 @ X6 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('40',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    r1_xboole_0 @ sk_A @ sk_C ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    $false ),
    inference(demod,[status(thm)],['0','41'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.nWTE0cLr6r
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:25:19 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.55  % Solved by: fo/fo7.sh
% 0.21/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.55  % done 221 iterations in 0.098s
% 0.21/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.55  % SZS output start Refutation
% 0.21/0.55  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.55  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.55  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.55  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.55  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.55  thf(t63_xboole_1, conjecture,
% 0.21/0.55    (![A:$i,B:$i,C:$i]:
% 0.21/0.55     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 0.21/0.55       ( r1_xboole_0 @ A @ C ) ))).
% 0.21/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.55    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.55        ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 0.21/0.55          ( r1_xboole_0 @ A @ C ) ) )),
% 0.21/0.55    inference('cnf.neg', [status(esa)], [t63_xboole_1])).
% 0.21/0.55  thf('0', plain, (~ (r1_xboole_0 @ sk_A @ sk_C)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('1', plain, ((r1_xboole_0 @ sk_B @ sk_C)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf(d7_xboole_0, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.21/0.55       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.21/0.55  thf('2', plain,
% 0.21/0.55      (![X4 : $i, X5 : $i]:
% 0.21/0.55         (((k3_xboole_0 @ X4 @ X5) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X4 @ X5))),
% 0.21/0.55      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.21/0.55  thf('3', plain, (((k3_xboole_0 @ sk_B @ sk_C) = (k1_xboole_0))),
% 0.21/0.55      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.55  thf(commutativity_k3_xboole_0, axiom,
% 0.21/0.55    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.21/0.55  thf('4', plain,
% 0.21/0.55      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.21/0.55      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.21/0.55  thf(t51_xboole_1, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 0.21/0.55       ( A ) ))).
% 0.21/0.55  thf('5', plain,
% 0.21/0.55      (![X20 : $i, X21 : $i]:
% 0.21/0.55         ((k2_xboole_0 @ (k3_xboole_0 @ X20 @ X21) @ (k4_xboole_0 @ X20 @ X21))
% 0.21/0.55           = (X20))),
% 0.21/0.55      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.21/0.55  thf('6', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1))
% 0.21/0.55           = (X0))),
% 0.21/0.55      inference('sup+', [status(thm)], ['4', '5'])).
% 0.21/0.55  thf('7', plain,
% 0.21/0.55      (((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ sk_C @ sk_B)) = (sk_C))),
% 0.21/0.55      inference('sup+', [status(thm)], ['3', '6'])).
% 0.21/0.55  thf(t2_boole, axiom,
% 0.21/0.55    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.21/0.55  thf('8', plain,
% 0.21/0.55      (![X9 : $i]: ((k3_xboole_0 @ X9 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.55      inference('cnf', [status(esa)], [t2_boole])).
% 0.21/0.55  thf('9', plain,
% 0.21/0.55      (![X20 : $i, X21 : $i]:
% 0.21/0.55         ((k2_xboole_0 @ (k3_xboole_0 @ X20 @ X21) @ (k4_xboole_0 @ X20 @ X21))
% 0.21/0.55           = (X20))),
% 0.21/0.55      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.21/0.55  thf('10', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         ((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ X0 @ k1_xboole_0)) = (X0))),
% 0.21/0.55      inference('sup+', [status(thm)], ['8', '9'])).
% 0.21/0.55  thf(t3_boole, axiom,
% 0.21/0.55    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.21/0.55  thf('11', plain, (![X14 : $i]: ((k4_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.21/0.55      inference('cnf', [status(esa)], [t3_boole])).
% 0.21/0.55  thf('12', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.21/0.55      inference('demod', [status(thm)], ['10', '11'])).
% 0.21/0.55  thf('13', plain, (((k4_xboole_0 @ sk_C @ sk_B) = (sk_C))),
% 0.21/0.55      inference('demod', [status(thm)], ['7', '12'])).
% 0.21/0.55  thf('14', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf(t12_xboole_1, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.21/0.55  thf('15', plain,
% 0.21/0.55      (![X7 : $i, X8 : $i]:
% 0.21/0.55         (((k2_xboole_0 @ X8 @ X7) = (X7)) | ~ (r1_tarski @ X8 @ X7))),
% 0.21/0.55      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.21/0.55  thf('16', plain, (((k2_xboole_0 @ sk_A @ sk_B) = (sk_B))),
% 0.21/0.55      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.55  thf(t41_xboole_1, axiom,
% 0.21/0.55    (![A:$i,B:$i,C:$i]:
% 0.21/0.55     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.21/0.55       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.21/0.55  thf('17', plain,
% 0.21/0.55      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.21/0.55         ((k4_xboole_0 @ (k4_xboole_0 @ X15 @ X16) @ X17)
% 0.21/0.55           = (k4_xboole_0 @ X15 @ (k2_xboole_0 @ X16 @ X17)))),
% 0.21/0.55      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.21/0.55  thf(t36_xboole_1, axiom,
% 0.21/0.55    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.21/0.55  thf('18', plain,
% 0.21/0.55      (![X10 : $i, X11 : $i]: (r1_tarski @ (k4_xboole_0 @ X10 @ X11) @ X10)),
% 0.21/0.55      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.21/0.55  thf('19', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.55         (r1_tarski @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ 
% 0.21/0.55          (k4_xboole_0 @ X2 @ X1))),
% 0.21/0.55      inference('sup+', [status(thm)], ['17', '18'])).
% 0.21/0.55  thf('20', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (r1_tarski @ (k4_xboole_0 @ X0 @ sk_B) @ (k4_xboole_0 @ X0 @ sk_A))),
% 0.21/0.55      inference('sup+', [status(thm)], ['16', '19'])).
% 0.21/0.56  thf('21', plain, ((r1_tarski @ sk_C @ (k4_xboole_0 @ sk_C @ sk_A))),
% 0.21/0.56      inference('sup+', [status(thm)], ['13', '20'])).
% 0.21/0.56  thf('22', plain,
% 0.21/0.56      (![X7 : $i, X8 : $i]:
% 0.21/0.56         (((k2_xboole_0 @ X8 @ X7) = (X7)) | ~ (r1_tarski @ X8 @ X7))),
% 0.21/0.56      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.21/0.56  thf('23', plain,
% 0.21/0.56      (((k2_xboole_0 @ sk_C @ (k4_xboole_0 @ sk_C @ sk_A))
% 0.21/0.56         = (k4_xboole_0 @ sk_C @ sk_A))),
% 0.21/0.56      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.56  thf('24', plain,
% 0.21/0.56      (![X10 : $i, X11 : $i]: (r1_tarski @ (k4_xboole_0 @ X10 @ X11) @ X10)),
% 0.21/0.56      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.21/0.56  thf('25', plain,
% 0.21/0.56      (![X7 : $i, X8 : $i]:
% 0.21/0.56         (((k2_xboole_0 @ X8 @ X7) = (X7)) | ~ (r1_tarski @ X8 @ X7))),
% 0.21/0.56      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.21/0.56  thf('26', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]:
% 0.21/0.56         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 0.21/0.56      inference('sup-', [status(thm)], ['24', '25'])).
% 0.21/0.56  thf(commutativity_k2_xboole_0, axiom,
% 0.21/0.56    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.21/0.56  thf('27', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.21/0.56      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.21/0.56  thf('28', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]:
% 0.21/0.56         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)) = (X0))),
% 0.21/0.56      inference('demod', [status(thm)], ['26', '27'])).
% 0.21/0.56  thf('29', plain, (((sk_C) = (k4_xboole_0 @ sk_C @ sk_A))),
% 0.21/0.56      inference('demod', [status(thm)], ['23', '28'])).
% 0.21/0.56  thf(t48_xboole_1, axiom,
% 0.21/0.56    (![A:$i,B:$i]:
% 0.21/0.56     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.21/0.56  thf('30', plain,
% 0.21/0.56      (![X18 : $i, X19 : $i]:
% 0.21/0.56         ((k4_xboole_0 @ X18 @ (k4_xboole_0 @ X18 @ X19))
% 0.21/0.56           = (k3_xboole_0 @ X18 @ X19))),
% 0.21/0.56      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.21/0.56  thf('31', plain,
% 0.21/0.56      (((k4_xboole_0 @ sk_C @ sk_C) = (k3_xboole_0 @ sk_C @ sk_A))),
% 0.21/0.56      inference('sup+', [status(thm)], ['29', '30'])).
% 0.21/0.56  thf('32', plain, (![X14 : $i]: ((k4_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.21/0.56      inference('cnf', [status(esa)], [t3_boole])).
% 0.21/0.56  thf('33', plain,
% 0.21/0.56      (![X18 : $i, X19 : $i]:
% 0.21/0.56         ((k4_xboole_0 @ X18 @ (k4_xboole_0 @ X18 @ X19))
% 0.21/0.56           = (k3_xboole_0 @ X18 @ X19))),
% 0.21/0.56      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.21/0.56  thf('34', plain,
% 0.21/0.56      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.21/0.56      inference('sup+', [status(thm)], ['32', '33'])).
% 0.21/0.56  thf('35', plain,
% 0.21/0.56      (![X9 : $i]: ((k3_xboole_0 @ X9 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.56      inference('cnf', [status(esa)], [t2_boole])).
% 0.21/0.56  thf('36', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.21/0.56      inference('demod', [status(thm)], ['34', '35'])).
% 0.21/0.56  thf('37', plain,
% 0.21/0.56      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.21/0.56      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.21/0.56  thf('38', plain, (((k1_xboole_0) = (k3_xboole_0 @ sk_A @ sk_C))),
% 0.21/0.56      inference('demod', [status(thm)], ['31', '36', '37'])).
% 0.21/0.56  thf('39', plain,
% 0.21/0.56      (![X4 : $i, X6 : $i]:
% 0.21/0.56         ((r1_xboole_0 @ X4 @ X6) | ((k3_xboole_0 @ X4 @ X6) != (k1_xboole_0)))),
% 0.21/0.56      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.21/0.56  thf('40', plain,
% 0.21/0.56      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ sk_A @ sk_C))),
% 0.21/0.56      inference('sup-', [status(thm)], ['38', '39'])).
% 0.21/0.56  thf('41', plain, ((r1_xboole_0 @ sk_A @ sk_C)),
% 0.21/0.56      inference('simplify', [status(thm)], ['40'])).
% 0.21/0.56  thf('42', plain, ($false), inference('demod', [status(thm)], ['0', '41'])).
% 0.21/0.56  
% 0.21/0.56  % SZS output end Refutation
% 0.21/0.56  
% 0.21/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
