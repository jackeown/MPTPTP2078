%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.t7ZcXBMfuq

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:32 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   36 (  40 expanded)
%              Number of leaves         :   15 (  18 expanded)
%              Depth                    :    8
%              Number of atoms          :  207 ( 242 expanded)
%              Number of equality atoms :   22 (  24 expanded)
%              Maximal formula depth    :    9 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t80_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_xboole_0 @ A @ B )
       => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t80_xboole_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('2',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('3',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('4',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k3_xboole_0 @ X14 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X14 @ X15 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('8',plain,(
    ! [X6: $i] :
      ( ( k3_xboole_0 @ X6 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('9',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k3_xboole_0 @ X14 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X14 @ X15 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('11',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X17 @ X18 ) @ ( k4_xboole_0 @ X17 @ X18 ) )
      = X17 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) @ ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('13',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ X7 @ ( k4_xboole_0 @ X8 @ X7 ) )
      = ( k2_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) @ X1 )
      = X1 ) ),
    inference(demod,[status(thm)],['12','13'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('15',plain,(
    ! [X5: $i] :
      ( ( k2_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('16',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['7','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    $false ),
    inference(demod,[status(thm)],['0','18'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.t7ZcXBMfuq
% 0.13/0.36  % Computer   : n002.cluster.edu
% 0.13/0.36  % Model      : x86_64 x86_64
% 0.13/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.36  % Memory     : 8042.1875MB
% 0.13/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.36  % CPULimit   : 60
% 0.13/0.36  % DateTime   : Tue Dec  1 09:33:37 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.13/0.36  % Running portfolio for 600 s
% 0.13/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.37  % Running in FO mode
% 0.22/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.50  % Solved by: fo/fo7.sh
% 0.22/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.50  % done 76 iterations in 0.040s
% 0.22/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.50  % SZS output start Refutation
% 0.22/0.50  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.22/0.50  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.50  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.22/0.50  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.22/0.50  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.50  thf(t80_xboole_1, conjecture,
% 0.22/0.50    (![A:$i,B:$i,C:$i]:
% 0.22/0.50     ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) ))).
% 0.22/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.50    (~( ![A:$i,B:$i,C:$i]:
% 0.22/0.50        ( ( r1_xboole_0 @ A @ B ) =>
% 0.22/0.50          ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) ) )),
% 0.22/0.50    inference('cnf.neg', [status(esa)], [t80_xboole_1])).
% 0.22/0.50  thf('0', plain, (~ (r1_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('1', plain, ((r1_xboole_0 @ sk_A @ sk_B)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf(d7_xboole_0, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.22/0.50       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.22/0.50  thf('2', plain,
% 0.22/0.50      (![X2 : $i, X3 : $i]:
% 0.22/0.50         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.22/0.50      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.22/0.50  thf('3', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.22/0.50      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.50  thf(t49_xboole_1, axiom,
% 0.22/0.50    (![A:$i,B:$i,C:$i]:
% 0.22/0.50     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.22/0.50       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 0.22/0.50  thf('4', plain,
% 0.22/0.50      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.22/0.50         ((k3_xboole_0 @ X14 @ (k4_xboole_0 @ X15 @ X16))
% 0.22/0.50           = (k4_xboole_0 @ (k3_xboole_0 @ X14 @ X15) @ X16))),
% 0.22/0.50      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.22/0.50  thf('5', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         ((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ X0))
% 0.22/0.50           = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.22/0.50      inference('sup+', [status(thm)], ['3', '4'])).
% 0.22/0.50  thf('6', plain,
% 0.22/0.50      (![X2 : $i, X4 : $i]:
% 0.22/0.50         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 0.22/0.50      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.22/0.50  thf('7', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (((k4_xboole_0 @ k1_xboole_0 @ X0) != (k1_xboole_0))
% 0.22/0.50          | (r1_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['5', '6'])).
% 0.22/0.50  thf(t2_boole, axiom,
% 0.22/0.50    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.22/0.50  thf('8', plain,
% 0.22/0.50      (![X6 : $i]: ((k3_xboole_0 @ X6 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.50      inference('cnf', [status(esa)], [t2_boole])).
% 0.22/0.50  thf('9', plain,
% 0.22/0.50      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.22/0.50         ((k3_xboole_0 @ X14 @ (k4_xboole_0 @ X15 @ X16))
% 0.22/0.50           = (k4_xboole_0 @ (k3_xboole_0 @ X14 @ X15) @ X16))),
% 0.22/0.50      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.22/0.50  thf('10', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ k1_xboole_0 @ X0))
% 0.22/0.50           = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.22/0.50      inference('sup+', [status(thm)], ['8', '9'])).
% 0.22/0.50  thf(t51_xboole_1, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 0.22/0.50       ( A ) ))).
% 0.22/0.50  thf('11', plain,
% 0.22/0.50      (![X17 : $i, X18 : $i]:
% 0.22/0.50         ((k2_xboole_0 @ (k3_xboole_0 @ X17 @ X18) @ (k4_xboole_0 @ X17 @ X18))
% 0.22/0.50           = (X17))),
% 0.22/0.50      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.22/0.50  thf('12', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         ((k2_xboole_0 @ (k4_xboole_0 @ k1_xboole_0 @ X0) @ 
% 0.22/0.50           (k4_xboole_0 @ X1 @ (k4_xboole_0 @ k1_xboole_0 @ X0))) = (X1))),
% 0.22/0.50      inference('sup+', [status(thm)], ['10', '11'])).
% 0.22/0.50  thf(t39_xboole_1, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.22/0.50  thf('13', plain,
% 0.22/0.50      (![X7 : $i, X8 : $i]:
% 0.22/0.50         ((k2_xboole_0 @ X7 @ (k4_xboole_0 @ X8 @ X7))
% 0.22/0.50           = (k2_xboole_0 @ X7 @ X8))),
% 0.22/0.50      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.22/0.50  thf('14', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         ((k2_xboole_0 @ (k4_xboole_0 @ k1_xboole_0 @ X0) @ X1) = (X1))),
% 0.22/0.50      inference('demod', [status(thm)], ['12', '13'])).
% 0.22/0.50  thf(t1_boole, axiom,
% 0.22/0.50    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.22/0.50  thf('15', plain, (![X5 : $i]: ((k2_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 0.22/0.50      inference('cnf', [status(esa)], [t1_boole])).
% 0.22/0.50  thf('16', plain,
% 0.22/0.50      (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.22/0.50      inference('sup+', [status(thm)], ['14', '15'])).
% 0.22/0.50  thf('17', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (((k1_xboole_0) != (k1_xboole_0))
% 0.22/0.50          | (r1_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)))),
% 0.22/0.50      inference('demod', [status(thm)], ['7', '16'])).
% 0.22/0.50  thf('18', plain,
% 0.22/0.50      (![X0 : $i]: (r1_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ X0))),
% 0.22/0.50      inference('simplify', [status(thm)], ['17'])).
% 0.22/0.50  thf('19', plain, ($false), inference('demod', [status(thm)], ['0', '18'])).
% 0.22/0.50  
% 0.22/0.50  % SZS output end Refutation
% 0.22/0.50  
% 0.22/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
