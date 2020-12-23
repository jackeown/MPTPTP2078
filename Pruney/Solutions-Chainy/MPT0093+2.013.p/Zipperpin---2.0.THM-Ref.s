%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.aJBYp37epr

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:48 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :   49 (  60 expanded)
%              Number of leaves         :   16 (  25 expanded)
%              Depth                    :   11
%              Number of atoms          :  289 ( 383 expanded)
%              Number of equality atoms :   33 (  40 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(t86_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) )
     => ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( r1_tarski @ A @ B )
          & ( r1_xboole_0 @ A @ C ) )
       => ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t86_xboole_1])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('2',plain,(
    ! [X0: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X2 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('3',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r1_xboole_0 @ sk_A @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('5',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k4_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('6',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C )
    = sk_A ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('7',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ ( k4_xboole_0 @ X5 @ X6 ) )
      = ( k3_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('8',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_A )
    = ( k3_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('9',plain,(
    ! [X4: $i] :
      ( ( k4_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('10',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ ( k4_xboole_0 @ X5 @ X6 ) )
      = ( k3_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('12',plain,(
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['8','13'])).

thf(t52_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf('15',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X7 @ X8 ) @ ( k3_xboole_0 @ X7 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ sk_C ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ sk_A @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X4: $i] :
      ( ( k4_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('18',plain,(
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('19',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X7 @ X8 ) @ ( k3_xboole_0 @ X7 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ k1_xboole_0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X4: $i] :
      ( ( k4_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['17','22'])).

thf('24',plain,(
    ! [X4: $i] :
      ( ( k4_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ sk_C ) )
      = ( k4_xboole_0 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['16','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( ( k4_xboole_0 @ X0 @ X1 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ sk_A @ X0 )
       != k1_xboole_0 )
      | ( r1_tarski @ sk_A @ ( k4_xboole_0 @ X0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['3','28'])).

thf('30',plain,(
    r1_tarski @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    $false ),
    inference(demod,[status(thm)],['0','30'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.aJBYp37epr
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:11:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.40/0.59  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.40/0.59  % Solved by: fo/fo7.sh
% 0.40/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.40/0.59  % done 193 iterations in 0.132s
% 0.40/0.59  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.40/0.59  % SZS output start Refutation
% 0.40/0.59  thf(sk_B_type, type, sk_B: $i).
% 0.40/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.40/0.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.40/0.59  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.40/0.59  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.40/0.59  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.40/0.59  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.40/0.59  thf(sk_C_type, type, sk_C: $i).
% 0.40/0.59  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.40/0.59  thf(t86_xboole_1, conjecture,
% 0.40/0.59    (![A:$i,B:$i,C:$i]:
% 0.40/0.59     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) =>
% 0.40/0.59       ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) ))).
% 0.40/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.40/0.59    (~( ![A:$i,B:$i,C:$i]:
% 0.40/0.59        ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) =>
% 0.40/0.59          ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) ) )),
% 0.40/0.59    inference('cnf.neg', [status(esa)], [t86_xboole_1])).
% 0.40/0.59  thf('0', plain, (~ (r1_tarski @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('1', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf(l32_xboole_1, axiom,
% 0.40/0.59    (![A:$i,B:$i]:
% 0.40/0.59     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.40/0.59  thf('2', plain,
% 0.40/0.59      (![X0 : $i, X2 : $i]:
% 0.40/0.59         (((k4_xboole_0 @ X0 @ X2) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ X2))),
% 0.40/0.59      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.40/0.59  thf('3', plain, (((k4_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.40/0.59      inference('sup-', [status(thm)], ['1', '2'])).
% 0.40/0.59  thf('4', plain, ((r1_xboole_0 @ sk_A @ sk_C)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf(t83_xboole_1, axiom,
% 0.40/0.59    (![A:$i,B:$i]:
% 0.40/0.59     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.40/0.59  thf('5', plain,
% 0.40/0.59      (![X10 : $i, X11 : $i]:
% 0.40/0.59         (((k4_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_xboole_0 @ X10 @ X11))),
% 0.40/0.59      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.40/0.59  thf('6', plain, (((k4_xboole_0 @ sk_A @ sk_C) = (sk_A))),
% 0.40/0.59      inference('sup-', [status(thm)], ['4', '5'])).
% 0.40/0.59  thf(t48_xboole_1, axiom,
% 0.40/0.59    (![A:$i,B:$i]:
% 0.40/0.59     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.40/0.59  thf('7', plain,
% 0.40/0.59      (![X5 : $i, X6 : $i]:
% 0.40/0.59         ((k4_xboole_0 @ X5 @ (k4_xboole_0 @ X5 @ X6))
% 0.40/0.59           = (k3_xboole_0 @ X5 @ X6))),
% 0.40/0.59      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.40/0.59  thf('8', plain,
% 0.40/0.59      (((k4_xboole_0 @ sk_A @ sk_A) = (k3_xboole_0 @ sk_A @ sk_C))),
% 0.40/0.59      inference('sup+', [status(thm)], ['6', '7'])).
% 0.40/0.59  thf(t3_boole, axiom,
% 0.40/0.59    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.40/0.59  thf('9', plain, (![X4 : $i]: ((k4_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 0.40/0.59      inference('cnf', [status(esa)], [t3_boole])).
% 0.40/0.59  thf('10', plain,
% 0.40/0.59      (![X5 : $i, X6 : $i]:
% 0.40/0.59         ((k4_xboole_0 @ X5 @ (k4_xboole_0 @ X5 @ X6))
% 0.40/0.59           = (k3_xboole_0 @ X5 @ X6))),
% 0.40/0.59      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.40/0.59  thf('11', plain,
% 0.40/0.59      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.40/0.59      inference('sup+', [status(thm)], ['9', '10'])).
% 0.40/0.59  thf(t2_boole, axiom,
% 0.40/0.59    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.40/0.59  thf('12', plain,
% 0.40/0.59      (![X3 : $i]: ((k3_xboole_0 @ X3 @ k1_xboole_0) = (k1_xboole_0))),
% 0.40/0.59      inference('cnf', [status(esa)], [t2_boole])).
% 0.40/0.59  thf('13', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.40/0.59      inference('demod', [status(thm)], ['11', '12'])).
% 0.40/0.59  thf('14', plain, (((k1_xboole_0) = (k3_xboole_0 @ sk_A @ sk_C))),
% 0.40/0.59      inference('demod', [status(thm)], ['8', '13'])).
% 0.40/0.59  thf(t52_xboole_1, axiom,
% 0.40/0.59    (![A:$i,B:$i,C:$i]:
% 0.40/0.59     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.40/0.59       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 0.40/0.59  thf('15', plain,
% 0.40/0.59      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.40/0.59         ((k4_xboole_0 @ X7 @ (k4_xboole_0 @ X8 @ X9))
% 0.40/0.59           = (k2_xboole_0 @ (k4_xboole_0 @ X7 @ X8) @ (k3_xboole_0 @ X7 @ X9)))),
% 0.40/0.59      inference('cnf', [status(esa)], [t52_xboole_1])).
% 0.40/0.59  thf('16', plain,
% 0.40/0.59      (![X0 : $i]:
% 0.40/0.59         ((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ X0 @ sk_C))
% 0.40/0.59           = (k2_xboole_0 @ (k4_xboole_0 @ sk_A @ X0) @ k1_xboole_0))),
% 0.40/0.59      inference('sup+', [status(thm)], ['14', '15'])).
% 0.40/0.59  thf('17', plain, (![X4 : $i]: ((k4_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 0.40/0.59      inference('cnf', [status(esa)], [t3_boole])).
% 0.40/0.59  thf('18', plain,
% 0.40/0.59      (![X3 : $i]: ((k3_xboole_0 @ X3 @ k1_xboole_0) = (k1_xboole_0))),
% 0.40/0.59      inference('cnf', [status(esa)], [t2_boole])).
% 0.40/0.59  thf('19', plain,
% 0.40/0.59      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.40/0.59         ((k4_xboole_0 @ X7 @ (k4_xboole_0 @ X8 @ X9))
% 0.40/0.59           = (k2_xboole_0 @ (k4_xboole_0 @ X7 @ X8) @ (k3_xboole_0 @ X7 @ X9)))),
% 0.40/0.59      inference('cnf', [status(esa)], [t52_xboole_1])).
% 0.40/0.59  thf('20', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i]:
% 0.40/0.59         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ k1_xboole_0))
% 0.40/0.59           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ k1_xboole_0))),
% 0.40/0.59      inference('sup+', [status(thm)], ['18', '19'])).
% 0.40/0.59  thf('21', plain, (![X4 : $i]: ((k4_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 0.40/0.59      inference('cnf', [status(esa)], [t3_boole])).
% 0.40/0.59  thf('22', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i]:
% 0.40/0.59         ((k4_xboole_0 @ X0 @ X1)
% 0.40/0.59           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ k1_xboole_0))),
% 0.40/0.59      inference('demod', [status(thm)], ['20', '21'])).
% 0.40/0.59  thf('23', plain,
% 0.40/0.59      (![X0 : $i]:
% 0.40/0.59         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k2_xboole_0 @ X0 @ k1_xboole_0))),
% 0.40/0.59      inference('sup+', [status(thm)], ['17', '22'])).
% 0.40/0.59  thf('24', plain, (![X4 : $i]: ((k4_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 0.40/0.59      inference('cnf', [status(esa)], [t3_boole])).
% 0.40/0.59  thf('25', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.40/0.59      inference('sup+', [status(thm)], ['23', '24'])).
% 0.40/0.59  thf('26', plain,
% 0.40/0.59      (![X0 : $i]:
% 0.40/0.59         ((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ X0 @ sk_C))
% 0.40/0.59           = (k4_xboole_0 @ sk_A @ X0))),
% 0.40/0.59      inference('demod', [status(thm)], ['16', '25'])).
% 0.40/0.59  thf('27', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i]:
% 0.40/0.59         ((r1_tarski @ X0 @ X1) | ((k4_xboole_0 @ X0 @ X1) != (k1_xboole_0)))),
% 0.40/0.59      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.40/0.59  thf('28', plain,
% 0.40/0.59      (![X0 : $i]:
% 0.40/0.59         (((k4_xboole_0 @ sk_A @ X0) != (k1_xboole_0))
% 0.40/0.59          | (r1_tarski @ sk_A @ (k4_xboole_0 @ X0 @ sk_C)))),
% 0.40/0.59      inference('sup-', [status(thm)], ['26', '27'])).
% 0.40/0.59  thf('29', plain,
% 0.40/0.59      ((((k1_xboole_0) != (k1_xboole_0))
% 0.40/0.59        | (r1_tarski @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)))),
% 0.40/0.59      inference('sup-', [status(thm)], ['3', '28'])).
% 0.40/0.59  thf('30', plain, ((r1_tarski @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))),
% 0.40/0.59      inference('simplify', [status(thm)], ['29'])).
% 0.40/0.59  thf('31', plain, ($false), inference('demod', [status(thm)], ['0', '30'])).
% 0.40/0.59  
% 0.40/0.59  % SZS output end Refutation
% 0.40/0.59  
% 0.40/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
