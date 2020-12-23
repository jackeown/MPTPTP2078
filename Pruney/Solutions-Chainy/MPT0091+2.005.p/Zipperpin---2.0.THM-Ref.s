%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ipOdEFsGmm

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:43 EST 2020

% Result     : Theorem 0.67s
% Output     : Refutation 0.67s
% Verified   : 
% Statistics : Number of formulae       :   51 (  62 expanded)
%              Number of leaves         :   15 (  24 expanded)
%              Depth                    :   16
%              Number of atoms          :  290 ( 389 expanded)
%              Number of equality atoms :   25 (  30 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t84_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r1_xboole_0 @ A @ B )
        & ( r1_xboole_0 @ A @ C )
        & ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ A @ C )
          & ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t84_xboole_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('3',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ ( k4_xboole_0 @ X6 @ X7 ) )
      = ( k3_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('5',plain,(
    r1_xboole_0 @ sk_A @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('6',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ~ ( r1_xboole_0 @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('7',plain,(
    r1_xboole_0 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('9',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('10',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k3_xboole_0 @ X8 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X8 @ X9 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_C @ ( k4_xboole_0 @ sk_A @ X0 ) )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('12',plain,(
    ! [X5: $i] :
      ( ( k4_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('13',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X11 @ X12 ) @ X12 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ~ ( r1_xboole_0 @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('17',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k4_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_C @ ( k4_xboole_0 @ sk_A @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['11','18'])).

thf('20',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ( ( k3_xboole_0 @ X0 @ X2 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ sk_C @ ( k4_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_C @ ( k4_xboole_0 @ sk_A @ X0 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ~ ( r1_xboole_0 @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ sk_A @ X0 ) @ sk_C ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ sk_A @ X0 ) @ sk_C ) ),
    inference('sup+',[status(thm)],['4','24'])).

thf('26',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k4_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ sk_A @ X0 ) @ sk_C )
      = ( k3_xboole_0 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k3_xboole_0 @ X8 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X8 @ X9 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ sk_C ) )
      = ( k3_xboole_0 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['3','29'])).

thf('31',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ( ( k3_xboole_0 @ X0 @ X2 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('32',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    $false ),
    inference(demod,[status(thm)],['0','33'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ipOdEFsGmm
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:51:21 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.13/0.36  % Running portfolio for 600 s
% 0.13/0.36  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.67/0.88  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.67/0.88  % Solved by: fo/fo7.sh
% 0.67/0.88  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.67/0.88  % done 1370 iterations in 0.405s
% 0.67/0.88  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.67/0.88  % SZS output start Refutation
% 0.67/0.88  thf(sk_A_type, type, sk_A: $i).
% 0.67/0.88  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.67/0.88  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.67/0.88  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.67/0.88  thf(sk_C_type, type, sk_C: $i).
% 0.67/0.88  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.67/0.88  thf(sk_B_type, type, sk_B: $i).
% 0.67/0.88  thf(t84_xboole_1, conjecture,
% 0.67/0.88    (![A:$i,B:$i,C:$i]:
% 0.67/0.88     ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & ( r1_xboole_0 @ A @ C ) & 
% 0.67/0.88          ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) ) ))).
% 0.67/0.88  thf(zf_stmt_0, negated_conjecture,
% 0.67/0.88    (~( ![A:$i,B:$i,C:$i]:
% 0.67/0.88        ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & ( r1_xboole_0 @ A @ C ) & 
% 0.67/0.88             ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) ) ) )),
% 0.67/0.88    inference('cnf.neg', [status(esa)], [t84_xboole_1])).
% 0.67/0.88  thf('0', plain, (~ (r1_xboole_0 @ sk_A @ sk_B)),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('1', plain, ((r1_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf(d7_xboole_0, axiom,
% 0.67/0.88    (![A:$i,B:$i]:
% 0.67/0.88     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.67/0.88       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.67/0.88  thf('2', plain,
% 0.67/0.88      (![X0 : $i, X1 : $i]:
% 0.67/0.88         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.67/0.88      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.67/0.88  thf('3', plain,
% 0.67/0.88      (((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) = (k1_xboole_0))),
% 0.67/0.88      inference('sup-', [status(thm)], ['1', '2'])).
% 0.67/0.88  thf(t48_xboole_1, axiom,
% 0.67/0.88    (![A:$i,B:$i]:
% 0.67/0.88     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.67/0.88  thf('4', plain,
% 0.67/0.88      (![X6 : $i, X7 : $i]:
% 0.67/0.88         ((k4_xboole_0 @ X6 @ (k4_xboole_0 @ X6 @ X7))
% 0.67/0.88           = (k3_xboole_0 @ X6 @ X7))),
% 0.67/0.88      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.67/0.88  thf('5', plain, ((r1_xboole_0 @ sk_A @ sk_C)),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf(symmetry_r1_xboole_0, axiom,
% 0.67/0.88    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.67/0.88  thf('6', plain,
% 0.67/0.88      (![X3 : $i, X4 : $i]:
% 0.67/0.88         ((r1_xboole_0 @ X3 @ X4) | ~ (r1_xboole_0 @ X4 @ X3))),
% 0.67/0.88      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.67/0.88  thf('7', plain, ((r1_xboole_0 @ sk_C @ sk_A)),
% 0.67/0.88      inference('sup-', [status(thm)], ['5', '6'])).
% 0.67/0.88  thf('8', plain,
% 0.67/0.88      (![X0 : $i, X1 : $i]:
% 0.67/0.88         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.67/0.88      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.67/0.88  thf('9', plain, (((k3_xboole_0 @ sk_C @ sk_A) = (k1_xboole_0))),
% 0.67/0.88      inference('sup-', [status(thm)], ['7', '8'])).
% 0.67/0.88  thf(t49_xboole_1, axiom,
% 0.67/0.88    (![A:$i,B:$i,C:$i]:
% 0.67/0.88     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.67/0.88       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 0.67/0.88  thf('10', plain,
% 0.67/0.88      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.67/0.88         ((k3_xboole_0 @ X8 @ (k4_xboole_0 @ X9 @ X10))
% 0.67/0.88           = (k4_xboole_0 @ (k3_xboole_0 @ X8 @ X9) @ X10))),
% 0.67/0.88      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.67/0.88  thf('11', plain,
% 0.67/0.88      (![X0 : $i]:
% 0.67/0.88         ((k3_xboole_0 @ sk_C @ (k4_xboole_0 @ sk_A @ X0))
% 0.67/0.88           = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.67/0.88      inference('sup+', [status(thm)], ['9', '10'])).
% 0.67/0.88  thf(t3_boole, axiom,
% 0.67/0.88    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.67/0.88  thf('12', plain, (![X5 : $i]: ((k4_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 0.67/0.88      inference('cnf', [status(esa)], [t3_boole])).
% 0.67/0.88  thf(t79_xboole_1, axiom,
% 0.67/0.88    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.67/0.88  thf('13', plain,
% 0.67/0.88      (![X11 : $i, X12 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X11 @ X12) @ X12)),
% 0.67/0.88      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.67/0.88  thf('14', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.67/0.88      inference('sup+', [status(thm)], ['12', '13'])).
% 0.67/0.88  thf('15', plain,
% 0.67/0.88      (![X3 : $i, X4 : $i]:
% 0.67/0.88         ((r1_xboole_0 @ X3 @ X4) | ~ (r1_xboole_0 @ X4 @ X3))),
% 0.67/0.88      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.67/0.88  thf('16', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.67/0.88      inference('sup-', [status(thm)], ['14', '15'])).
% 0.67/0.88  thf(t83_xboole_1, axiom,
% 0.67/0.88    (![A:$i,B:$i]:
% 0.67/0.88     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.67/0.88  thf('17', plain,
% 0.67/0.88      (![X13 : $i, X14 : $i]:
% 0.67/0.88         (((k4_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_xboole_0 @ X13 @ X14))),
% 0.67/0.88      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.67/0.88  thf('18', plain,
% 0.67/0.88      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.67/0.88      inference('sup-', [status(thm)], ['16', '17'])).
% 0.67/0.88  thf('19', plain,
% 0.67/0.88      (![X0 : $i]:
% 0.67/0.88         ((k3_xboole_0 @ sk_C @ (k4_xboole_0 @ sk_A @ X0)) = (k1_xboole_0))),
% 0.67/0.88      inference('demod', [status(thm)], ['11', '18'])).
% 0.67/0.88  thf('20', plain,
% 0.67/0.88      (![X0 : $i, X2 : $i]:
% 0.67/0.88         ((r1_xboole_0 @ X0 @ X2) | ((k3_xboole_0 @ X0 @ X2) != (k1_xboole_0)))),
% 0.67/0.88      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.67/0.88  thf('21', plain,
% 0.67/0.88      (![X0 : $i]:
% 0.67/0.88         (((k1_xboole_0) != (k1_xboole_0))
% 0.67/0.88          | (r1_xboole_0 @ sk_C @ (k4_xboole_0 @ sk_A @ X0)))),
% 0.67/0.88      inference('sup-', [status(thm)], ['19', '20'])).
% 0.67/0.88  thf('22', plain,
% 0.67/0.88      (![X0 : $i]: (r1_xboole_0 @ sk_C @ (k4_xboole_0 @ sk_A @ X0))),
% 0.67/0.88      inference('simplify', [status(thm)], ['21'])).
% 0.67/0.88  thf('23', plain,
% 0.67/0.88      (![X3 : $i, X4 : $i]:
% 0.67/0.88         ((r1_xboole_0 @ X3 @ X4) | ~ (r1_xboole_0 @ X4 @ X3))),
% 0.67/0.88      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.67/0.88  thf('24', plain,
% 0.67/0.88      (![X0 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ sk_A @ X0) @ sk_C)),
% 0.67/0.88      inference('sup-', [status(thm)], ['22', '23'])).
% 0.67/0.88  thf('25', plain,
% 0.67/0.88      (![X0 : $i]: (r1_xboole_0 @ (k3_xboole_0 @ sk_A @ X0) @ sk_C)),
% 0.67/0.88      inference('sup+', [status(thm)], ['4', '24'])).
% 0.67/0.88  thf('26', plain,
% 0.67/0.88      (![X13 : $i, X14 : $i]:
% 0.67/0.88         (((k4_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_xboole_0 @ X13 @ X14))),
% 0.67/0.88      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.67/0.88  thf('27', plain,
% 0.67/0.88      (![X0 : $i]:
% 0.67/0.88         ((k4_xboole_0 @ (k3_xboole_0 @ sk_A @ X0) @ sk_C)
% 0.67/0.88           = (k3_xboole_0 @ sk_A @ X0))),
% 0.67/0.88      inference('sup-', [status(thm)], ['25', '26'])).
% 0.67/0.88  thf('28', plain,
% 0.67/0.88      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.67/0.88         ((k3_xboole_0 @ X8 @ (k4_xboole_0 @ X9 @ X10))
% 0.67/0.88           = (k4_xboole_0 @ (k3_xboole_0 @ X8 @ X9) @ X10))),
% 0.67/0.88      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.67/0.88  thf('29', plain,
% 0.67/0.88      (![X0 : $i]:
% 0.67/0.88         ((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ X0 @ sk_C))
% 0.67/0.88           = (k3_xboole_0 @ sk_A @ X0))),
% 0.67/0.88      inference('demod', [status(thm)], ['27', '28'])).
% 0.67/0.88  thf('30', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.67/0.88      inference('demod', [status(thm)], ['3', '29'])).
% 0.67/0.88  thf('31', plain,
% 0.67/0.88      (![X0 : $i, X2 : $i]:
% 0.67/0.88         ((r1_xboole_0 @ X0 @ X2) | ((k3_xboole_0 @ X0 @ X2) != (k1_xboole_0)))),
% 0.67/0.88      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.67/0.88  thf('32', plain,
% 0.67/0.88      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ sk_A @ sk_B))),
% 0.67/0.88      inference('sup-', [status(thm)], ['30', '31'])).
% 0.67/0.88  thf('33', plain, ((r1_xboole_0 @ sk_A @ sk_B)),
% 0.67/0.88      inference('simplify', [status(thm)], ['32'])).
% 0.67/0.88  thf('34', plain, ($false), inference('demod', [status(thm)], ['0', '33'])).
% 0.67/0.88  
% 0.67/0.88  % SZS output end Refutation
% 0.67/0.88  
% 0.74/0.89  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
