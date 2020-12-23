%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.fb561agWoc

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:11 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   54 (  66 expanded)
%              Number of leaves         :   16 (  27 expanded)
%              Depth                    :   13
%              Number of atoms          :  326 ( 415 expanded)
%              Number of equality atoms :   39 (  49 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t74_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) )
        & ( r1_xboole_0 @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ~ ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t74_xboole_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('2',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('3',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('4',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) )
      = ( k4_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('6',plain,
    ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('7',plain,(
    ! [X6: $i] :
      ( ( k4_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('8',plain,
    ( sk_A
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(t52_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf('9',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X11 @ X12 ) @ ( k3_xboole_0 @ X11 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) )
      = ( k2_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X6: $i] :
      ( ( k4_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('12',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X11 @ X12 ) @ ( k3_xboole_0 @ X11 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ k1_xboole_0 @ X1 ) )
      = ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('15',plain,(
    ! [X5: $i] :
      ( ( k3_xboole_0 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) )
      = ( k4_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X6: $i] :
      ( ( k4_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('20',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X6: $i] :
      ( ( k4_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['13','20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) )
      = sk_A ) ),
    inference(demod,[status(thm)],['10','22'])).

thf('24',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ sk_A )
      = ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X6: $i] :
      ( ( k4_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('27',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X5: $i] :
      ( ( k3_xboole_0 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['25','30'])).

thf('32',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','34'])).

thf('36',plain,(
    $false ),
    inference(demod,[status(thm)],['0','35'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.fb561agWoc
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:16:08 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.39/0.57  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.39/0.57  % Solved by: fo/fo7.sh
% 0.39/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.57  % done 211 iterations in 0.105s
% 0.39/0.57  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.39/0.57  % SZS output start Refutation
% 0.39/0.57  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.39/0.57  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.39/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.57  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.39/0.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.39/0.57  thf(sk_C_type, type, sk_C: $i).
% 0.39/0.57  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.39/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.39/0.57  thf(t74_xboole_1, conjecture,
% 0.39/0.57    (![A:$i,B:$i,C:$i]:
% 0.39/0.57     ( ~( ( ~( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) & 
% 0.39/0.57          ( r1_xboole_0 @ A @ B ) ) ))).
% 0.39/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.57    (~( ![A:$i,B:$i,C:$i]:
% 0.39/0.57        ( ~( ( ~( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) & 
% 0.39/0.57             ( r1_xboole_0 @ A @ B ) ) ) )),
% 0.39/0.57    inference('cnf.neg', [status(esa)], [t74_xboole_1])).
% 0.39/0.57  thf('0', plain, (~ (r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf(t48_xboole_1, axiom,
% 0.39/0.57    (![A:$i,B:$i]:
% 0.39/0.57     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.39/0.57  thf('1', plain,
% 0.39/0.57      (![X9 : $i, X10 : $i]:
% 0.39/0.57         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 0.39/0.57           = (k3_xboole_0 @ X9 @ X10))),
% 0.39/0.57      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.39/0.57  thf('2', plain, ((r1_xboole_0 @ sk_A @ sk_B)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf(d7_xboole_0, axiom,
% 0.39/0.57    (![A:$i,B:$i]:
% 0.39/0.57     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.39/0.57       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.39/0.57  thf('3', plain,
% 0.39/0.57      (![X2 : $i, X3 : $i]:
% 0.39/0.57         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.39/0.57      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.39/0.57  thf('4', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.39/0.57      inference('sup-', [status(thm)], ['2', '3'])).
% 0.39/0.57  thf(t47_xboole_1, axiom,
% 0.39/0.57    (![A:$i,B:$i]:
% 0.39/0.57     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.39/0.57  thf('5', plain,
% 0.39/0.57      (![X7 : $i, X8 : $i]:
% 0.39/0.57         ((k4_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8))
% 0.39/0.57           = (k4_xboole_0 @ X7 @ X8))),
% 0.39/0.57      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.39/0.57  thf('6', plain,
% 0.39/0.57      (((k4_xboole_0 @ sk_A @ k1_xboole_0) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.39/0.57      inference('sup+', [status(thm)], ['4', '5'])).
% 0.39/0.57  thf(t3_boole, axiom,
% 0.39/0.57    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.39/0.57  thf('7', plain, (![X6 : $i]: ((k4_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 0.39/0.57      inference('cnf', [status(esa)], [t3_boole])).
% 0.39/0.57  thf('8', plain, (((sk_A) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.39/0.57      inference('demod', [status(thm)], ['6', '7'])).
% 0.39/0.57  thf(t52_xboole_1, axiom,
% 0.39/0.57    (![A:$i,B:$i,C:$i]:
% 0.39/0.57     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.39/0.57       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 0.39/0.57  thf('9', plain,
% 0.39/0.57      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.39/0.57         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X12 @ X13))
% 0.39/0.57           = (k2_xboole_0 @ (k4_xboole_0 @ X11 @ X12) @ 
% 0.39/0.57              (k3_xboole_0 @ X11 @ X13)))),
% 0.39/0.57      inference('cnf', [status(esa)], [t52_xboole_1])).
% 0.39/0.57  thf('10', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         ((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ X0))
% 0.39/0.57           = (k2_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_A @ X0)))),
% 0.39/0.57      inference('sup+', [status(thm)], ['8', '9'])).
% 0.39/0.57  thf('11', plain, (![X6 : $i]: ((k4_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 0.39/0.57      inference('cnf', [status(esa)], [t3_boole])).
% 0.39/0.57  thf('12', plain,
% 0.39/0.57      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.39/0.57         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X12 @ X13))
% 0.39/0.57           = (k2_xboole_0 @ (k4_xboole_0 @ X11 @ X12) @ 
% 0.39/0.57              (k3_xboole_0 @ X11 @ X13)))),
% 0.39/0.57      inference('cnf', [status(esa)], [t52_xboole_1])).
% 0.39/0.57  thf('13', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]:
% 0.39/0.57         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ k1_xboole_0 @ X1))
% 0.39/0.57           = (k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.39/0.57      inference('sup+', [status(thm)], ['11', '12'])).
% 0.39/0.57  thf(commutativity_k3_xboole_0, axiom,
% 0.39/0.57    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.39/0.57  thf('14', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.39/0.57      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.39/0.57  thf(t2_boole, axiom,
% 0.39/0.57    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.39/0.57  thf('15', plain,
% 0.39/0.57      (![X5 : $i]: ((k3_xboole_0 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 0.39/0.57      inference('cnf', [status(esa)], [t2_boole])).
% 0.39/0.57  thf('16', plain,
% 0.39/0.57      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.39/0.57      inference('sup+', [status(thm)], ['14', '15'])).
% 0.39/0.57  thf('17', plain,
% 0.39/0.57      (![X7 : $i, X8 : $i]:
% 0.39/0.57         ((k4_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8))
% 0.39/0.57           = (k4_xboole_0 @ X7 @ X8))),
% 0.39/0.57      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.39/0.57  thf('18', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         ((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0)
% 0.39/0.57           = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.39/0.57      inference('sup+', [status(thm)], ['16', '17'])).
% 0.39/0.57  thf('19', plain, (![X6 : $i]: ((k4_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 0.39/0.57      inference('cnf', [status(esa)], [t3_boole])).
% 0.39/0.57  thf('20', plain,
% 0.39/0.57      (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.39/0.57      inference('demod', [status(thm)], ['18', '19'])).
% 0.39/0.57  thf('21', plain, (![X6 : $i]: ((k4_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 0.39/0.57      inference('cnf', [status(esa)], [t3_boole])).
% 0.39/0.57  thf('22', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]:
% 0.39/0.57         ((X0) = (k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.39/0.57      inference('demod', [status(thm)], ['13', '20', '21'])).
% 0.39/0.57  thf('23', plain,
% 0.39/0.57      (![X0 : $i]: ((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)) = (sk_A))),
% 0.39/0.57      inference('demod', [status(thm)], ['10', '22'])).
% 0.39/0.57  thf('24', plain,
% 0.39/0.57      (![X9 : $i, X10 : $i]:
% 0.39/0.57         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 0.39/0.57           = (k3_xboole_0 @ X9 @ X10))),
% 0.39/0.57      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.39/0.57  thf('25', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         ((k4_xboole_0 @ sk_A @ sk_A)
% 0.39/0.57           = (k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)))),
% 0.39/0.57      inference('sup+', [status(thm)], ['23', '24'])).
% 0.39/0.57  thf('26', plain, (![X6 : $i]: ((k4_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 0.39/0.57      inference('cnf', [status(esa)], [t3_boole])).
% 0.39/0.57  thf('27', plain,
% 0.39/0.57      (![X9 : $i, X10 : $i]:
% 0.39/0.57         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 0.39/0.57           = (k3_xboole_0 @ X9 @ X10))),
% 0.39/0.57      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.39/0.57  thf('28', plain,
% 0.39/0.57      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.39/0.57      inference('sup+', [status(thm)], ['26', '27'])).
% 0.39/0.57  thf('29', plain,
% 0.39/0.57      (![X5 : $i]: ((k3_xboole_0 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 0.39/0.57      inference('cnf', [status(esa)], [t2_boole])).
% 0.39/0.57  thf('30', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.39/0.57      inference('demod', [status(thm)], ['28', '29'])).
% 0.39/0.57  thf('31', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         ((k1_xboole_0) = (k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)))),
% 0.39/0.57      inference('demod', [status(thm)], ['25', '30'])).
% 0.39/0.57  thf('32', plain,
% 0.39/0.57      (![X2 : $i, X4 : $i]:
% 0.39/0.57         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 0.39/0.57      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.39/0.57  thf('33', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         (((k1_xboole_0) != (k1_xboole_0))
% 0.39/0.57          | (r1_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)))),
% 0.39/0.57      inference('sup-', [status(thm)], ['31', '32'])).
% 0.39/0.57  thf('34', plain,
% 0.39/0.57      (![X0 : $i]: (r1_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ X0))),
% 0.39/0.57      inference('simplify', [status(thm)], ['33'])).
% 0.39/0.57  thf('35', plain,
% 0.39/0.57      (![X0 : $i]: (r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ X0))),
% 0.39/0.57      inference('sup+', [status(thm)], ['1', '34'])).
% 0.39/0.57  thf('36', plain, ($false), inference('demod', [status(thm)], ['0', '35'])).
% 0.39/0.57  
% 0.39/0.57  % SZS output end Refutation
% 0.39/0.57  
% 0.39/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
