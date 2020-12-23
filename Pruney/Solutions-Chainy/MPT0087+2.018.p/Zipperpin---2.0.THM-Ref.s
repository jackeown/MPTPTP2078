%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.mbeHbbOGfS

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:34 EST 2020

% Result     : Theorem 0.52s
% Output     : Refutation 0.52s
% Verified   : 
% Statistics : Number of formulae       :   60 (  88 expanded)
%              Number of leaves         :   16 (  34 expanded)
%              Depth                    :   13
%              Number of atoms          :  389 ( 602 expanded)
%              Number of equality atoms :   41 (  63 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

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

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('2',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k3_xboole_0 @ X9 @ X10 ) )
      = ( k4_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('7',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X6 @ X7 ) @ X8 )
      = ( k4_xboole_0 @ X6 @ ( k2_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('9',plain,(
    ! [X5: $i] :
      ( ( k4_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('10',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X5: $i] :
      ( ( k4_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('13',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X13 @ X14 ) @ X14 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['11','16'])).

thf('18',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X6 @ X7 ) @ X8 )
      = ( k4_xboole_0 @ X6 @ ( k2_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('20',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ X3 @ ( k4_xboole_0 @ X4 @ X3 ) )
      = ( k2_xboole_0 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','21'])).

thf('23',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ X3 @ ( k4_xboole_0 @ X4 @ X3 ) )
      = ( k2_xboole_0 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('24',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('26',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k3_xboole_0 @ X9 @ X10 ) )
      = ( k4_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('28',plain,
    ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X5: $i] :
      ( ( k4_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('30',plain,
    ( sk_A
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X6 @ X7 ) @ X8 )
      = ( k4_xboole_0 @ X6 @ ( k2_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ X0 )
      = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ sk_B ) )
      = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['23','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ X0 )
      = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ sk_B ) )
      = ( k4_xboole_0 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
      = ( k4_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['22','35'])).

thf('37',plain,(
    ! [X5: $i] :
      ( ( k4_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('38',plain,(
    ! [X0: $i] :
      ( sk_A
      = ( k4_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X13 @ X14 ) @ X14 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','40'])).

thf('42',plain,(
    $false ),
    inference(demod,[status(thm)],['0','41'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.mbeHbbOGfS
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:50:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.52/0.74  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.52/0.74  % Solved by: fo/fo7.sh
% 0.52/0.74  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.52/0.74  % done 517 iterations in 0.287s
% 0.52/0.74  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.52/0.74  % SZS output start Refutation
% 0.52/0.74  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.52/0.74  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.52/0.74  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.52/0.74  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.52/0.74  thf(sk_B_type, type, sk_B: $i).
% 0.52/0.74  thf(sk_A_type, type, sk_A: $i).
% 0.52/0.74  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.52/0.74  thf(sk_C_type, type, sk_C: $i).
% 0.52/0.74  thf(t80_xboole_1, conjecture,
% 0.52/0.74    (![A:$i,B:$i,C:$i]:
% 0.52/0.74     ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) ))).
% 0.52/0.74  thf(zf_stmt_0, negated_conjecture,
% 0.52/0.74    (~( ![A:$i,B:$i,C:$i]:
% 0.52/0.74        ( ( r1_xboole_0 @ A @ B ) =>
% 0.52/0.74          ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) ) )),
% 0.52/0.74    inference('cnf.neg', [status(esa)], [t80_xboole_1])).
% 0.52/0.74  thf('0', plain, (~ (r1_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))),
% 0.52/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.74  thf(t48_xboole_1, axiom,
% 0.52/0.74    (![A:$i,B:$i]:
% 0.52/0.74     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.52/0.74  thf('1', plain,
% 0.52/0.74      (![X11 : $i, X12 : $i]:
% 0.52/0.74         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 0.52/0.74           = (k3_xboole_0 @ X11 @ X12))),
% 0.52/0.74      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.52/0.74  thf('2', plain,
% 0.52/0.74      (![X11 : $i, X12 : $i]:
% 0.52/0.74         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 0.52/0.74           = (k3_xboole_0 @ X11 @ X12))),
% 0.52/0.74      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.52/0.74  thf('3', plain,
% 0.52/0.74      (![X0 : $i, X1 : $i]:
% 0.52/0.74         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.52/0.74           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.52/0.74      inference('sup+', [status(thm)], ['1', '2'])).
% 0.52/0.74  thf(t47_xboole_1, axiom,
% 0.52/0.74    (![A:$i,B:$i]:
% 0.52/0.74     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.52/0.74  thf('4', plain,
% 0.52/0.74      (![X9 : $i, X10 : $i]:
% 0.52/0.74         ((k4_xboole_0 @ X9 @ (k3_xboole_0 @ X9 @ X10))
% 0.52/0.74           = (k4_xboole_0 @ X9 @ X10))),
% 0.52/0.74      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.52/0.74  thf('5', plain,
% 0.52/0.74      (![X0 : $i, X1 : $i]:
% 0.52/0.74         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 0.52/0.74           = (k4_xboole_0 @ X1 @ X0))),
% 0.52/0.74      inference('sup+', [status(thm)], ['3', '4'])).
% 0.52/0.74  thf('6', plain,
% 0.52/0.74      (![X11 : $i, X12 : $i]:
% 0.52/0.74         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 0.52/0.74           = (k3_xboole_0 @ X11 @ X12))),
% 0.52/0.74      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.52/0.74  thf(t41_xboole_1, axiom,
% 0.52/0.74    (![A:$i,B:$i,C:$i]:
% 0.52/0.74     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.52/0.74       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.52/0.74  thf('7', plain,
% 0.52/0.74      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.52/0.74         ((k4_xboole_0 @ (k4_xboole_0 @ X6 @ X7) @ X8)
% 0.52/0.74           = (k4_xboole_0 @ X6 @ (k2_xboole_0 @ X7 @ X8)))),
% 0.52/0.74      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.52/0.74  thf('8', plain,
% 0.52/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.74         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 0.52/0.74           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)))),
% 0.52/0.75      inference('sup+', [status(thm)], ['6', '7'])).
% 0.52/0.75  thf(t3_boole, axiom,
% 0.52/0.75    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.52/0.75  thf('9', plain, (![X5 : $i]: ((k4_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 0.52/0.75      inference('cnf', [status(esa)], [t3_boole])).
% 0.52/0.75  thf('10', plain,
% 0.52/0.75      (![X11 : $i, X12 : $i]:
% 0.52/0.75         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 0.52/0.75           = (k3_xboole_0 @ X11 @ X12))),
% 0.52/0.75      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.52/0.75  thf('11', plain,
% 0.52/0.75      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.52/0.75      inference('sup+', [status(thm)], ['9', '10'])).
% 0.52/0.75  thf('12', plain, (![X5 : $i]: ((k4_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 0.52/0.75      inference('cnf', [status(esa)], [t3_boole])).
% 0.52/0.75  thf(t79_xboole_1, axiom,
% 0.52/0.75    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.52/0.75  thf('13', plain,
% 0.52/0.75      (![X13 : $i, X14 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X13 @ X14) @ X14)),
% 0.52/0.75      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.52/0.75  thf('14', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.52/0.75      inference('sup+', [status(thm)], ['12', '13'])).
% 0.52/0.75  thf(d7_xboole_0, axiom,
% 0.52/0.75    (![A:$i,B:$i]:
% 0.52/0.75     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.52/0.75       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.52/0.75  thf('15', plain,
% 0.52/0.75      (![X0 : $i, X1 : $i]:
% 0.52/0.75         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.52/0.75      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.52/0.75  thf('16', plain,
% 0.52/0.75      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.52/0.75      inference('sup-', [status(thm)], ['14', '15'])).
% 0.52/0.75  thf('17', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.52/0.75      inference('demod', [status(thm)], ['11', '16'])).
% 0.52/0.75  thf('18', plain,
% 0.52/0.75      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.52/0.75         ((k4_xboole_0 @ (k4_xboole_0 @ X6 @ X7) @ X8)
% 0.52/0.75           = (k4_xboole_0 @ X6 @ (k2_xboole_0 @ X7 @ X8)))),
% 0.52/0.75      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.52/0.75  thf('19', plain,
% 0.52/0.75      (![X0 : $i, X1 : $i]:
% 0.52/0.75         ((k1_xboole_0)
% 0.52/0.75           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))))),
% 0.52/0.75      inference('sup+', [status(thm)], ['17', '18'])).
% 0.52/0.75  thf(t39_xboole_1, axiom,
% 0.52/0.75    (![A:$i,B:$i]:
% 0.52/0.75     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.52/0.75  thf('20', plain,
% 0.52/0.75      (![X3 : $i, X4 : $i]:
% 0.52/0.75         ((k2_xboole_0 @ X3 @ (k4_xboole_0 @ X4 @ X3))
% 0.52/0.75           = (k2_xboole_0 @ X3 @ X4))),
% 0.52/0.75      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.52/0.75  thf('21', plain,
% 0.52/0.75      (![X0 : $i, X1 : $i]:
% 0.52/0.75         ((k1_xboole_0) = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1)))),
% 0.52/0.75      inference('demod', [status(thm)], ['19', '20'])).
% 0.52/0.75  thf('22', plain,
% 0.52/0.75      (![X0 : $i, X1 : $i]:
% 0.52/0.75         ((k1_xboole_0) = (k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0))),
% 0.52/0.75      inference('sup+', [status(thm)], ['8', '21'])).
% 0.52/0.75  thf('23', plain,
% 0.52/0.75      (![X3 : $i, X4 : $i]:
% 0.52/0.75         ((k2_xboole_0 @ X3 @ (k4_xboole_0 @ X4 @ X3))
% 0.52/0.75           = (k2_xboole_0 @ X3 @ X4))),
% 0.52/0.75      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.52/0.75  thf('24', plain, ((r1_xboole_0 @ sk_A @ sk_B)),
% 0.52/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.75  thf('25', plain,
% 0.52/0.75      (![X0 : $i, X1 : $i]:
% 0.52/0.75         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.52/0.75      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.52/0.75  thf('26', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.52/0.75      inference('sup-', [status(thm)], ['24', '25'])).
% 0.52/0.75  thf('27', plain,
% 0.52/0.75      (![X9 : $i, X10 : $i]:
% 0.52/0.75         ((k4_xboole_0 @ X9 @ (k3_xboole_0 @ X9 @ X10))
% 0.52/0.75           = (k4_xboole_0 @ X9 @ X10))),
% 0.52/0.75      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.52/0.75  thf('28', plain,
% 0.52/0.75      (((k4_xboole_0 @ sk_A @ k1_xboole_0) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.52/0.75      inference('sup+', [status(thm)], ['26', '27'])).
% 0.52/0.75  thf('29', plain, (![X5 : $i]: ((k4_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 0.52/0.75      inference('cnf', [status(esa)], [t3_boole])).
% 0.52/0.75  thf('30', plain, (((sk_A) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.52/0.75      inference('demod', [status(thm)], ['28', '29'])).
% 0.52/0.75  thf('31', plain,
% 0.52/0.75      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.52/0.75         ((k4_xboole_0 @ (k4_xboole_0 @ X6 @ X7) @ X8)
% 0.52/0.75           = (k4_xboole_0 @ X6 @ (k2_xboole_0 @ X7 @ X8)))),
% 0.52/0.75      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.52/0.75  thf('32', plain,
% 0.52/0.75      (![X0 : $i]:
% 0.52/0.75         ((k4_xboole_0 @ sk_A @ X0)
% 0.52/0.75           = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ X0)))),
% 0.52/0.75      inference('sup+', [status(thm)], ['30', '31'])).
% 0.52/0.75  thf('33', plain,
% 0.52/0.75      (![X0 : $i]:
% 0.52/0.75         ((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ X0 @ sk_B))
% 0.52/0.75           = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ X0)))),
% 0.52/0.75      inference('sup+', [status(thm)], ['23', '32'])).
% 0.52/0.75  thf('34', plain,
% 0.52/0.75      (![X0 : $i]:
% 0.52/0.75         ((k4_xboole_0 @ sk_A @ X0)
% 0.52/0.75           = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ X0)))),
% 0.52/0.75      inference('sup+', [status(thm)], ['30', '31'])).
% 0.52/0.75  thf('35', plain,
% 0.52/0.75      (![X0 : $i]:
% 0.52/0.75         ((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ X0 @ sk_B))
% 0.52/0.75           = (k4_xboole_0 @ sk_A @ X0))),
% 0.52/0.75      inference('demod', [status(thm)], ['33', '34'])).
% 0.52/0.75  thf('36', plain,
% 0.52/0.75      (![X0 : $i]:
% 0.52/0.75         ((k4_xboole_0 @ sk_A @ k1_xboole_0)
% 0.52/0.75           = (k4_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ X0)))),
% 0.52/0.75      inference('sup+', [status(thm)], ['22', '35'])).
% 0.52/0.75  thf('37', plain, (![X5 : $i]: ((k4_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 0.52/0.75      inference('cnf', [status(esa)], [t3_boole])).
% 0.52/0.75  thf('38', plain,
% 0.52/0.75      (![X0 : $i]: ((sk_A) = (k4_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ X0)))),
% 0.52/0.75      inference('demod', [status(thm)], ['36', '37'])).
% 0.52/0.75  thf('39', plain,
% 0.52/0.75      (![X13 : $i, X14 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X13 @ X14) @ X14)),
% 0.52/0.75      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.52/0.75  thf('40', plain,
% 0.52/0.75      (![X0 : $i]: (r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ X0))),
% 0.52/0.75      inference('sup+', [status(thm)], ['38', '39'])).
% 0.52/0.75  thf('41', plain,
% 0.52/0.75      (![X0 : $i]: (r1_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ X0))),
% 0.52/0.75      inference('sup+', [status(thm)], ['5', '40'])).
% 0.52/0.75  thf('42', plain, ($false), inference('demod', [status(thm)], ['0', '41'])).
% 0.52/0.75  
% 0.52/0.75  % SZS output end Refutation
% 0.52/0.75  
% 0.52/0.76  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
