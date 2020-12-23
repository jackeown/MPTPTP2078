%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.T6NIxfptRP

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:14 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   54 (  80 expanded)
%              Number of leaves         :   16 (  31 expanded)
%              Depth                    :   14
%              Number of atoms          :  318 ( 496 expanded)
%              Number of equality atoms :   36 (  59 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(t75_xboole_1,conjecture,(
    ! [A: $i,B: $i] :
      ~ ( ~ ( r1_xboole_0 @ A @ B )
        & ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t75_xboole_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('2',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ~ ( r1_xboole_0 @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('3',plain,(
    r1_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('4',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('5',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ sk_B ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('6',plain,(
    ! [X9: $i] :
      ( ( k4_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('7',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('9',plain,(
    ! [X8: $i] :
      ( ( k3_xboole_0 @ X8 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['8','9'])).

thf(t54_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ C ) ) ) )).

thf('11',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k3_xboole_0 @ X13 @ X14 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ ( k4_xboole_0 @ X12 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t54_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('14',plain,(
    ! [X7: $i] :
      ( ( k2_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['12','15'])).

thf('17',plain,
    ( ( k4_xboole_0 @ sk_B @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['5','16'])).

thf('18',plain,(
    ! [X9: $i] :
      ( ( k4_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('19',plain,
    ( sk_B
    = ( k4_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('21',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k3_xboole_0 @ X13 @ X14 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ ( k4_xboole_0 @ X12 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t54_xboole_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('26',plain,
    ( sk_B
    = ( k4_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['19','25'])).

thf('27',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('28',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_B )
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('30',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('32',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    r1_xboole_0 @ sk_B @ sk_A ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ~ ( r1_xboole_0 @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('35',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    $false ),
    inference(demod,[status(thm)],['0','35'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.T6NIxfptRP
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:45:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.52  % Solved by: fo/fo7.sh
% 0.20/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.52  % done 154 iterations in 0.061s
% 0.20/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.52  % SZS output start Refutation
% 0.20/0.52  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.52  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.52  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.52  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.52  thf(t75_xboole_1, conjecture,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.20/0.52          ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ B ) ) ))).
% 0.20/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.52    (~( ![A:$i,B:$i]:
% 0.20/0.52        ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.20/0.52             ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ B ) ) ) )),
% 0.20/0.52    inference('cnf.neg', [status(esa)], [t75_xboole_1])).
% 0.20/0.52  thf('0', plain, (~ (r1_xboole_0 @ sk_A @ sk_B)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('1', plain, ((r1_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B) @ sk_B)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(symmetry_r1_xboole_0, axiom,
% 0.20/0.52    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.20/0.52  thf('2', plain,
% 0.20/0.52      (![X5 : $i, X6 : $i]:
% 0.20/0.52         ((r1_xboole_0 @ X5 @ X6) | ~ (r1_xboole_0 @ X6 @ X5))),
% 0.20/0.52      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.20/0.52  thf('3', plain, ((r1_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_A @ sk_B))),
% 0.20/0.52      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.52  thf(d7_xboole_0, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.20/0.52       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.52  thf('4', plain,
% 0.20/0.52      (![X2 : $i, X3 : $i]:
% 0.20/0.52         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.20/0.52      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.20/0.52  thf('5', plain,
% 0.20/0.52      (((k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_A @ sk_B)) = (k1_xboole_0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.52  thf(t3_boole, axiom,
% 0.20/0.52    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.20/0.52  thf('6', plain, (![X9 : $i]: ((k4_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 0.20/0.52      inference('cnf', [status(esa)], [t3_boole])).
% 0.20/0.52  thf(t48_xboole_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.20/0.52  thf('7', plain,
% 0.20/0.52      (![X10 : $i, X11 : $i]:
% 0.20/0.52         ((k4_xboole_0 @ X10 @ (k4_xboole_0 @ X10 @ X11))
% 0.20/0.52           = (k3_xboole_0 @ X10 @ X11))),
% 0.20/0.52      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.20/0.52  thf('8', plain,
% 0.20/0.52      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.20/0.52      inference('sup+', [status(thm)], ['6', '7'])).
% 0.20/0.52  thf(t2_boole, axiom,
% 0.20/0.52    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.20/0.52  thf('9', plain,
% 0.20/0.52      (![X8 : $i]: ((k3_xboole_0 @ X8 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.52      inference('cnf', [status(esa)], [t2_boole])).
% 0.20/0.52  thf('10', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.20/0.52      inference('demod', [status(thm)], ['8', '9'])).
% 0.20/0.52  thf(t54_xboole_1, axiom,
% 0.20/0.52    (![A:$i,B:$i,C:$i]:
% 0.20/0.52     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) =
% 0.20/0.52       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ C ) ) ))).
% 0.20/0.52  thf('11', plain,
% 0.20/0.52      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.20/0.52         ((k4_xboole_0 @ X12 @ (k3_xboole_0 @ X13 @ X14))
% 0.20/0.52           = (k2_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ 
% 0.20/0.52              (k4_xboole_0 @ X12 @ X14)))),
% 0.20/0.52      inference('cnf', [status(esa)], [t54_xboole_1])).
% 0.20/0.52  thf('12', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.20/0.52           = (k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.20/0.52      inference('sup+', [status(thm)], ['10', '11'])).
% 0.20/0.52  thf(commutativity_k2_xboole_0, axiom,
% 0.20/0.52    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.20/0.52  thf('13', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.20/0.52      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.20/0.52  thf(t1_boole, axiom,
% 0.20/0.52    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.20/0.52  thf('14', plain, (![X7 : $i]: ((k2_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 0.20/0.52      inference('cnf', [status(esa)], [t1_boole])).
% 0.20/0.52  thf('15', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.20/0.52      inference('sup+', [status(thm)], ['13', '14'])).
% 0.20/0.52  thf('16', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.20/0.52           = (k4_xboole_0 @ X1 @ X0))),
% 0.20/0.52      inference('demod', [status(thm)], ['12', '15'])).
% 0.20/0.52  thf('17', plain,
% 0.20/0.52      (((k4_xboole_0 @ sk_B @ k1_xboole_0)
% 0.20/0.52         = (k4_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.20/0.52      inference('sup+', [status(thm)], ['5', '16'])).
% 0.20/0.52  thf('18', plain, (![X9 : $i]: ((k4_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 0.20/0.52      inference('cnf', [status(esa)], [t3_boole])).
% 0.20/0.52  thf('19', plain,
% 0.20/0.52      (((sk_B) = (k4_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.20/0.52      inference('demod', [status(thm)], ['17', '18'])).
% 0.20/0.52  thf('20', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.20/0.52      inference('demod', [status(thm)], ['8', '9'])).
% 0.20/0.52  thf('21', plain,
% 0.20/0.52      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.20/0.52         ((k4_xboole_0 @ X12 @ (k3_xboole_0 @ X13 @ X14))
% 0.20/0.52           = (k2_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ 
% 0.20/0.52              (k4_xboole_0 @ X12 @ X14)))),
% 0.20/0.52      inference('cnf', [status(esa)], [t54_xboole_1])).
% 0.20/0.52  thf('22', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 0.20/0.52           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ k1_xboole_0))),
% 0.20/0.52      inference('sup+', [status(thm)], ['20', '21'])).
% 0.20/0.52  thf('23', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.20/0.52      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.20/0.52  thf('24', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.20/0.52      inference('sup+', [status(thm)], ['13', '14'])).
% 0.20/0.52  thf('25', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 0.20/0.52           = (k4_xboole_0 @ X0 @ X1))),
% 0.20/0.52      inference('demod', [status(thm)], ['22', '23', '24'])).
% 0.20/0.52  thf('26', plain, (((sk_B) = (k4_xboole_0 @ sk_B @ sk_A))),
% 0.20/0.52      inference('demod', [status(thm)], ['19', '25'])).
% 0.20/0.52  thf('27', plain,
% 0.20/0.52      (![X10 : $i, X11 : $i]:
% 0.20/0.52         ((k4_xboole_0 @ X10 @ (k4_xboole_0 @ X10 @ X11))
% 0.20/0.52           = (k3_xboole_0 @ X10 @ X11))),
% 0.20/0.52      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.20/0.52  thf('28', plain,
% 0.20/0.52      (((k4_xboole_0 @ sk_B @ sk_B) = (k3_xboole_0 @ sk_B @ sk_A))),
% 0.20/0.52      inference('sup+', [status(thm)], ['26', '27'])).
% 0.20/0.52  thf('29', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.20/0.52      inference('demod', [status(thm)], ['8', '9'])).
% 0.20/0.52  thf('30', plain, (((k1_xboole_0) = (k3_xboole_0 @ sk_B @ sk_A))),
% 0.20/0.52      inference('demod', [status(thm)], ['28', '29'])).
% 0.20/0.52  thf('31', plain,
% 0.20/0.52      (![X2 : $i, X4 : $i]:
% 0.20/0.52         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 0.20/0.52      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.20/0.52  thf('32', plain,
% 0.20/0.52      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ sk_B @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['30', '31'])).
% 0.20/0.52  thf('33', plain, ((r1_xboole_0 @ sk_B @ sk_A)),
% 0.20/0.52      inference('simplify', [status(thm)], ['32'])).
% 0.20/0.52  thf('34', plain,
% 0.20/0.52      (![X5 : $i, X6 : $i]:
% 0.20/0.52         ((r1_xboole_0 @ X5 @ X6) | ~ (r1_xboole_0 @ X6 @ X5))),
% 0.20/0.52      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.20/0.52  thf('35', plain, ((r1_xboole_0 @ sk_A @ sk_B)),
% 0.20/0.52      inference('sup-', [status(thm)], ['33', '34'])).
% 0.20/0.52  thf('36', plain, ($false), inference('demod', [status(thm)], ['0', '35'])).
% 0.20/0.52  
% 0.20/0.52  % SZS output end Refutation
% 0.20/0.52  
% 0.36/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
