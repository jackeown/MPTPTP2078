%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.YjTJBUMwEs

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:26 EST 2020

% Result     : Theorem 0.41s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :   52 (  61 expanded)
%              Number of leaves         :   17 (  25 expanded)
%              Depth                    :   13
%              Number of atoms          :  338 ( 422 expanded)
%              Number of equality atoms :   36 (  45 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t78_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
        = ( k3_xboole_0 @ A @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_xboole_0 @ A @ B )
       => ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
          = ( k3_xboole_0 @ A @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t78_xboole_1])).

thf('0',plain,(
    ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
 != ( k3_xboole_0 @ sk_A @ sk_C ) ),
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

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('5',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ( ( k4_xboole_0 @ X5 @ X6 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( r1_tarski @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf('8',plain,(
    r1_tarski @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['7'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('9',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_xboole_0 @ X9 @ X8 )
        = X8 )
      | ~ ( r1_tarski @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('10',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('12',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_tarski @ X15 @ ( k2_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X5: $i,X7: $i] :
      ( ( ( k4_xboole_0 @ X5 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('16',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k4_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('17',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ( ( k4_xboole_0 @ X5 @ X6 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
       != k1_xboole_0 )
      | ( r1_tarski @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_xboole_0 @ X9 @ X8 )
        = X8 )
      | ~ ( r1_tarski @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( sk_A
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['10','24'])).

thf('26',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k4_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ X0 )
      = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ X0 ) )
      = ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ X0 )
      = ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ( k3_xboole_0 @ sk_A @ sk_C )
 != ( k3_xboole_0 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['0','31'])).

thf('33',plain,(
    $false ),
    inference(simplify,[status(thm)],['32'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.YjTJBUMwEs
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:42:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.41/0.61  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.41/0.61  % Solved by: fo/fo7.sh
% 0.41/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.41/0.61  % done 515 iterations in 0.171s
% 0.41/0.61  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.41/0.61  % SZS output start Refutation
% 0.41/0.61  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.41/0.61  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.41/0.61  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.41/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.41/0.61  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.41/0.61  thf(sk_C_type, type, sk_C: $i).
% 0.41/0.61  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.41/0.61  thf(sk_B_type, type, sk_B: $i).
% 0.41/0.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.41/0.61  thf(t78_xboole_1, conjecture,
% 0.41/0.61    (![A:$i,B:$i,C:$i]:
% 0.41/0.61     ( ( r1_xboole_0 @ A @ B ) =>
% 0.41/0.61       ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) =
% 0.41/0.61         ( k3_xboole_0 @ A @ C ) ) ))).
% 0.41/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.41/0.61    (~( ![A:$i,B:$i,C:$i]:
% 0.41/0.61        ( ( r1_xboole_0 @ A @ B ) =>
% 0.41/0.61          ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) =
% 0.41/0.61            ( k3_xboole_0 @ A @ C ) ) ) )),
% 0.41/0.61    inference('cnf.neg', [status(esa)], [t78_xboole_1])).
% 0.41/0.61  thf('0', plain,
% 0.41/0.61      (((k3_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))
% 0.41/0.61         != (k3_xboole_0 @ sk_A @ sk_C))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('1', plain, ((r1_xboole_0 @ sk_A @ sk_B)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf(d7_xboole_0, axiom,
% 0.41/0.61    (![A:$i,B:$i]:
% 0.41/0.61     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.41/0.61       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.41/0.61  thf('2', plain,
% 0.41/0.61      (![X2 : $i, X3 : $i]:
% 0.41/0.61         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.41/0.61      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.41/0.61  thf('3', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.41/0.61      inference('sup-', [status(thm)], ['1', '2'])).
% 0.41/0.61  thf(t48_xboole_1, axiom,
% 0.41/0.61    (![A:$i,B:$i]:
% 0.41/0.61     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.41/0.61  thf('4', plain,
% 0.41/0.61      (![X13 : $i, X14 : $i]:
% 0.41/0.61         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 0.41/0.61           = (k3_xboole_0 @ X13 @ X14))),
% 0.41/0.61      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.41/0.61  thf(l32_xboole_1, axiom,
% 0.41/0.61    (![A:$i,B:$i]:
% 0.41/0.61     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.41/0.61  thf('5', plain,
% 0.41/0.61      (![X5 : $i, X6 : $i]:
% 0.41/0.61         ((r1_tarski @ X5 @ X6) | ((k4_xboole_0 @ X5 @ X6) != (k1_xboole_0)))),
% 0.41/0.61      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.41/0.61  thf('6', plain,
% 0.41/0.61      (![X0 : $i, X1 : $i]:
% 0.41/0.61         (((k3_xboole_0 @ X1 @ X0) != (k1_xboole_0))
% 0.41/0.61          | (r1_tarski @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['4', '5'])).
% 0.41/0.61  thf('7', plain,
% 0.41/0.61      ((((k1_xboole_0) != (k1_xboole_0))
% 0.41/0.61        | (r1_tarski @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['3', '6'])).
% 0.41/0.61  thf('8', plain, ((r1_tarski @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B))),
% 0.41/0.61      inference('simplify', [status(thm)], ['7'])).
% 0.41/0.61  thf(t12_xboole_1, axiom,
% 0.41/0.61    (![A:$i,B:$i]:
% 0.41/0.61     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.41/0.61  thf('9', plain,
% 0.41/0.61      (![X8 : $i, X9 : $i]:
% 0.41/0.61         (((k2_xboole_0 @ X9 @ X8) = (X8)) | ~ (r1_tarski @ X9 @ X8))),
% 0.41/0.61      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.41/0.61  thf('10', plain,
% 0.41/0.61      (((k2_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B))
% 0.41/0.61         = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.41/0.61      inference('sup-', [status(thm)], ['8', '9'])).
% 0.41/0.61  thf(commutativity_k2_xboole_0, axiom,
% 0.41/0.61    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.41/0.61  thf('11', plain,
% 0.41/0.61      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.41/0.61      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.41/0.61  thf(t7_xboole_1, axiom,
% 0.41/0.61    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.41/0.61  thf('12', plain,
% 0.41/0.61      (![X15 : $i, X16 : $i]: (r1_tarski @ X15 @ (k2_xboole_0 @ X15 @ X16))),
% 0.41/0.61      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.41/0.61  thf('13', plain,
% 0.41/0.61      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.41/0.61      inference('sup+', [status(thm)], ['11', '12'])).
% 0.41/0.61  thf('14', plain,
% 0.41/0.61      (![X5 : $i, X7 : $i]:
% 0.41/0.61         (((k4_xboole_0 @ X5 @ X7) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ X7))),
% 0.41/0.61      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.41/0.61  thf('15', plain,
% 0.41/0.61      (![X0 : $i, X1 : $i]:
% 0.41/0.61         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.41/0.61      inference('sup-', [status(thm)], ['13', '14'])).
% 0.41/0.61  thf(t41_xboole_1, axiom,
% 0.41/0.61    (![A:$i,B:$i,C:$i]:
% 0.41/0.61     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.41/0.61       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.41/0.61  thf('16', plain,
% 0.41/0.61      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.41/0.61         ((k4_xboole_0 @ (k4_xboole_0 @ X10 @ X11) @ X12)
% 0.41/0.61           = (k4_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 0.41/0.61      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.41/0.61  thf('17', plain,
% 0.41/0.61      (![X5 : $i, X6 : $i]:
% 0.41/0.61         ((r1_tarski @ X5 @ X6) | ((k4_xboole_0 @ X5 @ X6) != (k1_xboole_0)))),
% 0.41/0.61      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.41/0.61  thf('18', plain,
% 0.41/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.61         (((k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) != (k1_xboole_0))
% 0.41/0.61          | (r1_tarski @ (k4_xboole_0 @ X2 @ X1) @ X0))),
% 0.41/0.61      inference('sup-', [status(thm)], ['16', '17'])).
% 0.41/0.61  thf('19', plain,
% 0.41/0.61      (![X0 : $i, X1 : $i]:
% 0.41/0.61         (((k1_xboole_0) != (k1_xboole_0))
% 0.41/0.61          | (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0))),
% 0.41/0.61      inference('sup-', [status(thm)], ['15', '18'])).
% 0.41/0.61  thf('20', plain,
% 0.41/0.61      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0)),
% 0.41/0.61      inference('simplify', [status(thm)], ['19'])).
% 0.41/0.61  thf('21', plain,
% 0.41/0.61      (![X8 : $i, X9 : $i]:
% 0.41/0.61         (((k2_xboole_0 @ X9 @ X8) = (X8)) | ~ (r1_tarski @ X9 @ X8))),
% 0.41/0.61      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.41/0.61  thf('22', plain,
% 0.41/0.61      (![X0 : $i, X1 : $i]:
% 0.41/0.61         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 0.41/0.61      inference('sup-', [status(thm)], ['20', '21'])).
% 0.41/0.61  thf('23', plain,
% 0.41/0.61      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.41/0.61      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.41/0.61  thf('24', plain,
% 0.41/0.61      (![X0 : $i, X1 : $i]:
% 0.41/0.61         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)) = (X0))),
% 0.41/0.61      inference('demod', [status(thm)], ['22', '23'])).
% 0.41/0.61  thf('25', plain, (((sk_A) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.41/0.61      inference('demod', [status(thm)], ['10', '24'])).
% 0.41/0.61  thf('26', plain,
% 0.41/0.61      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.41/0.61         ((k4_xboole_0 @ (k4_xboole_0 @ X10 @ X11) @ X12)
% 0.41/0.61           = (k4_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 0.41/0.61      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.41/0.61  thf('27', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         ((k4_xboole_0 @ sk_A @ X0)
% 0.41/0.61           = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ X0)))),
% 0.41/0.61      inference('sup+', [status(thm)], ['25', '26'])).
% 0.41/0.61  thf('28', plain,
% 0.41/0.61      (![X13 : $i, X14 : $i]:
% 0.41/0.61         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 0.41/0.61           = (k3_xboole_0 @ X13 @ X14))),
% 0.41/0.61      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.41/0.61  thf('29', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         ((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ X0))
% 0.41/0.61           = (k3_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ X0)))),
% 0.41/0.61      inference('sup+', [status(thm)], ['27', '28'])).
% 0.41/0.61  thf('30', plain,
% 0.41/0.61      (![X13 : $i, X14 : $i]:
% 0.41/0.61         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 0.41/0.61           = (k3_xboole_0 @ X13 @ X14))),
% 0.41/0.61      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.41/0.61  thf('31', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         ((k3_xboole_0 @ sk_A @ X0)
% 0.41/0.61           = (k3_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ X0)))),
% 0.41/0.61      inference('demod', [status(thm)], ['29', '30'])).
% 0.41/0.61  thf('32', plain,
% 0.41/0.61      (((k3_xboole_0 @ sk_A @ sk_C) != (k3_xboole_0 @ sk_A @ sk_C))),
% 0.41/0.61      inference('demod', [status(thm)], ['0', '31'])).
% 0.41/0.61  thf('33', plain, ($false), inference('simplify', [status(thm)], ['32'])).
% 0.41/0.61  
% 0.41/0.61  % SZS output end Refutation
% 0.41/0.61  
% 0.41/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
