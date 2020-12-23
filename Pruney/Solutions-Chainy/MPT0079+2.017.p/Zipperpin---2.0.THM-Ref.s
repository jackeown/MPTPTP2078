%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2YErDfH11g

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:58 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :   45 (  62 expanded)
%              Number of leaves         :   14 (  25 expanded)
%              Depth                    :   10
%              Number of atoms          :  290 ( 488 expanded)
%              Number of equality atoms :   36 (  61 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(t72_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( ( k2_xboole_0 @ A @ B )
          = ( k2_xboole_0 @ C @ D ) )
        & ( r1_xboole_0 @ C @ A )
        & ( r1_xboole_0 @ D @ B ) )
     => ( C = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( ( k2_xboole_0 @ A @ B )
            = ( k2_xboole_0 @ C @ D ) )
          & ( r1_xboole_0 @ C @ A )
          & ( r1_xboole_0 @ D @ B ) )
       => ( C = B ) ) ),
    inference('cnf.neg',[status(esa)],[t72_xboole_1])).

thf('0',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('2',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = ( k2_xboole_0 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('3',plain,(
    r1_xboole_0 @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('4',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('5',plain,
    ( ( k3_xboole_0 @ sk_D @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['3','4'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('6',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('7',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_D )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['5','6'])).

thf(t23_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf('8',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k3_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X9 @ X10 ) @ ( k3_xboole_0 @ X9 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t23_xboole_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_B @ ( k2_xboole_0 @ X0 @ sk_D ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_B @ ( k2_xboole_0 @ X0 @ sk_D ) )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_B @ sk_A ) )
    = ( k2_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['2','11'])).

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = A ) )).

thf('13',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k3_xboole_0 @ X7 @ ( k2_xboole_0 @ X7 @ X8 ) )
      = X7 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('14',plain,
    ( sk_B
    = ( k2_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = ( k2_xboole_0 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('16',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k3_xboole_0 @ X7 @ ( k2_xboole_0 @ X7 @ X8 ) )
      = X7 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('17',plain,
    ( ( k3_xboole_0 @ sk_C @ ( k2_xboole_0 @ sk_B @ sk_A ) )
    = sk_C ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    r1_xboole_0 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('20',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k3_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X9 @ X10 ) @ ( k3_xboole_0 @ X9 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t23_xboole_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_C @ ( k2_xboole_0 @ X0 @ sk_A ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ sk_C @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_C @ ( k2_xboole_0 @ X0 @ sk_A ) )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ sk_C @ X0 ) ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('26',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_C ) )
    = sk_C ),
    inference(demod,[status(thm)],['17','24','25'])).

thf('27',plain,(
    sk_B = sk_C ),
    inference('sup+',[status(thm)],['14','26'])).

thf('28',plain,(
    sk_C != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['27','28'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2YErDfH11g
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:03:51 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.45/0.69  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.45/0.69  % Solved by: fo/fo7.sh
% 0.45/0.69  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.69  % done 611 iterations in 0.238s
% 0.45/0.69  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.45/0.69  % SZS output start Refutation
% 0.45/0.69  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.45/0.69  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.45/0.69  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.69  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.69  thf(sk_C_type, type, sk_C: $i).
% 0.45/0.69  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.45/0.69  thf(sk_D_type, type, sk_D: $i).
% 0.45/0.69  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.45/0.69  thf(t72_xboole_1, conjecture,
% 0.45/0.69    (![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.69     ( ( ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ C @ D ) ) & 
% 0.45/0.69         ( r1_xboole_0 @ C @ A ) & ( r1_xboole_0 @ D @ B ) ) =>
% 0.45/0.69       ( ( C ) = ( B ) ) ))).
% 0.45/0.69  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.69    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.69        ( ( ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ C @ D ) ) & 
% 0.45/0.69            ( r1_xboole_0 @ C @ A ) & ( r1_xboole_0 @ D @ B ) ) =>
% 0.45/0.69          ( ( C ) = ( B ) ) ) )),
% 0.45/0.69    inference('cnf.neg', [status(esa)], [t72_xboole_1])).
% 0.45/0.69  thf('0', plain,
% 0.45/0.69      (((k2_xboole_0 @ sk_A @ sk_B) = (k2_xboole_0 @ sk_C @ sk_D))),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf(commutativity_k2_xboole_0, axiom,
% 0.45/0.69    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.45/0.69  thf('1', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.45/0.69      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.45/0.69  thf('2', plain,
% 0.45/0.69      (((k2_xboole_0 @ sk_B @ sk_A) = (k2_xboole_0 @ sk_C @ sk_D))),
% 0.45/0.69      inference('demod', [status(thm)], ['0', '1'])).
% 0.45/0.69  thf('3', plain, ((r1_xboole_0 @ sk_D @ sk_B)),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf(d7_xboole_0, axiom,
% 0.45/0.69    (![A:$i,B:$i]:
% 0.45/0.69     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.45/0.69       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.45/0.69  thf('4', plain,
% 0.45/0.69      (![X4 : $i, X5 : $i]:
% 0.45/0.69         (((k3_xboole_0 @ X4 @ X5) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X4 @ X5))),
% 0.45/0.69      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.45/0.69  thf('5', plain, (((k3_xboole_0 @ sk_D @ sk_B) = (k1_xboole_0))),
% 0.45/0.69      inference('sup-', [status(thm)], ['3', '4'])).
% 0.45/0.69  thf(commutativity_k3_xboole_0, axiom,
% 0.45/0.69    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.45/0.69  thf('6', plain,
% 0.45/0.69      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.45/0.69      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.45/0.69  thf('7', plain, (((k3_xboole_0 @ sk_B @ sk_D) = (k1_xboole_0))),
% 0.45/0.69      inference('demod', [status(thm)], ['5', '6'])).
% 0.45/0.69  thf(t23_xboole_1, axiom,
% 0.45/0.69    (![A:$i,B:$i,C:$i]:
% 0.45/0.69     ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) =
% 0.45/0.69       ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 0.45/0.69  thf('8', plain,
% 0.45/0.69      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.45/0.69         ((k3_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X11))
% 0.45/0.69           = (k2_xboole_0 @ (k3_xboole_0 @ X9 @ X10) @ (k3_xboole_0 @ X9 @ X11)))),
% 0.45/0.69      inference('cnf', [status(esa)], [t23_xboole_1])).
% 0.45/0.69  thf('9', plain,
% 0.45/0.69      (![X0 : $i]:
% 0.45/0.69         ((k3_xboole_0 @ sk_B @ (k2_xboole_0 @ X0 @ sk_D))
% 0.45/0.69           = (k2_xboole_0 @ (k3_xboole_0 @ sk_B @ X0) @ k1_xboole_0))),
% 0.45/0.69      inference('sup+', [status(thm)], ['7', '8'])).
% 0.45/0.69  thf('10', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.45/0.69      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.45/0.69  thf('11', plain,
% 0.45/0.69      (![X0 : $i]:
% 0.45/0.69         ((k3_xboole_0 @ sk_B @ (k2_xboole_0 @ X0 @ sk_D))
% 0.45/0.69           = (k2_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ sk_B @ X0)))),
% 0.45/0.69      inference('demod', [status(thm)], ['9', '10'])).
% 0.45/0.69  thf('12', plain,
% 0.45/0.69      (((k3_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_B @ sk_A))
% 0.45/0.69         = (k2_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_C)))),
% 0.45/0.69      inference('sup+', [status(thm)], ['2', '11'])).
% 0.45/0.69  thf(t21_xboole_1, axiom,
% 0.45/0.69    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.45/0.69  thf('13', plain,
% 0.45/0.69      (![X7 : $i, X8 : $i]:
% 0.45/0.69         ((k3_xboole_0 @ X7 @ (k2_xboole_0 @ X7 @ X8)) = (X7))),
% 0.45/0.69      inference('cnf', [status(esa)], [t21_xboole_1])).
% 0.45/0.69  thf('14', plain,
% 0.45/0.69      (((sk_B) = (k2_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_C)))),
% 0.45/0.69      inference('demod', [status(thm)], ['12', '13'])).
% 0.45/0.69  thf('15', plain,
% 0.45/0.69      (((k2_xboole_0 @ sk_B @ sk_A) = (k2_xboole_0 @ sk_C @ sk_D))),
% 0.45/0.69      inference('demod', [status(thm)], ['0', '1'])).
% 0.45/0.69  thf('16', plain,
% 0.45/0.69      (![X7 : $i, X8 : $i]:
% 0.45/0.69         ((k3_xboole_0 @ X7 @ (k2_xboole_0 @ X7 @ X8)) = (X7))),
% 0.45/0.69      inference('cnf', [status(esa)], [t21_xboole_1])).
% 0.45/0.69  thf('17', plain,
% 0.45/0.69      (((k3_xboole_0 @ sk_C @ (k2_xboole_0 @ sk_B @ sk_A)) = (sk_C))),
% 0.45/0.69      inference('sup+', [status(thm)], ['15', '16'])).
% 0.45/0.69  thf('18', plain, ((r1_xboole_0 @ sk_C @ sk_A)),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('19', plain,
% 0.45/0.69      (![X4 : $i, X5 : $i]:
% 0.45/0.69         (((k3_xboole_0 @ X4 @ X5) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X4 @ X5))),
% 0.45/0.69      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.45/0.69  thf('20', plain, (((k3_xboole_0 @ sk_C @ sk_A) = (k1_xboole_0))),
% 0.45/0.69      inference('sup-', [status(thm)], ['18', '19'])).
% 0.45/0.69  thf('21', plain,
% 0.45/0.69      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.45/0.69         ((k3_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X11))
% 0.45/0.69           = (k2_xboole_0 @ (k3_xboole_0 @ X9 @ X10) @ (k3_xboole_0 @ X9 @ X11)))),
% 0.45/0.69      inference('cnf', [status(esa)], [t23_xboole_1])).
% 0.45/0.69  thf('22', plain,
% 0.45/0.69      (![X0 : $i]:
% 0.45/0.69         ((k3_xboole_0 @ sk_C @ (k2_xboole_0 @ X0 @ sk_A))
% 0.45/0.69           = (k2_xboole_0 @ (k3_xboole_0 @ sk_C @ X0) @ k1_xboole_0))),
% 0.45/0.69      inference('sup+', [status(thm)], ['20', '21'])).
% 0.45/0.69  thf('23', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.45/0.69      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.45/0.69  thf('24', plain,
% 0.45/0.69      (![X0 : $i]:
% 0.45/0.69         ((k3_xboole_0 @ sk_C @ (k2_xboole_0 @ X0 @ sk_A))
% 0.45/0.69           = (k2_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ sk_C @ X0)))),
% 0.45/0.69      inference('demod', [status(thm)], ['22', '23'])).
% 0.45/0.69  thf('25', plain,
% 0.45/0.69      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.45/0.69      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.45/0.69  thf('26', plain,
% 0.45/0.69      (((k2_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_C)) = (sk_C))),
% 0.45/0.69      inference('demod', [status(thm)], ['17', '24', '25'])).
% 0.45/0.69  thf('27', plain, (((sk_B) = (sk_C))),
% 0.45/0.69      inference('sup+', [status(thm)], ['14', '26'])).
% 0.45/0.69  thf('28', plain, (((sk_C) != (sk_B))),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('29', plain, ($false),
% 0.45/0.69      inference('simplify_reflect-', [status(thm)], ['27', '28'])).
% 0.45/0.69  
% 0.45/0.69  % SZS output end Refutation
% 0.45/0.69  
% 0.54/0.70  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
