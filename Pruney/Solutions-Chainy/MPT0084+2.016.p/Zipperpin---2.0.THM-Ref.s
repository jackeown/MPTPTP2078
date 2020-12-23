%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hHJZWZSQIo

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:20 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   53 (  79 expanded)
%              Number of leaves         :   18 (  31 expanded)
%              Depth                    :   14
%              Number of atoms          :  323 ( 538 expanded)
%              Number of equality atoms :   35 (  54 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t77_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r1_xboole_0 @ A @ B )
        & ( r1_tarski @ A @ C )
        & ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ( r1_tarski @ A @ C )
          & ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t77_xboole_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ),
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
    ( ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r1_tarski @ sk_A @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('5',plain,(
    ! [X5: $i,X7: $i] :
      ( ( ( k4_xboole_0 @ X5 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('6',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t52_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf('7',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X16 @ X17 ) @ ( k3_xboole_0 @ X16 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_C @ X0 ) )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ sk_A @ X0 ) ) ) ),
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

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('10',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X14 @ X15 ) @ ( k4_xboole_0 @ X14 @ X15 ) )
      = X14 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('12',plain,(
    ! [X9: $i] :
      ( ( k4_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_C @ X0 ) )
      = ( k3_xboole_0 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['8','13'])).

thf('15',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ( ( k4_xboole_0 @ X5 @ X6 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ sk_A @ X0 )
       != k1_xboole_0 )
      | ( r1_tarski @ sk_A @ ( k4_xboole_0 @ sk_C @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_A @ ( k4_xboole_0 @ sk_C @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['3','16'])).

thf('18',plain,(
    r1_tarski @ sk_A @ ( k4_xboole_0 @ sk_C @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('20',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) )
      = ( k4_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    r1_tarski @ sk_A @ ( k4_xboole_0 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X5: $i,X7: $i] :
      ( ( ( k4_xboole_0 @ X5 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('24',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_C @ sk_B ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_C @ X0 ) )
      = ( k3_xboole_0 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['8','13'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('27',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('29',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf('32',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    $false ),
    inference(demod,[status(thm)],['0','32'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hHJZWZSQIo
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:28:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.19/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.49  % Solved by: fo/fo7.sh
% 0.19/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.49  % done 96 iterations in 0.039s
% 0.19/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.49  % SZS output start Refutation
% 0.19/0.49  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.19/0.49  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.19/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.19/0.49  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.19/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.49  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.19/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.49  thf(t77_xboole_1, conjecture,
% 0.19/0.49    (![A:$i,B:$i,C:$i]:
% 0.19/0.49     ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & ( r1_tarski @ A @ C ) & 
% 0.19/0.49          ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) ))).
% 0.19/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.49    (~( ![A:$i,B:$i,C:$i]:
% 0.19/0.49        ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & ( r1_tarski @ A @ C ) & 
% 0.19/0.49             ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) ) )),
% 0.19/0.49    inference('cnf.neg', [status(esa)], [t77_xboole_1])).
% 0.19/0.49  thf('0', plain, (~ (r1_xboole_0 @ sk_A @ sk_B)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('1', plain, ((r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf(d7_xboole_0, axiom,
% 0.19/0.49    (![A:$i,B:$i]:
% 0.19/0.49     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.19/0.49       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.19/0.49  thf('2', plain,
% 0.19/0.49      (![X2 : $i, X3 : $i]:
% 0.19/0.49         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.19/0.49      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.19/0.49  thf('3', plain,
% 0.19/0.49      (((k3_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)) = (k1_xboole_0))),
% 0.19/0.49      inference('sup-', [status(thm)], ['1', '2'])).
% 0.19/0.49  thf('4', plain, ((r1_tarski @ sk_A @ sk_C)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf(l32_xboole_1, axiom,
% 0.19/0.49    (![A:$i,B:$i]:
% 0.19/0.49     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.19/0.49  thf('5', plain,
% 0.19/0.49      (![X5 : $i, X7 : $i]:
% 0.19/0.49         (((k4_xboole_0 @ X5 @ X7) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ X7))),
% 0.19/0.49      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.19/0.49  thf('6', plain, (((k4_xboole_0 @ sk_A @ sk_C) = (k1_xboole_0))),
% 0.19/0.49      inference('sup-', [status(thm)], ['4', '5'])).
% 0.19/0.49  thf(t52_xboole_1, axiom,
% 0.19/0.49    (![A:$i,B:$i,C:$i]:
% 0.19/0.49     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.19/0.49       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 0.19/0.49  thf('7', plain,
% 0.19/0.49      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.19/0.49         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X18))
% 0.19/0.49           = (k2_xboole_0 @ (k4_xboole_0 @ X16 @ X17) @ 
% 0.19/0.49              (k3_xboole_0 @ X16 @ X18)))),
% 0.19/0.49      inference('cnf', [status(esa)], [t52_xboole_1])).
% 0.19/0.49  thf('8', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         ((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_C @ X0))
% 0.19/0.49           = (k2_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ sk_A @ X0)))),
% 0.19/0.49      inference('sup+', [status(thm)], ['6', '7'])).
% 0.19/0.49  thf(t2_boole, axiom,
% 0.19/0.49    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.19/0.49  thf('9', plain,
% 0.19/0.49      (![X8 : $i]: ((k3_xboole_0 @ X8 @ k1_xboole_0) = (k1_xboole_0))),
% 0.19/0.49      inference('cnf', [status(esa)], [t2_boole])).
% 0.19/0.49  thf(t51_xboole_1, axiom,
% 0.19/0.49    (![A:$i,B:$i]:
% 0.19/0.49     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 0.19/0.49       ( A ) ))).
% 0.19/0.49  thf('10', plain,
% 0.19/0.49      (![X14 : $i, X15 : $i]:
% 0.19/0.49         ((k2_xboole_0 @ (k3_xboole_0 @ X14 @ X15) @ (k4_xboole_0 @ X14 @ X15))
% 0.19/0.49           = (X14))),
% 0.19/0.49      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.19/0.49  thf('11', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         ((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ X0 @ k1_xboole_0)) = (X0))),
% 0.19/0.49      inference('sup+', [status(thm)], ['9', '10'])).
% 0.19/0.49  thf(t3_boole, axiom,
% 0.19/0.49    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.19/0.49  thf('12', plain, (![X9 : $i]: ((k4_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 0.19/0.49      inference('cnf', [status(esa)], [t3_boole])).
% 0.19/0.49  thf('13', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.19/0.49      inference('demod', [status(thm)], ['11', '12'])).
% 0.19/0.49  thf('14', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         ((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_C @ X0))
% 0.19/0.49           = (k3_xboole_0 @ sk_A @ X0))),
% 0.19/0.49      inference('demod', [status(thm)], ['8', '13'])).
% 0.19/0.49  thf('15', plain,
% 0.19/0.49      (![X5 : $i, X6 : $i]:
% 0.19/0.49         ((r1_tarski @ X5 @ X6) | ((k4_xboole_0 @ X5 @ X6) != (k1_xboole_0)))),
% 0.19/0.49      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.19/0.49  thf('16', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         (((k3_xboole_0 @ sk_A @ X0) != (k1_xboole_0))
% 0.19/0.49          | (r1_tarski @ sk_A @ (k4_xboole_0 @ sk_C @ X0)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['14', '15'])).
% 0.19/0.49  thf('17', plain,
% 0.19/0.49      ((((k1_xboole_0) != (k1_xboole_0))
% 0.19/0.49        | (r1_tarski @ sk_A @ 
% 0.19/0.49           (k4_xboole_0 @ sk_C @ (k3_xboole_0 @ sk_B @ sk_C))))),
% 0.19/0.49      inference('sup-', [status(thm)], ['3', '16'])).
% 0.19/0.49  thf('18', plain,
% 0.19/0.49      ((r1_tarski @ sk_A @ (k4_xboole_0 @ sk_C @ (k3_xboole_0 @ sk_B @ sk_C)))),
% 0.19/0.49      inference('simplify', [status(thm)], ['17'])).
% 0.19/0.49  thf(commutativity_k3_xboole_0, axiom,
% 0.19/0.49    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.19/0.49  thf('19', plain,
% 0.19/0.49      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.19/0.49      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.19/0.49  thf(t47_xboole_1, axiom,
% 0.19/0.49    (![A:$i,B:$i]:
% 0.19/0.49     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.19/0.49  thf('20', plain,
% 0.19/0.49      (![X10 : $i, X11 : $i]:
% 0.19/0.49         ((k4_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11))
% 0.19/0.49           = (k4_xboole_0 @ X10 @ X11))),
% 0.19/0.49      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.19/0.49  thf('21', plain,
% 0.19/0.49      (![X0 : $i, X1 : $i]:
% 0.19/0.49         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 0.19/0.49           = (k4_xboole_0 @ X0 @ X1))),
% 0.19/0.49      inference('sup+', [status(thm)], ['19', '20'])).
% 0.19/0.49  thf('22', plain, ((r1_tarski @ sk_A @ (k4_xboole_0 @ sk_C @ sk_B))),
% 0.19/0.49      inference('demod', [status(thm)], ['18', '21'])).
% 0.19/0.49  thf('23', plain,
% 0.19/0.49      (![X5 : $i, X7 : $i]:
% 0.19/0.49         (((k4_xboole_0 @ X5 @ X7) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ X7))),
% 0.19/0.49      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.19/0.49  thf('24', plain,
% 0.19/0.49      (((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_C @ sk_B)) = (k1_xboole_0))),
% 0.19/0.49      inference('sup-', [status(thm)], ['22', '23'])).
% 0.19/0.49  thf('25', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         ((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_C @ X0))
% 0.19/0.49           = (k3_xboole_0 @ sk_A @ X0))),
% 0.19/0.49      inference('demod', [status(thm)], ['8', '13'])).
% 0.19/0.49  thf('26', plain,
% 0.19/0.49      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.19/0.49      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.19/0.49  thf('27', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (k1_xboole_0))),
% 0.19/0.49      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.19/0.49  thf('28', plain,
% 0.19/0.49      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.19/0.49      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.19/0.49  thf('29', plain,
% 0.19/0.49      (![X2 : $i, X4 : $i]:
% 0.19/0.49         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 0.19/0.49      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.19/0.49  thf('30', plain,
% 0.19/0.49      (![X0 : $i, X1 : $i]:
% 0.19/0.49         (((k3_xboole_0 @ X1 @ X0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ X1))),
% 0.19/0.49      inference('sup-', [status(thm)], ['28', '29'])).
% 0.19/0.49  thf('31', plain,
% 0.19/0.49      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ sk_A @ sk_B))),
% 0.19/0.49      inference('sup-', [status(thm)], ['27', '30'])).
% 0.19/0.49  thf('32', plain, ((r1_xboole_0 @ sk_A @ sk_B)),
% 0.19/0.49      inference('simplify', [status(thm)], ['31'])).
% 0.19/0.49  thf('33', plain, ($false), inference('demod', [status(thm)], ['0', '32'])).
% 0.19/0.49  
% 0.19/0.49  % SZS output end Refutation
% 0.19/0.49  
% 0.19/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
