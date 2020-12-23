%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.A2cSLWDxW7

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:24 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   52 (  61 expanded)
%              Number of leaves         :   18 (  25 expanded)
%              Depth                    :   11
%              Number of atoms          :  325 ( 410 expanded)
%              Number of equality atoms :   34 (  39 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

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
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('3',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) )
      = ( k4_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('5',plain,
    ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('6',plain,(
    ! [X9: $i] :
      ( ( k4_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('7',plain,
    ( sk_A
    = ( k4_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(t50_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf('8',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k3_xboole_0 @ X17 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X17 @ X18 ) @ ( k3_xboole_0 @ X17 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t50_xboole_1])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('9',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k3_xboole_0 @ X14 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X14 @ X15 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('10',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k3_xboole_0 @ X17 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X17 @ ( k4_xboole_0 @ X18 @ ( k3_xboole_0 @ X17 @ X19 ) ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_C ) )
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['7','10'])).

thf('12',plain,(
    r1_tarski @ sk_A @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('13',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('14',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('15',plain,(
    ! [X6: $i] :
      ( ( k3_xboole_0 @ X6 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('16',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['11','14','15'])).

thf('17',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) )
      = ( k4_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('18',plain,
    ( ( k4_xboole_0 @ sk_B @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X9: $i] :
      ( ( k4_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('20',plain,
    ( sk_B
    = ( k4_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['18','19'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('21',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('22',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X7 @ X8 ) @ X7 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('23',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['21','24'])).

thf('26',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k3_xboole_0 @ X14 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X14 @ X15 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ( ( k3_xboole_0 @ X0 @ X2 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference('sup+',[status(thm)],['20','30'])).

thf('32',plain,(
    $false ),
    inference(demod,[status(thm)],['0','31'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.A2cSLWDxW7
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:28:34 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.22/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.49  % Solved by: fo/fo7.sh
% 0.22/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.49  % done 76 iterations in 0.035s
% 0.22/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.49  % SZS output start Refutation
% 0.22/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.49  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.22/0.49  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.49  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.22/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.49  thf(t77_xboole_1, conjecture,
% 0.22/0.49    (![A:$i,B:$i,C:$i]:
% 0.22/0.49     ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & ( r1_tarski @ A @ C ) & 
% 0.22/0.49          ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) ))).
% 0.22/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.49    (~( ![A:$i,B:$i,C:$i]:
% 0.22/0.49        ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & ( r1_tarski @ A @ C ) & 
% 0.22/0.49             ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) ) )),
% 0.22/0.49    inference('cnf.neg', [status(esa)], [t77_xboole_1])).
% 0.22/0.49  thf('0', plain, (~ (r1_xboole_0 @ sk_A @ sk_B)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('1', plain, ((r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf(d7_xboole_0, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.22/0.49       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.22/0.49  thf('2', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.22/0.49      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.22/0.49  thf('3', plain,
% 0.22/0.49      (((k3_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)) = (k1_xboole_0))),
% 0.22/0.49      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.49  thf(t47_xboole_1, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.22/0.49  thf('4', plain,
% 0.22/0.49      (![X10 : $i, X11 : $i]:
% 0.22/0.49         ((k4_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11))
% 0.22/0.49           = (k4_xboole_0 @ X10 @ X11))),
% 0.22/0.49      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.22/0.49  thf('5', plain,
% 0.22/0.49      (((k4_xboole_0 @ sk_A @ k1_xboole_0)
% 0.22/0.49         = (k4_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)))),
% 0.22/0.49      inference('sup+', [status(thm)], ['3', '4'])).
% 0.22/0.49  thf(t3_boole, axiom,
% 0.22/0.49    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.22/0.49  thf('6', plain, (![X9 : $i]: ((k4_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 0.22/0.49      inference('cnf', [status(esa)], [t3_boole])).
% 0.22/0.49  thf('7', plain,
% 0.22/0.49      (((sk_A) = (k4_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)))),
% 0.22/0.49      inference('demod', [status(thm)], ['5', '6'])).
% 0.22/0.49  thf(t50_xboole_1, axiom,
% 0.22/0.49    (![A:$i,B:$i,C:$i]:
% 0.22/0.49     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.22/0.49       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 0.22/0.49  thf('8', plain,
% 0.22/0.49      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.22/0.49         ((k3_xboole_0 @ X17 @ (k4_xboole_0 @ X18 @ X19))
% 0.22/0.49           = (k4_xboole_0 @ (k3_xboole_0 @ X17 @ X18) @ 
% 0.22/0.49              (k3_xboole_0 @ X17 @ X19)))),
% 0.22/0.49      inference('cnf', [status(esa)], [t50_xboole_1])).
% 0.22/0.49  thf(t49_xboole_1, axiom,
% 0.22/0.49    (![A:$i,B:$i,C:$i]:
% 0.22/0.49     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.22/0.49       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 0.22/0.49  thf('9', plain,
% 0.22/0.49      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.22/0.49         ((k3_xboole_0 @ X14 @ (k4_xboole_0 @ X15 @ X16))
% 0.22/0.49           = (k4_xboole_0 @ (k3_xboole_0 @ X14 @ X15) @ X16))),
% 0.22/0.49      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.22/0.49  thf('10', plain,
% 0.22/0.49      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.22/0.49         ((k3_xboole_0 @ X17 @ (k4_xboole_0 @ X18 @ X19))
% 0.22/0.49           = (k3_xboole_0 @ X17 @ 
% 0.22/0.49              (k4_xboole_0 @ X18 @ (k3_xboole_0 @ X17 @ X19))))),
% 0.22/0.49      inference('demod', [status(thm)], ['8', '9'])).
% 0.22/0.49  thf('11', plain,
% 0.22/0.49      (((k3_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_C))
% 0.22/0.49         = (k3_xboole_0 @ sk_B @ sk_A))),
% 0.22/0.49      inference('sup+', [status(thm)], ['7', '10'])).
% 0.22/0.49  thf('12', plain, ((r1_tarski @ sk_A @ sk_C)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf(l32_xboole_1, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.22/0.49  thf('13', plain,
% 0.22/0.49      (![X3 : $i, X5 : $i]:
% 0.22/0.49         (((k4_xboole_0 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 0.22/0.49      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.22/0.49  thf('14', plain, (((k4_xboole_0 @ sk_A @ sk_C) = (k1_xboole_0))),
% 0.22/0.49      inference('sup-', [status(thm)], ['12', '13'])).
% 0.22/0.49  thf(t2_boole, axiom,
% 0.22/0.49    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.22/0.49  thf('15', plain,
% 0.22/0.49      (![X6 : $i]: ((k3_xboole_0 @ X6 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.49      inference('cnf', [status(esa)], [t2_boole])).
% 0.22/0.49  thf('16', plain, (((k1_xboole_0) = (k3_xboole_0 @ sk_B @ sk_A))),
% 0.22/0.49      inference('demod', [status(thm)], ['11', '14', '15'])).
% 0.22/0.49  thf('17', plain,
% 0.22/0.49      (![X10 : $i, X11 : $i]:
% 0.22/0.49         ((k4_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11))
% 0.22/0.49           = (k4_xboole_0 @ X10 @ X11))),
% 0.22/0.49      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.22/0.49  thf('18', plain,
% 0.22/0.49      (((k4_xboole_0 @ sk_B @ k1_xboole_0) = (k4_xboole_0 @ sk_B @ sk_A))),
% 0.22/0.49      inference('sup+', [status(thm)], ['16', '17'])).
% 0.22/0.49  thf('19', plain, (![X9 : $i]: ((k4_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 0.22/0.49      inference('cnf', [status(esa)], [t3_boole])).
% 0.22/0.49  thf('20', plain, (((sk_B) = (k4_xboole_0 @ sk_B @ sk_A))),
% 0.22/0.49      inference('demod', [status(thm)], ['18', '19'])).
% 0.22/0.49  thf(t48_xboole_1, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.22/0.49  thf('21', plain,
% 0.22/0.49      (![X12 : $i, X13 : $i]:
% 0.22/0.49         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X12 @ X13))
% 0.22/0.49           = (k3_xboole_0 @ X12 @ X13))),
% 0.22/0.49      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.22/0.49  thf(t36_xboole_1, axiom,
% 0.22/0.49    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.22/0.49  thf('22', plain,
% 0.22/0.49      (![X7 : $i, X8 : $i]: (r1_tarski @ (k4_xboole_0 @ X7 @ X8) @ X7)),
% 0.22/0.49      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.22/0.49  thf('23', plain,
% 0.22/0.49      (![X3 : $i, X5 : $i]:
% 0.22/0.49         (((k4_xboole_0 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 0.22/0.49      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.22/0.49  thf('24', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 0.22/0.49      inference('sup-', [status(thm)], ['22', '23'])).
% 0.22/0.49  thf('25', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1) = (k1_xboole_0))),
% 0.22/0.49      inference('sup+', [status(thm)], ['21', '24'])).
% 0.22/0.49  thf('26', plain,
% 0.22/0.49      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.22/0.49         ((k3_xboole_0 @ X14 @ (k4_xboole_0 @ X15 @ X16))
% 0.22/0.49           = (k4_xboole_0 @ (k3_xboole_0 @ X14 @ X15) @ X16))),
% 0.22/0.49      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.22/0.49  thf('27', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1)) = (k1_xboole_0))),
% 0.22/0.49      inference('demod', [status(thm)], ['25', '26'])).
% 0.22/0.49  thf('28', plain,
% 0.22/0.49      (![X0 : $i, X2 : $i]:
% 0.22/0.49         ((r1_xboole_0 @ X0 @ X2) | ((k3_xboole_0 @ X0 @ X2) != (k1_xboole_0)))),
% 0.22/0.49      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.22/0.49  thf('29', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         (((k1_xboole_0) != (k1_xboole_0))
% 0.22/0.49          | (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['27', '28'])).
% 0.22/0.49  thf('30', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 0.22/0.49      inference('simplify', [status(thm)], ['29'])).
% 0.22/0.49  thf('31', plain, ((r1_xboole_0 @ sk_A @ sk_B)),
% 0.22/0.49      inference('sup+', [status(thm)], ['20', '30'])).
% 0.22/0.49  thf('32', plain, ($false), inference('demod', [status(thm)], ['0', '31'])).
% 0.22/0.49  
% 0.22/0.49  % SZS output end Refutation
% 0.22/0.49  
% 0.22/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
