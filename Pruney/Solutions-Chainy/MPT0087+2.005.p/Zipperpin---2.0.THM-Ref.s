%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.CLiOwMw2gt

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:32 EST 2020

% Result     : Theorem 0.24s
% Output     : Refutation 0.24s
% Verified   : 
% Statistics : Number of formulae       :   54 (  80 expanded)
%              Number of leaves         :   15 (  32 expanded)
%              Depth                    :    9
%              Number of atoms          :  320 ( 488 expanded)
%              Number of equality atoms :   34 (  53 expanded)
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

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

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

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) )
      = ( k4_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('5',plain,
    ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('6',plain,(
    ! [X7: $i] :
      ( ( k4_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('7',plain,
    ( sk_A
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(t52_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf('8',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X14 @ X15 ) @ ( k3_xboole_0 @ X14 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) )
      = ( k2_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('10',plain,(
    ! [X17: $i,X18: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X17 @ X18 ) @ X18 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_A @ X0 ) ) @ ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X7: $i] :
      ( ( k4_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('13',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X14 @ X15 ) @ ( k3_xboole_0 @ X14 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ k1_xboole_0 @ X1 ) )
      = ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X7: $i] :
      ( ( k4_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('16',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X7: $i] :
      ( ( k4_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('19',plain,(
    ! [X17: $i,X18: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X17 @ X18 ) @ X18 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['17','22'])).

thf('24',plain,(
    ! [X17: $i,X18: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X17 @ X18 ) @ X18 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('25',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) )
      = ( k4_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ k1_xboole_0 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X7: $i] :
      ( ( k4_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['23','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['17','22'])).

thf('33',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X7: $i] :
      ( ( k4_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['14','33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['11','35'])).

thf('37',plain,(
    $false ),
    inference(demod,[status(thm)],['0','36'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.CLiOwMw2gt
% 0.15/0.37  % Computer   : n013.cluster.edu
% 0.15/0.37  % Model      : x86_64 x86_64
% 0.15/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.37  % Memory     : 8042.1875MB
% 0.15/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.37  % CPULimit   : 60
% 0.15/0.37  % DateTime   : Tue Dec  1 19:27:40 EST 2020
% 0.15/0.37  % CPUTime    : 
% 0.15/0.37  % Running portfolio for 600 s
% 0.15/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.37  % Number of cores: 8
% 0.15/0.38  % Python version: Python 3.6.8
% 0.15/0.38  % Running in FO mode
% 0.24/0.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.24/0.54  % Solved by: fo/fo7.sh
% 0.24/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.24/0.54  % done 107 iterations in 0.051s
% 0.24/0.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.24/0.54  % SZS output start Refutation
% 0.24/0.54  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.24/0.54  thf(sk_C_type, type, sk_C: $i).
% 0.24/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.24/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.24/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.24/0.54  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.24/0.54  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.24/0.54  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.24/0.54  thf(t80_xboole_1, conjecture,
% 0.24/0.54    (![A:$i,B:$i,C:$i]:
% 0.24/0.54     ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) ))).
% 0.24/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.24/0.54    (~( ![A:$i,B:$i,C:$i]:
% 0.24/0.54        ( ( r1_xboole_0 @ A @ B ) =>
% 0.24/0.54          ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) ) )),
% 0.24/0.54    inference('cnf.neg', [status(esa)], [t80_xboole_1])).
% 0.24/0.54  thf('0', plain, (~ (r1_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))),
% 0.24/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.54  thf('1', plain, ((r1_xboole_0 @ sk_A @ sk_B)),
% 0.24/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.54  thf(d7_xboole_0, axiom,
% 0.24/0.54    (![A:$i,B:$i]:
% 0.24/0.54     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.24/0.54       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.24/0.54  thf('2', plain,
% 0.24/0.54      (![X2 : $i, X3 : $i]:
% 0.24/0.54         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.24/0.54      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.24/0.54  thf('3', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.24/0.54      inference('sup-', [status(thm)], ['1', '2'])).
% 0.24/0.54  thf(t47_xboole_1, axiom,
% 0.24/0.54    (![A:$i,B:$i]:
% 0.24/0.54     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.24/0.54  thf('4', plain,
% 0.24/0.54      (![X8 : $i, X9 : $i]:
% 0.24/0.54         ((k4_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9))
% 0.24/0.54           = (k4_xboole_0 @ X8 @ X9))),
% 0.24/0.54      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.24/0.54  thf('5', plain,
% 0.24/0.54      (((k4_xboole_0 @ sk_A @ k1_xboole_0) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.24/0.54      inference('sup+', [status(thm)], ['3', '4'])).
% 0.24/0.54  thf(t3_boole, axiom,
% 0.24/0.54    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.24/0.54  thf('6', plain, (![X7 : $i]: ((k4_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 0.24/0.54      inference('cnf', [status(esa)], [t3_boole])).
% 0.24/0.54  thf('7', plain, (((sk_A) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.24/0.54      inference('demod', [status(thm)], ['5', '6'])).
% 0.24/0.54  thf(t52_xboole_1, axiom,
% 0.24/0.54    (![A:$i,B:$i,C:$i]:
% 0.24/0.54     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.24/0.54       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 0.24/0.54  thf('8', plain,
% 0.24/0.54      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.24/0.54         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X15 @ X16))
% 0.24/0.54           = (k2_xboole_0 @ (k4_xboole_0 @ X14 @ X15) @ 
% 0.24/0.54              (k3_xboole_0 @ X14 @ X16)))),
% 0.24/0.54      inference('cnf', [status(esa)], [t52_xboole_1])).
% 0.24/0.54  thf('9', plain,
% 0.24/0.54      (![X0 : $i]:
% 0.24/0.54         ((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ X0))
% 0.24/0.54           = (k2_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_A @ X0)))),
% 0.24/0.54      inference('sup+', [status(thm)], ['7', '8'])).
% 0.24/0.54  thf(t79_xboole_1, axiom,
% 0.24/0.54    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.24/0.54  thf('10', plain,
% 0.24/0.54      (![X17 : $i, X18 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X17 @ X18) @ X18)),
% 0.24/0.54      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.24/0.54  thf('11', plain,
% 0.24/0.54      (![X0 : $i]:
% 0.24/0.54         (r1_xboole_0 @ (k2_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_A @ X0)) @ 
% 0.24/0.54          (k4_xboole_0 @ sk_B @ X0))),
% 0.24/0.54      inference('sup+', [status(thm)], ['9', '10'])).
% 0.24/0.54  thf('12', plain, (![X7 : $i]: ((k4_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 0.24/0.54      inference('cnf', [status(esa)], [t3_boole])).
% 0.24/0.54  thf('13', plain,
% 0.24/0.54      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.24/0.54         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X15 @ X16))
% 0.24/0.54           = (k2_xboole_0 @ (k4_xboole_0 @ X14 @ X15) @ 
% 0.24/0.54              (k3_xboole_0 @ X14 @ X16)))),
% 0.24/0.54      inference('cnf', [status(esa)], [t52_xboole_1])).
% 0.24/0.54  thf('14', plain,
% 0.24/0.54      (![X0 : $i, X1 : $i]:
% 0.24/0.54         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ k1_xboole_0 @ X1))
% 0.24/0.54           = (k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.24/0.54      inference('sup+', [status(thm)], ['12', '13'])).
% 0.24/0.54  thf('15', plain, (![X7 : $i]: ((k4_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 0.24/0.54      inference('cnf', [status(esa)], [t3_boole])).
% 0.24/0.54  thf(t48_xboole_1, axiom,
% 0.24/0.54    (![A:$i,B:$i]:
% 0.24/0.54     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.24/0.54  thf('16', plain,
% 0.24/0.54      (![X10 : $i, X11 : $i]:
% 0.24/0.54         ((k4_xboole_0 @ X10 @ (k4_xboole_0 @ X10 @ X11))
% 0.24/0.54           = (k3_xboole_0 @ X10 @ X11))),
% 0.24/0.54      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.24/0.54  thf('17', plain,
% 0.24/0.54      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.24/0.54      inference('sup+', [status(thm)], ['15', '16'])).
% 0.24/0.54  thf('18', plain, (![X7 : $i]: ((k4_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 0.24/0.54      inference('cnf', [status(esa)], [t3_boole])).
% 0.24/0.54  thf('19', plain,
% 0.24/0.54      (![X17 : $i, X18 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X17 @ X18) @ X18)),
% 0.24/0.54      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.24/0.54  thf('20', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.24/0.54      inference('sup+', [status(thm)], ['18', '19'])).
% 0.24/0.54  thf('21', plain,
% 0.24/0.54      (![X2 : $i, X3 : $i]:
% 0.24/0.54         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.24/0.54      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.24/0.54  thf('22', plain,
% 0.24/0.54      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.24/0.54      inference('sup-', [status(thm)], ['20', '21'])).
% 0.24/0.54  thf('23', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.24/0.54      inference('demod', [status(thm)], ['17', '22'])).
% 0.24/0.54  thf('24', plain,
% 0.24/0.54      (![X17 : $i, X18 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X17 @ X18) @ X18)),
% 0.24/0.54      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.24/0.54  thf('25', plain,
% 0.24/0.54      (![X2 : $i, X3 : $i]:
% 0.24/0.54         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.24/0.54      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.24/0.54  thf('26', plain,
% 0.24/0.54      (![X0 : $i, X1 : $i]:
% 0.24/0.54         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0) = (k1_xboole_0))),
% 0.24/0.54      inference('sup-', [status(thm)], ['24', '25'])).
% 0.24/0.54  thf('27', plain,
% 0.24/0.54      (![X8 : $i, X9 : $i]:
% 0.24/0.54         ((k4_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9))
% 0.24/0.54           = (k4_xboole_0 @ X8 @ X9))),
% 0.24/0.54      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.24/0.54  thf('28', plain,
% 0.24/0.54      (![X0 : $i, X1 : $i]:
% 0.24/0.54         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ k1_xboole_0)
% 0.24/0.54           = (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 0.24/0.54      inference('sup+', [status(thm)], ['26', '27'])).
% 0.24/0.54  thf('29', plain, (![X7 : $i]: ((k4_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 0.24/0.54      inference('cnf', [status(esa)], [t3_boole])).
% 0.24/0.54  thf('30', plain,
% 0.24/0.54      (![X0 : $i, X1 : $i]:
% 0.24/0.54         ((k4_xboole_0 @ X1 @ X0)
% 0.24/0.54           = (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 0.24/0.54      inference('demod', [status(thm)], ['28', '29'])).
% 0.24/0.54  thf('31', plain,
% 0.24/0.54      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.24/0.54      inference('sup+', [status(thm)], ['23', '30'])).
% 0.24/0.54  thf('32', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.24/0.54      inference('demod', [status(thm)], ['17', '22'])).
% 0.24/0.54  thf('33', plain,
% 0.24/0.54      (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.24/0.54      inference('demod', [status(thm)], ['31', '32'])).
% 0.24/0.54  thf('34', plain, (![X7 : $i]: ((k4_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 0.24/0.54      inference('cnf', [status(esa)], [t3_boole])).
% 0.24/0.54  thf('35', plain,
% 0.24/0.54      (![X0 : $i, X1 : $i]:
% 0.24/0.54         ((X0) = (k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.24/0.54      inference('demod', [status(thm)], ['14', '33', '34'])).
% 0.24/0.54  thf('36', plain,
% 0.24/0.54      (![X0 : $i]: (r1_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ X0))),
% 0.24/0.54      inference('demod', [status(thm)], ['11', '35'])).
% 0.24/0.54  thf('37', plain, ($false), inference('demod', [status(thm)], ['0', '36'])).
% 0.24/0.54  
% 0.24/0.54  % SZS output end Refutation
% 0.24/0.54  
% 0.24/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
