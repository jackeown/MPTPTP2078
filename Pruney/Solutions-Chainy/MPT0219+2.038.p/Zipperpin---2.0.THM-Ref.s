%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.KqNujabmn0

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:08 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   56 (  87 expanded)
%              Number of leaves         :   19 (  35 expanded)
%              Depth                    :   15
%              Number of atoms          :  355 ( 578 expanded)
%              Number of equality atoms :   45 (  78 expanded)
%              Maximal formula depth    :    9 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t13_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
     => ( A = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
          = ( k1_tarski @ A ) )
       => ( A = B ) ) ),
    inference('cnf.neg',[status(esa)],[t13_zfmisc_1])).

thf('0',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('2',plain,(
    ! [X12: $i] :
      ( ( k5_xboole_0 @ X12 @ X12 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('3',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k5_xboole_0 @ X9 @ ( k5_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('5',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('6',plain,(
    ! [X6: $i] :
      ( ( k5_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['4','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','8'])).

thf('10',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['0','9'])).

thf('11',plain,(
    ! [X12: $i] :
      ( ( k5_xboole_0 @ X12 @ X12 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('12',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['10','11'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('13',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['4','7'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('19',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_B ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('21',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) ),
    inference('sup+',[status(thm)],['19','22'])).

thf('24',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('25',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['4','7'])).

thf('27',plain,
    ( ( k1_tarski @ sk_A )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('29',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('30',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ X7 @ ( k2_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('31',plain,(
    r1_tarski @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf(t6_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
     => ( A = B ) ) )).

thf('32',plain,(
    ! [X43: $i,X44: $i] :
      ( ( X44 = X43 )
      | ~ ( r1_tarski @ ( k1_tarski @ X44 ) @ ( k1_tarski @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[t6_zfmisc_1])).

thf('33',plain,(
    sk_B = sk_A ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['33','34'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.KqNujabmn0
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:01:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.22/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.52  % Solved by: fo/fo7.sh
% 0.22/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.52  % done 97 iterations in 0.062s
% 0.22/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.52  % SZS output start Refutation
% 0.22/0.52  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.22/0.52  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.52  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.52  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.22/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.52  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.22/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.52  thf(t13_zfmisc_1, conjecture,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.22/0.52         ( k1_tarski @ A ) ) =>
% 0.22/0.52       ( ( A ) = ( B ) ) ))).
% 0.22/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.52    (~( ![A:$i,B:$i]:
% 0.22/0.52        ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.22/0.52            ( k1_tarski @ A ) ) =>
% 0.22/0.52          ( ( A ) = ( B ) ) ) )),
% 0.22/0.52    inference('cnf.neg', [status(esa)], [t13_zfmisc_1])).
% 0.22/0.52  thf('0', plain,
% 0.22/0.52      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.22/0.52         = (k1_tarski @ sk_A))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf(t98_xboole_1, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.22/0.52  thf('1', plain,
% 0.22/0.52      (![X13 : $i, X14 : $i]:
% 0.22/0.52         ((k2_xboole_0 @ X13 @ X14)
% 0.22/0.52           = (k5_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X13)))),
% 0.22/0.52      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.22/0.52  thf(t92_xboole_1, axiom,
% 0.22/0.52    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.22/0.52  thf('2', plain, (![X12 : $i]: ((k5_xboole_0 @ X12 @ X12) = (k1_xboole_0))),
% 0.22/0.52      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.22/0.52  thf(t91_xboole_1, axiom,
% 0.22/0.52    (![A:$i,B:$i,C:$i]:
% 0.22/0.52     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.22/0.52       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.22/0.52  thf('3', plain,
% 0.22/0.52      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.22/0.52         ((k5_xboole_0 @ (k5_xboole_0 @ X9 @ X10) @ X11)
% 0.22/0.52           = (k5_xboole_0 @ X9 @ (k5_xboole_0 @ X10 @ X11)))),
% 0.22/0.52      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.22/0.52  thf('4', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.22/0.52           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.22/0.52      inference('sup+', [status(thm)], ['2', '3'])).
% 0.22/0.52  thf(commutativity_k5_xboole_0, axiom,
% 0.22/0.52    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.22/0.52  thf('5', plain,
% 0.22/0.52      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.22/0.52      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.22/0.52  thf(t5_boole, axiom,
% 0.22/0.52    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.22/0.52  thf('6', plain, (![X6 : $i]: ((k5_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 0.22/0.52      inference('cnf', [status(esa)], [t5_boole])).
% 0.22/0.52  thf('7', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.22/0.52      inference('sup+', [status(thm)], ['5', '6'])).
% 0.22/0.52  thf('8', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.22/0.52      inference('demod', [status(thm)], ['4', '7'])).
% 0.22/0.52  thf('9', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         ((k4_xboole_0 @ X0 @ X1)
% 0.22/0.52           = (k5_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.22/0.52      inference('sup+', [status(thm)], ['1', '8'])).
% 0.22/0.52  thf('10', plain,
% 0.22/0.52      (((k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 0.22/0.52         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))),
% 0.22/0.52      inference('sup+', [status(thm)], ['0', '9'])).
% 0.22/0.52  thf('11', plain, (![X12 : $i]: ((k5_xboole_0 @ X12 @ X12) = (k1_xboole_0))),
% 0.22/0.52      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.22/0.52  thf('12', plain,
% 0.22/0.52      (((k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)) = (k1_xboole_0))),
% 0.22/0.52      inference('demod', [status(thm)], ['10', '11'])).
% 0.22/0.52  thf(t100_xboole_1, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.22/0.52  thf('13', plain,
% 0.22/0.52      (![X4 : $i, X5 : $i]:
% 0.22/0.52         ((k4_xboole_0 @ X4 @ X5)
% 0.22/0.52           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 0.22/0.52      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.22/0.52  thf('14', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.22/0.52      inference('demod', [status(thm)], ['4', '7'])).
% 0.22/0.52  thf('15', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         ((k3_xboole_0 @ X1 @ X0)
% 0.22/0.52           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.22/0.52      inference('sup+', [status(thm)], ['13', '14'])).
% 0.22/0.52  thf('16', plain,
% 0.22/0.52      (((k3_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 0.22/0.52         = (k5_xboole_0 @ (k1_tarski @ sk_B) @ k1_xboole_0))),
% 0.22/0.52      inference('sup+', [status(thm)], ['12', '15'])).
% 0.22/0.52  thf('17', plain,
% 0.22/0.52      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.22/0.52      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.22/0.52  thf('18', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.22/0.52      inference('sup+', [status(thm)], ['5', '6'])).
% 0.22/0.52  thf('19', plain,
% 0.22/0.52      (((k3_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 0.22/0.52         = (k1_tarski @ sk_B))),
% 0.22/0.52      inference('demod', [status(thm)], ['16', '17', '18'])).
% 0.22/0.52  thf(commutativity_k3_xboole_0, axiom,
% 0.22/0.52    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.22/0.52  thf('20', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.22/0.52      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.22/0.52  thf('21', plain,
% 0.22/0.52      (![X4 : $i, X5 : $i]:
% 0.22/0.52         ((k4_xboole_0 @ X4 @ X5)
% 0.22/0.52           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 0.22/0.52      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.22/0.52  thf('22', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         ((k4_xboole_0 @ X0 @ X1)
% 0.22/0.52           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.22/0.52      inference('sup+', [status(thm)], ['20', '21'])).
% 0.22/0.52  thf('23', plain,
% 0.22/0.52      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.22/0.52         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)))),
% 0.22/0.52      inference('sup+', [status(thm)], ['19', '22'])).
% 0.22/0.52  thf('24', plain,
% 0.22/0.52      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.22/0.52      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.22/0.52  thf('25', plain,
% 0.22/0.52      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.22/0.52         = (k5_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)))),
% 0.22/0.52      inference('demod', [status(thm)], ['23', '24'])).
% 0.22/0.52  thf('26', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.22/0.52      inference('demod', [status(thm)], ['4', '7'])).
% 0.22/0.52  thf('27', plain,
% 0.22/0.52      (((k1_tarski @ sk_A)
% 0.22/0.52         = (k5_xboole_0 @ (k1_tarski @ sk_B) @ 
% 0.22/0.52            (k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))))),
% 0.22/0.52      inference('sup+', [status(thm)], ['25', '26'])).
% 0.22/0.52  thf('28', plain,
% 0.22/0.52      (![X13 : $i, X14 : $i]:
% 0.22/0.52         ((k2_xboole_0 @ X13 @ X14)
% 0.22/0.52           = (k5_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X13)))),
% 0.22/0.52      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.22/0.52  thf('29', plain,
% 0.22/0.52      (((k1_tarski @ sk_A)
% 0.22/0.52         = (k2_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)))),
% 0.22/0.52      inference('demod', [status(thm)], ['27', '28'])).
% 0.22/0.52  thf(t7_xboole_1, axiom,
% 0.22/0.52    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.22/0.52  thf('30', plain,
% 0.22/0.52      (![X7 : $i, X8 : $i]: (r1_tarski @ X7 @ (k2_xboole_0 @ X7 @ X8))),
% 0.22/0.52      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.22/0.52  thf('31', plain, ((r1_tarski @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))),
% 0.22/0.52      inference('sup+', [status(thm)], ['29', '30'])).
% 0.22/0.52  thf(t6_zfmisc_1, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =>
% 0.22/0.52       ( ( A ) = ( B ) ) ))).
% 0.22/0.52  thf('32', plain,
% 0.22/0.52      (![X43 : $i, X44 : $i]:
% 0.22/0.52         (((X44) = (X43))
% 0.22/0.52          | ~ (r1_tarski @ (k1_tarski @ X44) @ (k1_tarski @ X43)))),
% 0.22/0.52      inference('cnf', [status(esa)], [t6_zfmisc_1])).
% 0.22/0.52  thf('33', plain, (((sk_B) = (sk_A))),
% 0.22/0.52      inference('sup-', [status(thm)], ['31', '32'])).
% 0.22/0.52  thf('34', plain, (((sk_A) != (sk_B))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('35', plain, ($false),
% 0.22/0.52      inference('simplify_reflect-', [status(thm)], ['33', '34'])).
% 0.22/0.52  
% 0.22/0.52  % SZS output end Refutation
% 0.22/0.52  
% 0.22/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
