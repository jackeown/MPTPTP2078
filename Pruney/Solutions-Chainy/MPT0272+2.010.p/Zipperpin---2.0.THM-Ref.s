%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.zUoIOasIHS

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:27 EST 2020

% Result     : Theorem 0.86s
% Output     : Refutation 0.86s
% Verified   : 
% Statistics : Number of formulae       :   55 (  73 expanded)
%              Number of leaves         :   20 (  30 expanded)
%              Depth                    :   13
%              Number of atoms          :  380 ( 528 expanded)
%              Number of equality atoms :   36 (  52 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('0',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ( X6 != X7 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('1',plain,(
    ! [X7: $i] :
      ( r1_tarski @ X7 @ X7 ) ),
    inference(simplify,[status(thm)],['0'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('2',plain,(
    ! [X15: $i] :
      ( ( k2_tarski @ X15 @ X15 )
      = ( k1_tarski @ X15 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('3',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ( r2_hidden @ X45 @ X46 )
      | ~ ( r1_tarski @ ( k2_tarski @ X45 @ X47 ) @ X46 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf(t1_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) )
    <=> ~ ( ( r2_hidden @ A @ B )
        <=> ( r2_hidden @ A @ C ) ) ) )).

thf('6',plain,(
    ! [X2: $i,X3: $i,X5: $i] :
      ( ( r2_hidden @ X2 @ ( k5_xboole_0 @ X3 @ X5 ) )
      | ( r2_hidden @ X2 @ X5 )
      | ~ ( r2_hidden @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ ( k5_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(l31_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k3_xboole_0 @ B @ ( k1_tarski @ A ) )
        = ( k1_tarski @ A ) ) ) )).

thf('8',plain,(
    ! [X43: $i,X44: $i] :
      ( ( ( k3_xboole_0 @ X44 @ ( k1_tarski @ X43 ) )
        = ( k1_tarski @ X43 ) )
      | ~ ( r2_hidden @ X43 @ X44 ) ) ),
    inference(cnf,[status(esa)],[l31_zfmisc_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( ( k3_xboole_0 @ ( k5_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) @ ( k1_tarski @ X1 ) )
        = ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ ( k5_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) )
        = ( k1_tarski @ X1 ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('13',plain,(
    ! [X43: $i,X44: $i] :
      ( ( ( k3_xboole_0 @ X44 @ ( k1_tarski @ X43 ) )
        = ( k1_tarski @ X43 ) )
      | ~ ( r2_hidden @ X43 @ X44 ) ) ),
    inference(cnf,[status(esa)],[l31_zfmisc_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t112_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ B ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ A @ C ) @ B ) ) )).

thf('15',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X11 @ X13 ) @ ( k3_xboole_0 @ X12 @ X13 ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X11 @ X12 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[t112_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k1_tarski @ X0 ) @ ( k3_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('18',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ X10 )
      = ( k5_xboole_0 @ X9 @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      = ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ ( k5_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ) ),
    inference(demod,[status(thm)],['16','19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['11','21'])).

thf(t69_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = ( k1_tarski @ A ) )
      | ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = k1_xboole_0 ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
          = ( k1_tarski @ A ) )
        | ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
          = k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t69_zfmisc_1])).

thf('23',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
 != ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( ( k1_tarski @ sk_A )
     != ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X43: $i,X44: $i] :
      ( ( ( k3_xboole_0 @ X44 @ ( k1_tarski @ X43 ) )
        = ( k1_tarski @ X43 ) )
      | ~ ( r2_hidden @ X43 @ X44 ) ) ),
    inference(cnf,[status(esa)],[l31_zfmisc_1])).

thf('27',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('29',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('30',plain,(
    ! [X14: $i] :
      ( ( k5_xboole_0 @ X14 @ X14 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('31',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['31','32'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.zUoIOasIHS
% 0.14/0.35  % Computer   : n014.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:11:38 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.86/1.05  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.86/1.05  % Solved by: fo/fo7.sh
% 0.86/1.05  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.86/1.05  % done 1541 iterations in 0.586s
% 0.86/1.05  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.86/1.05  % SZS output start Refutation
% 0.86/1.05  thf(sk_B_type, type, sk_B: $i).
% 0.86/1.05  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.86/1.05  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.86/1.05  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.86/1.05  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.86/1.05  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.86/1.05  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.86/1.05  thf(sk_A_type, type, sk_A: $i).
% 0.86/1.05  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.86/1.05  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.86/1.05  thf(d10_xboole_0, axiom,
% 0.86/1.05    (![A:$i,B:$i]:
% 0.86/1.05     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.86/1.05  thf('0', plain,
% 0.86/1.05      (![X6 : $i, X7 : $i]: ((r1_tarski @ X6 @ X7) | ((X6) != (X7)))),
% 0.86/1.05      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.86/1.05  thf('1', plain, (![X7 : $i]: (r1_tarski @ X7 @ X7)),
% 0.86/1.05      inference('simplify', [status(thm)], ['0'])).
% 0.86/1.05  thf(t69_enumset1, axiom,
% 0.86/1.05    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.86/1.05  thf('2', plain, (![X15 : $i]: ((k2_tarski @ X15 @ X15) = (k1_tarski @ X15))),
% 0.86/1.05      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.86/1.05  thf(t38_zfmisc_1, axiom,
% 0.86/1.05    (![A:$i,B:$i,C:$i]:
% 0.86/1.05     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.86/1.05       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.86/1.05  thf('3', plain,
% 0.86/1.05      (![X45 : $i, X46 : $i, X47 : $i]:
% 0.86/1.05         ((r2_hidden @ X45 @ X46)
% 0.86/1.05          | ~ (r1_tarski @ (k2_tarski @ X45 @ X47) @ X46))),
% 0.86/1.05      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.86/1.05  thf('4', plain,
% 0.86/1.05      (![X0 : $i, X1 : $i]:
% 0.86/1.05         (~ (r1_tarski @ (k1_tarski @ X0) @ X1) | (r2_hidden @ X0 @ X1))),
% 0.86/1.05      inference('sup-', [status(thm)], ['2', '3'])).
% 0.86/1.05  thf('5', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.86/1.05      inference('sup-', [status(thm)], ['1', '4'])).
% 0.86/1.05  thf(t1_xboole_0, axiom,
% 0.86/1.05    (![A:$i,B:$i,C:$i]:
% 0.86/1.05     ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 0.86/1.05       ( ~( ( r2_hidden @ A @ B ) <=> ( r2_hidden @ A @ C ) ) ) ))).
% 0.86/1.05  thf('6', plain,
% 0.86/1.05      (![X2 : $i, X3 : $i, X5 : $i]:
% 0.86/1.05         ((r2_hidden @ X2 @ (k5_xboole_0 @ X3 @ X5))
% 0.86/1.05          | (r2_hidden @ X2 @ X5)
% 0.86/1.05          | ~ (r2_hidden @ X2 @ X3))),
% 0.86/1.05      inference('cnf', [status(esa)], [t1_xboole_0])).
% 0.86/1.05  thf('7', plain,
% 0.86/1.05      (![X0 : $i, X1 : $i]:
% 0.86/1.05         ((r2_hidden @ X0 @ X1)
% 0.86/1.05          | (r2_hidden @ X0 @ (k5_xboole_0 @ (k1_tarski @ X0) @ X1)))),
% 0.86/1.05      inference('sup-', [status(thm)], ['5', '6'])).
% 0.86/1.05  thf(l31_zfmisc_1, axiom,
% 0.86/1.05    (![A:$i,B:$i]:
% 0.86/1.05     ( ( r2_hidden @ A @ B ) =>
% 0.86/1.05       ( ( k3_xboole_0 @ B @ ( k1_tarski @ A ) ) = ( k1_tarski @ A ) ) ))).
% 0.86/1.05  thf('8', plain,
% 0.86/1.05      (![X43 : $i, X44 : $i]:
% 0.86/1.05         (((k3_xboole_0 @ X44 @ (k1_tarski @ X43)) = (k1_tarski @ X43))
% 0.86/1.05          | ~ (r2_hidden @ X43 @ X44))),
% 0.86/1.05      inference('cnf', [status(esa)], [l31_zfmisc_1])).
% 0.86/1.05  thf('9', plain,
% 0.86/1.05      (![X0 : $i, X1 : $i]:
% 0.86/1.05         ((r2_hidden @ X1 @ X0)
% 0.86/1.05          | ((k3_xboole_0 @ (k5_xboole_0 @ (k1_tarski @ X1) @ X0) @ 
% 0.86/1.05              (k1_tarski @ X1)) = (k1_tarski @ X1)))),
% 0.86/1.05      inference('sup-', [status(thm)], ['7', '8'])).
% 0.86/1.05  thf(commutativity_k3_xboole_0, axiom,
% 0.86/1.05    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.86/1.05  thf('10', plain,
% 0.86/1.05      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.86/1.05      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.86/1.05  thf('11', plain,
% 0.86/1.05      (![X0 : $i, X1 : $i]:
% 0.86/1.05         ((r2_hidden @ X1 @ X0)
% 0.86/1.05          | ((k3_xboole_0 @ (k1_tarski @ X1) @ 
% 0.86/1.05              (k5_xboole_0 @ (k1_tarski @ X1) @ X0)) = (k1_tarski @ X1)))),
% 0.86/1.05      inference('demod', [status(thm)], ['9', '10'])).
% 0.86/1.05  thf('12', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.86/1.05      inference('sup-', [status(thm)], ['1', '4'])).
% 0.86/1.05  thf('13', plain,
% 0.86/1.05      (![X43 : $i, X44 : $i]:
% 0.86/1.05         (((k3_xboole_0 @ X44 @ (k1_tarski @ X43)) = (k1_tarski @ X43))
% 0.86/1.05          | ~ (r2_hidden @ X43 @ X44))),
% 0.86/1.05      inference('cnf', [status(esa)], [l31_zfmisc_1])).
% 0.86/1.05  thf('14', plain,
% 0.86/1.05      (![X0 : $i]:
% 0.86/1.05         ((k3_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0))
% 0.86/1.05           = (k1_tarski @ X0))),
% 0.86/1.05      inference('sup-', [status(thm)], ['12', '13'])).
% 0.86/1.05  thf(t112_xboole_1, axiom,
% 0.86/1.05    (![A:$i,B:$i,C:$i]:
% 0.86/1.05     ( ( k5_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ B ) ) =
% 0.86/1.05       ( k3_xboole_0 @ ( k5_xboole_0 @ A @ C ) @ B ) ))).
% 0.86/1.05  thf('15', plain,
% 0.86/1.05      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.86/1.05         ((k5_xboole_0 @ (k3_xboole_0 @ X11 @ X13) @ (k3_xboole_0 @ X12 @ X13))
% 0.86/1.05           = (k3_xboole_0 @ (k5_xboole_0 @ X11 @ X12) @ X13))),
% 0.86/1.05      inference('cnf', [status(esa)], [t112_xboole_1])).
% 0.86/1.05  thf('16', plain,
% 0.86/1.05      (![X0 : $i, X1 : $i]:
% 0.86/1.05         ((k5_xboole_0 @ (k1_tarski @ X0) @ 
% 0.86/1.05           (k3_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 0.86/1.05           = (k3_xboole_0 @ (k5_xboole_0 @ (k1_tarski @ X0) @ X1) @ 
% 0.86/1.05              (k1_tarski @ X0)))),
% 0.86/1.05      inference('sup+', [status(thm)], ['14', '15'])).
% 0.86/1.05  thf('17', plain,
% 0.86/1.05      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.86/1.05      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.86/1.05  thf(t100_xboole_1, axiom,
% 0.86/1.05    (![A:$i,B:$i]:
% 0.86/1.05     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.86/1.05  thf('18', plain,
% 0.86/1.05      (![X9 : $i, X10 : $i]:
% 0.86/1.05         ((k4_xboole_0 @ X9 @ X10)
% 0.86/1.05           = (k5_xboole_0 @ X9 @ (k3_xboole_0 @ X9 @ X10)))),
% 0.86/1.05      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.86/1.05  thf('19', plain,
% 0.86/1.05      (![X0 : $i, X1 : $i]:
% 0.86/1.05         ((k4_xboole_0 @ X0 @ X1)
% 0.86/1.05           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.86/1.05      inference('sup+', [status(thm)], ['17', '18'])).
% 0.86/1.05  thf('20', plain,
% 0.86/1.05      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.86/1.05      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.86/1.05  thf('21', plain,
% 0.86/1.05      (![X0 : $i, X1 : $i]:
% 0.86/1.05         ((k4_xboole_0 @ (k1_tarski @ X0) @ X1)
% 0.86/1.05           = (k3_xboole_0 @ (k1_tarski @ X0) @ 
% 0.86/1.05              (k5_xboole_0 @ (k1_tarski @ X0) @ X1)))),
% 0.86/1.05      inference('demod', [status(thm)], ['16', '19', '20'])).
% 0.86/1.05  thf('22', plain,
% 0.86/1.05      (![X0 : $i, X1 : $i]:
% 0.86/1.05         (((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_tarski @ X0))
% 0.86/1.05          | (r2_hidden @ X0 @ X1))),
% 0.86/1.05      inference('sup+', [status(thm)], ['11', '21'])).
% 0.86/1.05  thf(t69_zfmisc_1, conjecture,
% 0.86/1.05    (![A:$i,B:$i]:
% 0.86/1.05     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) | 
% 0.86/1.05       ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_xboole_0 ) ) ))).
% 0.86/1.05  thf(zf_stmt_0, negated_conjecture,
% 0.86/1.05    (~( ![A:$i,B:$i]:
% 0.86/1.05        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) | 
% 0.86/1.05          ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_xboole_0 ) ) ) )),
% 0.86/1.05    inference('cnf.neg', [status(esa)], [t69_zfmisc_1])).
% 0.86/1.05  thf('23', plain,
% 0.86/1.05      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_tarski @ sk_A))),
% 0.86/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.05  thf('24', plain,
% 0.86/1.05      ((((k1_tarski @ sk_A) != (k1_tarski @ sk_A)) | (r2_hidden @ sk_A @ sk_B))),
% 0.86/1.05      inference('sup-', [status(thm)], ['22', '23'])).
% 0.86/1.05  thf('25', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.86/1.05      inference('simplify', [status(thm)], ['24'])).
% 0.86/1.05  thf('26', plain,
% 0.86/1.05      (![X43 : $i, X44 : $i]:
% 0.86/1.05         (((k3_xboole_0 @ X44 @ (k1_tarski @ X43)) = (k1_tarski @ X43))
% 0.86/1.05          | ~ (r2_hidden @ X43 @ X44))),
% 0.86/1.05      inference('cnf', [status(esa)], [l31_zfmisc_1])).
% 0.86/1.05  thf('27', plain,
% 0.86/1.05      (((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A))),
% 0.86/1.05      inference('sup-', [status(thm)], ['25', '26'])).
% 0.86/1.05  thf('28', plain,
% 0.86/1.05      (![X0 : $i, X1 : $i]:
% 0.86/1.05         ((k4_xboole_0 @ X0 @ X1)
% 0.86/1.05           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.86/1.05      inference('sup+', [status(thm)], ['17', '18'])).
% 0.86/1.05  thf('29', plain,
% 0.86/1.05      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)
% 0.86/1.05         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))),
% 0.86/1.05      inference('sup+', [status(thm)], ['27', '28'])).
% 0.86/1.05  thf(t92_xboole_1, axiom,
% 0.86/1.05    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.86/1.05  thf('30', plain, (![X14 : $i]: ((k5_xboole_0 @ X14 @ X14) = (k1_xboole_0))),
% 0.86/1.05      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.86/1.05  thf('31', plain,
% 0.86/1.05      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))),
% 0.86/1.05      inference('demod', [status(thm)], ['29', '30'])).
% 0.86/1.05  thf('32', plain,
% 0.86/1.05      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_xboole_0))),
% 0.86/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.05  thf('33', plain, ($false),
% 0.86/1.05      inference('simplify_reflect-', [status(thm)], ['31', '32'])).
% 0.86/1.05  
% 0.86/1.05  % SZS output end Refutation
% 0.86/1.05  
% 0.86/1.06  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
