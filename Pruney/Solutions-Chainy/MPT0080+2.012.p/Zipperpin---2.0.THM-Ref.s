%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.VzadcLlgFa

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:05 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   61 (  79 expanded)
%              Number of leaves         :   18 (  32 expanded)
%              Depth                    :   15
%              Number of atoms          :  409 ( 556 expanded)
%              Number of equality atoms :   38 (  49 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(t73_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
        & ( r1_xboole_0 @ A @ C ) )
     => ( r1_tarski @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ C ) )
       => ( r1_tarski @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t73_xboole_1])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('2',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_xboole_0 @ X5 @ X4 )
        = X4 )
      | ~ ( r1_tarski @ X5 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('3',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X15 @ X16 ) @ X16 )
      = ( k4_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('5',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_C ) @ ( k2_xboole_0 @ sk_B @ sk_C ) )
    = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('6',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X17 @ X18 ) @ X19 )
      = ( k4_xboole_0 @ X17 @ ( k2_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('7',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X17 @ X18 ) @ X19 )
      = ( k4_xboole_0 @ X17 @ ( k2_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('8',plain,
    ( ( k4_xboole_0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_C ) @ sk_B ) @ sk_C )
    = ( k4_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('9',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X13 ) )
      = ( k2_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('10',plain,
    ( ( k2_xboole_0 @ sk_C @ ( k4_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_C ) )
    = ( k2_xboole_0 @ sk_C @ ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_C ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X13 ) )
      = ( k2_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('12',plain,
    ( ( k2_xboole_0 @ sk_C @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_C @ ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_C ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('14',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X15 @ X16 ) @ X16 )
      = ( k4_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('16',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X11 @ X12 ) @ X11 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('17',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_xboole_0 @ X5 @ X4 )
        = X4 )
      | ~ ( r1_tarski @ X5 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,
    ( ( k2_xboole_0 @ sk_C @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = sk_C ),
    inference(demod,[status(thm)],['12','15','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('23',plain,(
    ! [X23: $i,X24: $i] :
      ( r1_tarski @ X23 @ ( k2_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_C ),
    inference('sup+',[status(thm)],['21','24'])).

thf('26',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X11 @ X12 ) @ X11 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t67_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C )
        & ( r1_xboole_0 @ B @ C ) )
     => ( A = k1_xboole_0 ) ) )).

thf('27',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( X20 = k1_xboole_0 )
      | ~ ( r1_tarski @ X20 @ X21 )
      | ~ ( r1_tarski @ X20 @ X22 )
      | ~ ( r1_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t67_xboole_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 )
      | ( ( k4_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ~ ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['25','28'])).

thf('30',plain,(
    r1_xboole_0 @ sk_A @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X13 ) )
      = ( k2_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('33',plain,
    ( ( k2_xboole_0 @ sk_B @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('36',plain,(
    ! [X8: $i] :
      ( ( k2_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,
    ( sk_B
    = ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['33','34','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('40',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    $false ),
    inference(demod,[status(thm)],['0','40'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.VzadcLlgFa
% 0.14/0.36  % Computer   : n007.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 13:44:06 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  % Running portfolio for 600 s
% 0.14/0.36  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.37  % Python version: Python 3.6.8
% 0.14/0.37  % Running in FO mode
% 0.38/0.61  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.38/0.61  % Solved by: fo/fo7.sh
% 0.38/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.61  % done 278 iterations in 0.129s
% 0.38/0.61  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.38/0.61  % SZS output start Refutation
% 0.38/0.61  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.61  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.38/0.61  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.38/0.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.61  thf(sk_C_type, type, sk_C: $i).
% 0.38/0.61  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.38/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.61  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.38/0.61  thf(t73_xboole_1, conjecture,
% 0.38/0.61    (![A:$i,B:$i,C:$i]:
% 0.38/0.61     ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) & ( r1_xboole_0 @ A @ C ) ) =>
% 0.38/0.61       ( r1_tarski @ A @ B ) ))).
% 0.38/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.61    (~( ![A:$i,B:$i,C:$i]:
% 0.38/0.61        ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) & 
% 0.38/0.61            ( r1_xboole_0 @ A @ C ) ) =>
% 0.38/0.61          ( r1_tarski @ A @ B ) ) )),
% 0.38/0.61    inference('cnf.neg', [status(esa)], [t73_xboole_1])).
% 0.38/0.61  thf('0', plain, (~ (r1_tarski @ sk_A @ sk_B)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('1', plain, ((r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf(t12_xboole_1, axiom,
% 0.38/0.61    (![A:$i,B:$i]:
% 0.38/0.61     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.38/0.61  thf('2', plain,
% 0.38/0.61      (![X4 : $i, X5 : $i]:
% 0.38/0.61         (((k2_xboole_0 @ X5 @ X4) = (X4)) | ~ (r1_tarski @ X5 @ X4))),
% 0.38/0.61      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.38/0.61  thf('3', plain,
% 0.38/0.61      (((k2_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))
% 0.38/0.61         = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.38/0.61      inference('sup-', [status(thm)], ['1', '2'])).
% 0.38/0.61  thf(t40_xboole_1, axiom,
% 0.38/0.61    (![A:$i,B:$i]:
% 0.38/0.61     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.38/0.61  thf('4', plain,
% 0.38/0.61      (![X15 : $i, X16 : $i]:
% 0.38/0.61         ((k4_xboole_0 @ (k2_xboole_0 @ X15 @ X16) @ X16)
% 0.38/0.61           = (k4_xboole_0 @ X15 @ X16))),
% 0.38/0.61      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.38/0.61  thf('5', plain,
% 0.38/0.61      (((k4_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_C) @ 
% 0.38/0.61         (k2_xboole_0 @ sk_B @ sk_C))
% 0.38/0.61         = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 0.38/0.61      inference('sup+', [status(thm)], ['3', '4'])).
% 0.38/0.61  thf(t41_xboole_1, axiom,
% 0.38/0.61    (![A:$i,B:$i,C:$i]:
% 0.38/0.61     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.38/0.61       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.38/0.61  thf('6', plain,
% 0.38/0.61      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.38/0.61         ((k4_xboole_0 @ (k4_xboole_0 @ X17 @ X18) @ X19)
% 0.38/0.61           = (k4_xboole_0 @ X17 @ (k2_xboole_0 @ X18 @ X19)))),
% 0.38/0.61      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.38/0.61  thf('7', plain,
% 0.38/0.61      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.38/0.61         ((k4_xboole_0 @ (k4_xboole_0 @ X17 @ X18) @ X19)
% 0.38/0.61           = (k4_xboole_0 @ X17 @ (k2_xboole_0 @ X18 @ X19)))),
% 0.38/0.61      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.38/0.61  thf('8', plain,
% 0.38/0.61      (((k4_xboole_0 @ (k4_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_C) @ sk_B) @ 
% 0.38/0.61         sk_C) = (k4_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_C))),
% 0.38/0.61      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.38/0.61  thf(t39_xboole_1, axiom,
% 0.38/0.61    (![A:$i,B:$i]:
% 0.38/0.61     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.38/0.61  thf('9', plain,
% 0.38/0.61      (![X13 : $i, X14 : $i]:
% 0.38/0.61         ((k2_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X13))
% 0.38/0.61           = (k2_xboole_0 @ X13 @ X14))),
% 0.38/0.61      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.38/0.61  thf('10', plain,
% 0.38/0.61      (((k2_xboole_0 @ sk_C @ 
% 0.38/0.61         (k4_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_C))
% 0.38/0.61         = (k2_xboole_0 @ sk_C @ 
% 0.38/0.61            (k4_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_C) @ sk_B)))),
% 0.38/0.61      inference('sup+', [status(thm)], ['8', '9'])).
% 0.38/0.61  thf('11', plain,
% 0.38/0.61      (![X13 : $i, X14 : $i]:
% 0.38/0.61         ((k2_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X13))
% 0.38/0.61           = (k2_xboole_0 @ X13 @ X14))),
% 0.38/0.61      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.38/0.61  thf('12', plain,
% 0.38/0.61      (((k2_xboole_0 @ sk_C @ (k4_xboole_0 @ sk_A @ sk_B))
% 0.38/0.61         = (k2_xboole_0 @ sk_C @ 
% 0.38/0.61            (k4_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_C) @ sk_B)))),
% 0.38/0.61      inference('demod', [status(thm)], ['10', '11'])).
% 0.38/0.61  thf(commutativity_k2_xboole_0, axiom,
% 0.38/0.61    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.38/0.61  thf('13', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.38/0.61      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.38/0.61  thf('14', plain,
% 0.38/0.61      (![X15 : $i, X16 : $i]:
% 0.38/0.61         ((k4_xboole_0 @ (k2_xboole_0 @ X15 @ X16) @ X16)
% 0.38/0.61           = (k4_xboole_0 @ X15 @ X16))),
% 0.38/0.61      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.38/0.61  thf('15', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i]:
% 0.38/0.61         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 0.38/0.61           = (k4_xboole_0 @ X0 @ X1))),
% 0.38/0.61      inference('sup+', [status(thm)], ['13', '14'])).
% 0.38/0.61  thf(t36_xboole_1, axiom,
% 0.38/0.61    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.38/0.61  thf('16', plain,
% 0.38/0.61      (![X11 : $i, X12 : $i]: (r1_tarski @ (k4_xboole_0 @ X11 @ X12) @ X11)),
% 0.38/0.61      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.38/0.61  thf('17', plain,
% 0.38/0.61      (![X4 : $i, X5 : $i]:
% 0.38/0.61         (((k2_xboole_0 @ X5 @ X4) = (X4)) | ~ (r1_tarski @ X5 @ X4))),
% 0.38/0.61      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.38/0.61  thf('18', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i]:
% 0.38/0.61         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 0.38/0.61      inference('sup-', [status(thm)], ['16', '17'])).
% 0.38/0.61  thf('19', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.38/0.61      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.38/0.61  thf('20', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i]:
% 0.38/0.61         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)) = (X0))),
% 0.38/0.61      inference('demod', [status(thm)], ['18', '19'])).
% 0.38/0.61  thf('21', plain,
% 0.38/0.61      (((k2_xboole_0 @ sk_C @ (k4_xboole_0 @ sk_A @ sk_B)) = (sk_C))),
% 0.38/0.61      inference('demod', [status(thm)], ['12', '15', '20'])).
% 0.38/0.61  thf('22', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.38/0.61      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.38/0.61  thf(t7_xboole_1, axiom,
% 0.38/0.61    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.38/0.61  thf('23', plain,
% 0.38/0.61      (![X23 : $i, X24 : $i]: (r1_tarski @ X23 @ (k2_xboole_0 @ X23 @ X24))),
% 0.38/0.61      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.38/0.61  thf('24', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.38/0.61      inference('sup+', [status(thm)], ['22', '23'])).
% 0.38/0.61  thf('25', plain, ((r1_tarski @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_C)),
% 0.38/0.61      inference('sup+', [status(thm)], ['21', '24'])).
% 0.38/0.61  thf('26', plain,
% 0.38/0.61      (![X11 : $i, X12 : $i]: (r1_tarski @ (k4_xboole_0 @ X11 @ X12) @ X11)),
% 0.38/0.61      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.38/0.61  thf(t67_xboole_1, axiom,
% 0.38/0.61    (![A:$i,B:$i,C:$i]:
% 0.38/0.61     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) & 
% 0.38/0.61         ( r1_xboole_0 @ B @ C ) ) =>
% 0.38/0.61       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.38/0.61  thf('27', plain,
% 0.38/0.61      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.38/0.61         (((X20) = (k1_xboole_0))
% 0.38/0.61          | ~ (r1_tarski @ X20 @ X21)
% 0.38/0.61          | ~ (r1_tarski @ X20 @ X22)
% 0.38/0.61          | ~ (r1_xboole_0 @ X21 @ X22))),
% 0.38/0.61      inference('cnf', [status(esa)], [t67_xboole_1])).
% 0.38/0.61  thf('28', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.61         (~ (r1_xboole_0 @ X0 @ X2)
% 0.38/0.61          | ~ (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X2)
% 0.38/0.61          | ((k4_xboole_0 @ X0 @ X1) = (k1_xboole_0)))),
% 0.38/0.61      inference('sup-', [status(thm)], ['26', '27'])).
% 0.38/0.61  thf('29', plain,
% 0.38/0.61      ((((k4_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.38/0.61        | ~ (r1_xboole_0 @ sk_A @ sk_C))),
% 0.38/0.61      inference('sup-', [status(thm)], ['25', '28'])).
% 0.38/0.61  thf('30', plain, ((r1_xboole_0 @ sk_A @ sk_C)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('31', plain, (((k4_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.38/0.61      inference('demod', [status(thm)], ['29', '30'])).
% 0.38/0.61  thf('32', plain,
% 0.38/0.61      (![X13 : $i, X14 : $i]:
% 0.38/0.61         ((k2_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X13))
% 0.38/0.61           = (k2_xboole_0 @ X13 @ X14))),
% 0.38/0.61      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.38/0.61  thf('33', plain,
% 0.38/0.61      (((k2_xboole_0 @ sk_B @ k1_xboole_0) = (k2_xboole_0 @ sk_B @ sk_A))),
% 0.38/0.61      inference('sup+', [status(thm)], ['31', '32'])).
% 0.38/0.61  thf('34', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.38/0.61      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.38/0.61  thf('35', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.38/0.61      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.38/0.61  thf(t1_boole, axiom,
% 0.38/0.61    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.38/0.61  thf('36', plain, (![X8 : $i]: ((k2_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 0.38/0.61      inference('cnf', [status(esa)], [t1_boole])).
% 0.38/0.61  thf('37', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.38/0.61      inference('sup+', [status(thm)], ['35', '36'])).
% 0.38/0.61  thf('38', plain, (((sk_B) = (k2_xboole_0 @ sk_B @ sk_A))),
% 0.38/0.61      inference('demod', [status(thm)], ['33', '34', '37'])).
% 0.38/0.61  thf('39', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.38/0.61      inference('sup+', [status(thm)], ['22', '23'])).
% 0.38/0.61  thf('40', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.38/0.61      inference('sup+', [status(thm)], ['38', '39'])).
% 0.38/0.61  thf('41', plain, ($false), inference('demod', [status(thm)], ['0', '40'])).
% 0.38/0.61  
% 0.38/0.61  % SZS output end Refutation
% 0.38/0.61  
% 0.38/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
