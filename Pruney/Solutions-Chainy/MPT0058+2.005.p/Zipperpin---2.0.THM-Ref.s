%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.La6VfqO645

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:18 EST 2020

% Result     : Theorem 0.70s
% Output     : Refutation 0.70s
% Verified   : 
% Statistics : Number of formulae       :   48 (  56 expanded)
%              Number of leaves         :   16 (  22 expanded)
%              Depth                    :   10
%              Number of atoms          :  412 ( 511 expanded)
%              Number of equality atoms :   38 (  46 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t51_xboole_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
        = A ) ),
    inference('cnf.neg',[status(esa)],[t51_xboole_1])).

thf('0',plain,(
    ( k2_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B ) @ ( k4_xboole_0 @ sk_A @ sk_B ) )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X20 @ ( k4_xboole_0 @ X20 @ X21 ) )
      = ( k3_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X16 ) )
      = ( k2_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('7',plain,(
    ( k2_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) )
 != sk_A ),
    inference(demod,[status(thm)],['0','6'])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('8',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k3_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X4 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['8'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('10',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X11 )
      | ( r2_hidden @ X12 @ X9 )
      | ( X11
       != ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('11',plain,(
    ! [X9: $i,X10: $i,X12: $i] :
      ( ( r2_hidden @ X12 @ X9 )
      | ~ ( r2_hidden @ X12 @ ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
        = ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      | ( r2_hidden @ ( sk_D @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['8'])).

thf('14',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k3_xboole_0 @ X3 @ X4 ) )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X4 )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X3 )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['8'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X1 )
        = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) )
      | ( ( k4_xboole_0 @ X0 @ X1 )
        = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['12','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('21',plain,(
    ! [X14: $i,X15: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X14 @ X15 ) @ X14 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t45_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( B
        = ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) ) )).

thf('22',plain,(
    ! [X18: $i,X19: $i] :
      ( ( X19
        = ( k2_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X18 ) ) )
      | ~ ( r1_tarski @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t45_xboole_1])).

thf('23',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X16 ) )
      = ( k2_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('24',plain,(
    ! [X18: $i,X19: $i] :
      ( ( X19
        = ( k2_xboole_0 @ X18 @ X19 ) )
      | ~ ( r1_tarski @ X18 @ X19 ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['20','27'])).

thf('29',plain,(
    sk_A != sk_A ),
    inference(demod,[status(thm)],['7','28'])).

thf('30',plain,(
    $false ),
    inference(simplify,[status(thm)],['29'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.La6VfqO645
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:15:14 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.70/0.90  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.70/0.90  % Solved by: fo/fo7.sh
% 0.70/0.90  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.70/0.90  % done 425 iterations in 0.437s
% 0.70/0.90  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.70/0.90  % SZS output start Refutation
% 0.70/0.90  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.70/0.90  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.70/0.90  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.70/0.90  thf(sk_B_type, type, sk_B: $i).
% 0.70/0.90  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.70/0.90  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.70/0.90  thf(sk_A_type, type, sk_A: $i).
% 0.70/0.90  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.70/0.90  thf(t51_xboole_1, conjecture,
% 0.70/0.90    (![A:$i,B:$i]:
% 0.70/0.90     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 0.70/0.90       ( A ) ))).
% 0.70/0.90  thf(zf_stmt_0, negated_conjecture,
% 0.70/0.90    (~( ![A:$i,B:$i]:
% 0.70/0.90        ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 0.70/0.90          ( A ) ) )),
% 0.70/0.90    inference('cnf.neg', [status(esa)], [t51_xboole_1])).
% 0.70/0.90  thf('0', plain,
% 0.70/0.90      (((k2_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B) @ 
% 0.70/0.90         (k4_xboole_0 @ sk_A @ sk_B)) != (sk_A))),
% 0.70/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.90  thf(t48_xboole_1, axiom,
% 0.70/0.90    (![A:$i,B:$i]:
% 0.70/0.90     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.70/0.90  thf('1', plain,
% 0.70/0.90      (![X20 : $i, X21 : $i]:
% 0.70/0.90         ((k4_xboole_0 @ X20 @ (k4_xboole_0 @ X20 @ X21))
% 0.70/0.90           = (k3_xboole_0 @ X20 @ X21))),
% 0.70/0.90      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.70/0.90  thf(t39_xboole_1, axiom,
% 0.70/0.90    (![A:$i,B:$i]:
% 0.70/0.90     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.70/0.90  thf('2', plain,
% 0.70/0.90      (![X16 : $i, X17 : $i]:
% 0.70/0.90         ((k2_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X16))
% 0.70/0.90           = (k2_xboole_0 @ X16 @ X17))),
% 0.70/0.90      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.70/0.90  thf('3', plain,
% 0.70/0.90      (![X0 : $i, X1 : $i]:
% 0.70/0.90         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 0.70/0.90           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1))),
% 0.70/0.90      inference('sup+', [status(thm)], ['1', '2'])).
% 0.70/0.90  thf(commutativity_k2_xboole_0, axiom,
% 0.70/0.90    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.70/0.90  thf('4', plain,
% 0.70/0.90      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.70/0.90      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.70/0.90  thf('5', plain,
% 0.70/0.90      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.70/0.90      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.70/0.90  thf('6', plain,
% 0.70/0.90      (![X0 : $i, X1 : $i]:
% 0.70/0.90         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 0.70/0.90           = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.70/0.90      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.70/0.90  thf('7', plain,
% 0.70/0.90      (((k2_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B)) != (sk_A))),
% 0.70/0.90      inference('demod', [status(thm)], ['0', '6'])).
% 0.70/0.90  thf(d4_xboole_0, axiom,
% 0.70/0.90    (![A:$i,B:$i,C:$i]:
% 0.70/0.90     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.70/0.90       ( ![D:$i]:
% 0.70/0.90         ( ( r2_hidden @ D @ C ) <=>
% 0.70/0.90           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.70/0.90  thf('8', plain,
% 0.70/0.90      (![X3 : $i, X4 : $i, X7 : $i]:
% 0.70/0.90         (((X7) = (k3_xboole_0 @ X3 @ X4))
% 0.70/0.90          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X4)
% 0.70/0.90          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 0.70/0.90      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.70/0.90  thf('9', plain,
% 0.70/0.90      (![X0 : $i, X1 : $i]:
% 0.70/0.90         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.70/0.90          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 0.70/0.90      inference('eq_fact', [status(thm)], ['8'])).
% 0.70/0.90  thf(d5_xboole_0, axiom,
% 0.70/0.90    (![A:$i,B:$i,C:$i]:
% 0.70/0.90     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.70/0.90       ( ![D:$i]:
% 0.70/0.90         ( ( r2_hidden @ D @ C ) <=>
% 0.70/0.90           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.70/0.90  thf('10', plain,
% 0.70/0.90      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.70/0.90         (~ (r2_hidden @ X12 @ X11)
% 0.70/0.90          | (r2_hidden @ X12 @ X9)
% 0.70/0.90          | ((X11) != (k4_xboole_0 @ X9 @ X10)))),
% 0.70/0.90      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.70/0.90  thf('11', plain,
% 0.70/0.90      (![X9 : $i, X10 : $i, X12 : $i]:
% 0.70/0.90         ((r2_hidden @ X12 @ X9)
% 0.70/0.90          | ~ (r2_hidden @ X12 @ (k4_xboole_0 @ X9 @ X10)))),
% 0.70/0.90      inference('simplify', [status(thm)], ['10'])).
% 0.70/0.90  thf('12', plain,
% 0.70/0.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.70/0.90         (((k4_xboole_0 @ X1 @ X0)
% 0.70/0.90            = (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))
% 0.70/0.90          | (r2_hidden @ 
% 0.70/0.90             (sk_D @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0) @ X2) @ 
% 0.70/0.90             X1))),
% 0.70/0.90      inference('sup-', [status(thm)], ['9', '11'])).
% 0.70/0.90  thf('13', plain,
% 0.70/0.90      (![X0 : $i, X1 : $i]:
% 0.70/0.90         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.70/0.90          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 0.70/0.90      inference('eq_fact', [status(thm)], ['8'])).
% 0.70/0.90  thf('14', plain,
% 0.70/0.90      (![X3 : $i, X4 : $i, X7 : $i]:
% 0.70/0.90         (((X7) = (k3_xboole_0 @ X3 @ X4))
% 0.70/0.90          | ~ (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X4)
% 0.70/0.90          | ~ (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X3)
% 0.70/0.90          | ~ (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 0.70/0.90      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.70/0.90  thf('15', plain,
% 0.70/0.90      (![X0 : $i, X1 : $i]:
% 0.70/0.90         (((X0) = (k3_xboole_0 @ X1 @ X0))
% 0.70/0.90          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.70/0.90          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 0.70/0.90          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 0.70/0.90      inference('sup-', [status(thm)], ['13', '14'])).
% 0.70/0.90  thf('16', plain,
% 0.70/0.90      (![X0 : $i, X1 : $i]:
% 0.70/0.90         (~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 0.70/0.90          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.70/0.90          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 0.70/0.90      inference('simplify', [status(thm)], ['15'])).
% 0.70/0.90  thf('17', plain,
% 0.70/0.90      (![X0 : $i, X1 : $i]:
% 0.70/0.90         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.70/0.90          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 0.70/0.90      inference('eq_fact', [status(thm)], ['8'])).
% 0.70/0.90  thf('18', plain,
% 0.70/0.90      (![X0 : $i, X1 : $i]:
% 0.70/0.90         (((X0) = (k3_xboole_0 @ X1 @ X0))
% 0.70/0.90          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1))),
% 0.70/0.90      inference('clc', [status(thm)], ['16', '17'])).
% 0.70/0.90  thf('19', plain,
% 0.70/0.90      (![X0 : $i, X1 : $i]:
% 0.70/0.90         (((k4_xboole_0 @ X0 @ X1)
% 0.70/0.90            = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))
% 0.70/0.90          | ((k4_xboole_0 @ X0 @ X1)
% 0.70/0.90              = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))))),
% 0.70/0.90      inference('sup-', [status(thm)], ['12', '18'])).
% 0.70/0.90  thf('20', plain,
% 0.70/0.90      (![X0 : $i, X1 : $i]:
% 0.70/0.90         ((k4_xboole_0 @ X0 @ X1)
% 0.70/0.90           = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.70/0.90      inference('simplify', [status(thm)], ['19'])).
% 0.70/0.90  thf(t17_xboole_1, axiom,
% 0.70/0.90    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.70/0.90  thf('21', plain,
% 0.70/0.90      (![X14 : $i, X15 : $i]: (r1_tarski @ (k3_xboole_0 @ X14 @ X15) @ X14)),
% 0.70/0.90      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.70/0.90  thf(t45_xboole_1, axiom,
% 0.70/0.90    (![A:$i,B:$i]:
% 0.70/0.90     ( ( r1_tarski @ A @ B ) =>
% 0.70/0.90       ( ( B ) = ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) ))).
% 0.70/0.90  thf('22', plain,
% 0.70/0.90      (![X18 : $i, X19 : $i]:
% 0.70/0.90         (((X19) = (k2_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X18)))
% 0.70/0.90          | ~ (r1_tarski @ X18 @ X19))),
% 0.70/0.90      inference('cnf', [status(esa)], [t45_xboole_1])).
% 0.70/0.90  thf('23', plain,
% 0.70/0.90      (![X16 : $i, X17 : $i]:
% 0.70/0.90         ((k2_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X16))
% 0.70/0.90           = (k2_xboole_0 @ X16 @ X17))),
% 0.70/0.90      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.70/0.90  thf('24', plain,
% 0.70/0.90      (![X18 : $i, X19 : $i]:
% 0.70/0.90         (((X19) = (k2_xboole_0 @ X18 @ X19)) | ~ (r1_tarski @ X18 @ X19))),
% 0.70/0.90      inference('demod', [status(thm)], ['22', '23'])).
% 0.70/0.90  thf('25', plain,
% 0.70/0.90      (![X0 : $i, X1 : $i]:
% 0.70/0.90         ((X0) = (k2_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0))),
% 0.70/0.90      inference('sup-', [status(thm)], ['21', '24'])).
% 0.70/0.90  thf('26', plain,
% 0.70/0.90      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.70/0.90      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.70/0.90  thf('27', plain,
% 0.70/0.90      (![X0 : $i, X1 : $i]:
% 0.70/0.90         ((X0) = (k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.70/0.90      inference('demod', [status(thm)], ['25', '26'])).
% 0.70/0.90  thf('28', plain,
% 0.70/0.90      (![X0 : $i, X1 : $i]:
% 0.70/0.90         ((X1) = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.70/0.90      inference('sup+', [status(thm)], ['20', '27'])).
% 0.70/0.90  thf('29', plain, (((sk_A) != (sk_A))),
% 0.70/0.90      inference('demod', [status(thm)], ['7', '28'])).
% 0.70/0.90  thf('30', plain, ($false), inference('simplify', [status(thm)], ['29'])).
% 0.70/0.90  
% 0.70/0.90  % SZS output end Refutation
% 0.70/0.90  
% 0.74/0.91  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
