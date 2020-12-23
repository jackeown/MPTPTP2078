%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.pTDD1UVpzD

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:51 EST 2020

% Result     : Theorem 0.60s
% Output     : Refutation 0.60s
% Verified   : 
% Statistics : Number of formulae       :   56 (  75 expanded)
%              Number of leaves         :   18 (  30 expanded)
%              Depth                    :    9
%              Number of atoms          :  356 ( 551 expanded)
%              Number of equality atoms :   13 (  20 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(t114_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_xboole_0 @ A @ D )
        & ( r1_xboole_0 @ B @ D )
        & ( r1_xboole_0 @ C @ D ) )
     => ( r1_xboole_0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) @ D ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( r1_xboole_0 @ A @ D )
          & ( r1_xboole_0 @ B @ D )
          & ( r1_xboole_0 @ C @ D ) )
       => ( r1_xboole_0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) @ D ) ) ),
    inference('cnf.neg',[status(esa)],[t114_xboole_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_B ) @ sk_C ) @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C )
      = ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('1',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k2_xboole_0 @ X8 @ ( k2_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('2',plain,(
    ~ ( r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) @ sk_D ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('3',plain,(
    r1_xboole_0 @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ ( k4_xboole_0 @ X6 @ X7 ) )
      = ( k3_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('6',plain,(
    ! [X4: $i,X5: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X4 @ X5 ) @ X4 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['4','7'])).

thf(t63_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf('9',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ X11 @ X12 )
      | ~ ( r1_xboole_0 @ X12 @ X13 )
      | ( r1_xboole_0 @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      | ~ ( r1_xboole_0 @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X0 @ sk_C ) @ sk_D ) ),
    inference('sup-',[status(thm)],['3','10'])).

thf('12',plain,(
    r1_xboole_0 @ sk_B @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('13',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('14',plain,(
    r1_xboole_0 @ sk_D @ sk_B ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t78_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
        = ( k3_xboole_0 @ A @ C ) ) ) )).

thf('15',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r1_xboole_0 @ X16 @ X17 )
      | ( ( k3_xboole_0 @ X16 @ ( k2_xboole_0 @ X17 @ X18 ) )
        = ( k3_xboole_0 @ X16 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t78_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_D @ ( k2_xboole_0 @ sk_B @ X0 ) )
      = ( k3_xboole_0 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t75_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ~ ( r1_xboole_0 @ A @ B )
        & ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ B ) ) )).

thf('18',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r1_xboole_0 @ X14 @ X15 )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X14 @ X15 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[t75_xboole_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ ( k3_xboole_0 @ sk_D @ X0 ) @ sk_D )
      | ( r1_xboole_0 @ ( k2_xboole_0 @ sk_B @ X0 ) @ sk_D ) ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('21',plain,(
    r1_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_C ) @ sk_D ),
    inference('sup-',[status(thm)],['11','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('23',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ X11 @ X12 )
      | ~ ( r1_xboole_0 @ X12 @ X13 )
      | ( r1_xboole_0 @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_xboole_0 @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_C ) @ X0 ) @ sk_D ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('27',plain,(
    r1_xboole_0 @ sk_A @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('29',plain,(
    r1_xboole_0 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r1_xboole_0 @ X16 @ X17 )
      | ( ( k3_xboole_0 @ X16 @ ( k2_xboole_0 @ X17 @ X18 ) )
        = ( k3_xboole_0 @ X16 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t78_xboole_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_D @ ( k2_xboole_0 @ sk_A @ X0 ) )
      = ( k3_xboole_0 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ ( k3_xboole_0 @ sk_D @ X0 ) @ sk_D )
      | ( r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ X0 ) @ sk_D ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X0 @ sk_D ) @ sk_D )
      | ( r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ X0 ) @ sk_D ) ) ),
    inference('sup-',[status(thm)],['26','33'])).

thf('35',plain,(
    r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) @ sk_D ),
    inference('sup-',[status(thm)],['25','34'])).

thf('36',plain,(
    $false ),
    inference(demod,[status(thm)],['2','35'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.pTDD1UVpzD
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:23:05 EST 2020
% 0.21/0.35  % CPUTime    : 
% 0.21/0.35  % Running portfolio for 600 s
% 0.21/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.21/0.35  % Number of cores: 8
% 0.21/0.35  % Python version: Python 3.6.8
% 0.21/0.36  % Running in FO mode
% 0.60/0.79  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.60/0.79  % Solved by: fo/fo7.sh
% 0.60/0.79  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.60/0.79  % done 573 iterations in 0.302s
% 0.60/0.79  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.60/0.79  % SZS output start Refutation
% 0.60/0.79  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.60/0.79  thf(sk_D_type, type, sk_D: $i).
% 0.60/0.79  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.60/0.79  thf(sk_A_type, type, sk_A: $i).
% 0.60/0.79  thf(sk_C_type, type, sk_C: $i).
% 0.60/0.79  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.60/0.79  thf(sk_B_type, type, sk_B: $i).
% 0.60/0.79  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.60/0.79  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.60/0.79  thf(t114_xboole_1, conjecture,
% 0.60/0.79    (![A:$i,B:$i,C:$i,D:$i]:
% 0.60/0.79     ( ( ( r1_xboole_0 @ A @ D ) & ( r1_xboole_0 @ B @ D ) & 
% 0.60/0.79         ( r1_xboole_0 @ C @ D ) ) =>
% 0.60/0.79       ( r1_xboole_0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) @ D ) ))).
% 0.60/0.79  thf(zf_stmt_0, negated_conjecture,
% 0.60/0.79    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.60/0.79        ( ( ( r1_xboole_0 @ A @ D ) & ( r1_xboole_0 @ B @ D ) & 
% 0.60/0.79            ( r1_xboole_0 @ C @ D ) ) =>
% 0.60/0.79          ( r1_xboole_0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) @ D ) ) )),
% 0.60/0.79    inference('cnf.neg', [status(esa)], [t114_xboole_1])).
% 0.60/0.79  thf('0', plain,
% 0.60/0.79      (~ (r1_xboole_0 @ (k2_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_B) @ sk_C) @ 
% 0.60/0.79          sk_D)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf(t4_xboole_1, axiom,
% 0.60/0.79    (![A:$i,B:$i,C:$i]:
% 0.60/0.79     ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 0.60/0.79       ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.60/0.79  thf('1', plain,
% 0.60/0.79      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.60/0.79         ((k2_xboole_0 @ (k2_xboole_0 @ X8 @ X9) @ X10)
% 0.60/0.79           = (k2_xboole_0 @ X8 @ (k2_xboole_0 @ X9 @ X10)))),
% 0.60/0.79      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.60/0.79  thf('2', plain,
% 0.60/0.79      (~ (r1_xboole_0 @ (k2_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)) @ 
% 0.60/0.79          sk_D)),
% 0.60/0.79      inference('demod', [status(thm)], ['0', '1'])).
% 0.60/0.79  thf('3', plain, ((r1_xboole_0 @ sk_C @ sk_D)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf(commutativity_k3_xboole_0, axiom,
% 0.60/0.79    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.60/0.79  thf('4', plain,
% 0.60/0.79      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.60/0.79      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.60/0.79  thf(t48_xboole_1, axiom,
% 0.60/0.79    (![A:$i,B:$i]:
% 0.60/0.79     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.60/0.79  thf('5', plain,
% 0.60/0.79      (![X6 : $i, X7 : $i]:
% 0.60/0.79         ((k4_xboole_0 @ X6 @ (k4_xboole_0 @ X6 @ X7))
% 0.60/0.79           = (k3_xboole_0 @ X6 @ X7))),
% 0.60/0.79      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.60/0.79  thf(t36_xboole_1, axiom,
% 0.60/0.79    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.60/0.79  thf('6', plain,
% 0.60/0.79      (![X4 : $i, X5 : $i]: (r1_tarski @ (k4_xboole_0 @ X4 @ X5) @ X4)),
% 0.60/0.79      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.60/0.79  thf('7', plain,
% 0.60/0.79      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 0.60/0.79      inference('sup+', [status(thm)], ['5', '6'])).
% 0.60/0.79  thf('8', plain,
% 0.60/0.79      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.60/0.79      inference('sup+', [status(thm)], ['4', '7'])).
% 0.60/0.79  thf(t63_xboole_1, axiom,
% 0.60/0.79    (![A:$i,B:$i,C:$i]:
% 0.60/0.79     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 0.60/0.79       ( r1_xboole_0 @ A @ C ) ))).
% 0.60/0.79  thf('9', plain,
% 0.60/0.79      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.60/0.79         (~ (r1_tarski @ X11 @ X12)
% 0.60/0.79          | ~ (r1_xboole_0 @ X12 @ X13)
% 0.60/0.79          | (r1_xboole_0 @ X11 @ X13))),
% 0.60/0.79      inference('cnf', [status(esa)], [t63_xboole_1])).
% 0.60/0.79  thf('10', plain,
% 0.60/0.79      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.60/0.79         ((r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 0.60/0.79          | ~ (r1_xboole_0 @ X0 @ X2))),
% 0.60/0.79      inference('sup-', [status(thm)], ['8', '9'])).
% 0.60/0.79  thf('11', plain,
% 0.60/0.79      (![X0 : $i]: (r1_xboole_0 @ (k3_xboole_0 @ X0 @ sk_C) @ sk_D)),
% 0.60/0.79      inference('sup-', [status(thm)], ['3', '10'])).
% 0.60/0.79  thf('12', plain, ((r1_xboole_0 @ sk_B @ sk_D)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf(symmetry_r1_xboole_0, axiom,
% 0.60/0.79    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.60/0.79  thf('13', plain,
% 0.60/0.79      (![X2 : $i, X3 : $i]:
% 0.60/0.79         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 0.60/0.79      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.60/0.79  thf('14', plain, ((r1_xboole_0 @ sk_D @ sk_B)),
% 0.60/0.79      inference('sup-', [status(thm)], ['12', '13'])).
% 0.60/0.79  thf(t78_xboole_1, axiom,
% 0.60/0.79    (![A:$i,B:$i,C:$i]:
% 0.60/0.79     ( ( r1_xboole_0 @ A @ B ) =>
% 0.60/0.79       ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) =
% 0.60/0.79         ( k3_xboole_0 @ A @ C ) ) ))).
% 0.60/0.79  thf('15', plain,
% 0.60/0.79      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.60/0.79         (~ (r1_xboole_0 @ X16 @ X17)
% 0.60/0.79          | ((k3_xboole_0 @ X16 @ (k2_xboole_0 @ X17 @ X18))
% 0.60/0.79              = (k3_xboole_0 @ X16 @ X18)))),
% 0.60/0.79      inference('cnf', [status(esa)], [t78_xboole_1])).
% 0.60/0.79  thf('16', plain,
% 0.60/0.79      (![X0 : $i]:
% 0.60/0.79         ((k3_xboole_0 @ sk_D @ (k2_xboole_0 @ sk_B @ X0))
% 0.60/0.79           = (k3_xboole_0 @ sk_D @ X0))),
% 0.60/0.79      inference('sup-', [status(thm)], ['14', '15'])).
% 0.60/0.79  thf('17', plain,
% 0.60/0.79      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.60/0.79      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.60/0.79  thf(t75_xboole_1, axiom,
% 0.60/0.79    (![A:$i,B:$i]:
% 0.60/0.79     ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.60/0.79          ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ B ) ) ))).
% 0.60/0.79  thf('18', plain,
% 0.60/0.79      (![X14 : $i, X15 : $i]:
% 0.60/0.79         ((r1_xboole_0 @ X14 @ X15)
% 0.60/0.79          | ~ (r1_xboole_0 @ (k3_xboole_0 @ X14 @ X15) @ X15))),
% 0.60/0.79      inference('cnf', [status(esa)], [t75_xboole_1])).
% 0.60/0.79  thf('19', plain,
% 0.60/0.79      (![X0 : $i, X1 : $i]:
% 0.60/0.79         (~ (r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1)
% 0.60/0.79          | (r1_xboole_0 @ X0 @ X1))),
% 0.60/0.79      inference('sup-', [status(thm)], ['17', '18'])).
% 0.60/0.79  thf('20', plain,
% 0.60/0.79      (![X0 : $i]:
% 0.60/0.79         (~ (r1_xboole_0 @ (k3_xboole_0 @ sk_D @ X0) @ sk_D)
% 0.60/0.79          | (r1_xboole_0 @ (k2_xboole_0 @ sk_B @ X0) @ sk_D))),
% 0.60/0.79      inference('sup-', [status(thm)], ['16', '19'])).
% 0.60/0.79  thf('21', plain, ((r1_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_C) @ sk_D)),
% 0.60/0.79      inference('sup-', [status(thm)], ['11', '20'])).
% 0.60/0.79  thf('22', plain,
% 0.60/0.79      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 0.60/0.79      inference('sup+', [status(thm)], ['5', '6'])).
% 0.60/0.79  thf('23', plain,
% 0.60/0.79      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.60/0.79         (~ (r1_tarski @ X11 @ X12)
% 0.60/0.79          | ~ (r1_xboole_0 @ X12 @ X13)
% 0.60/0.79          | (r1_xboole_0 @ X11 @ X13))),
% 0.60/0.79      inference('cnf', [status(esa)], [t63_xboole_1])).
% 0.60/0.79  thf('24', plain,
% 0.60/0.79      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.60/0.79         ((r1_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X2)
% 0.60/0.79          | ~ (r1_xboole_0 @ X0 @ X2))),
% 0.60/0.79      inference('sup-', [status(thm)], ['22', '23'])).
% 0.60/0.79  thf('25', plain,
% 0.60/0.79      (![X0 : $i]:
% 0.60/0.79         (r1_xboole_0 @ (k3_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_C) @ X0) @ sk_D)),
% 0.60/0.79      inference('sup-', [status(thm)], ['21', '24'])).
% 0.60/0.79  thf('26', plain,
% 0.60/0.79      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.60/0.79      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.60/0.79  thf('27', plain, ((r1_xboole_0 @ sk_A @ sk_D)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('28', plain,
% 0.60/0.79      (![X2 : $i, X3 : $i]:
% 0.60/0.79         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 0.60/0.79      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.60/0.79  thf('29', plain, ((r1_xboole_0 @ sk_D @ sk_A)),
% 0.60/0.79      inference('sup-', [status(thm)], ['27', '28'])).
% 0.60/0.79  thf('30', plain,
% 0.60/0.79      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.60/0.79         (~ (r1_xboole_0 @ X16 @ X17)
% 0.60/0.79          | ((k3_xboole_0 @ X16 @ (k2_xboole_0 @ X17 @ X18))
% 0.60/0.79              = (k3_xboole_0 @ X16 @ X18)))),
% 0.60/0.79      inference('cnf', [status(esa)], [t78_xboole_1])).
% 0.60/0.79  thf('31', plain,
% 0.60/0.79      (![X0 : $i]:
% 0.60/0.79         ((k3_xboole_0 @ sk_D @ (k2_xboole_0 @ sk_A @ X0))
% 0.60/0.79           = (k3_xboole_0 @ sk_D @ X0))),
% 0.60/0.79      inference('sup-', [status(thm)], ['29', '30'])).
% 0.60/0.79  thf('32', plain,
% 0.60/0.79      (![X0 : $i, X1 : $i]:
% 0.60/0.79         (~ (r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1)
% 0.60/0.79          | (r1_xboole_0 @ X0 @ X1))),
% 0.60/0.79      inference('sup-', [status(thm)], ['17', '18'])).
% 0.60/0.79  thf('33', plain,
% 0.60/0.79      (![X0 : $i]:
% 0.60/0.79         (~ (r1_xboole_0 @ (k3_xboole_0 @ sk_D @ X0) @ sk_D)
% 0.60/0.79          | (r1_xboole_0 @ (k2_xboole_0 @ sk_A @ X0) @ sk_D))),
% 0.60/0.79      inference('sup-', [status(thm)], ['31', '32'])).
% 0.60/0.79  thf('34', plain,
% 0.60/0.79      (![X0 : $i]:
% 0.60/0.79         (~ (r1_xboole_0 @ (k3_xboole_0 @ X0 @ sk_D) @ sk_D)
% 0.60/0.79          | (r1_xboole_0 @ (k2_xboole_0 @ sk_A @ X0) @ sk_D))),
% 0.60/0.79      inference('sup-', [status(thm)], ['26', '33'])).
% 0.60/0.79  thf('35', plain,
% 0.60/0.79      ((r1_xboole_0 @ (k2_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)) @ sk_D)),
% 0.60/0.79      inference('sup-', [status(thm)], ['25', '34'])).
% 0.60/0.79  thf('36', plain, ($false), inference('demod', [status(thm)], ['2', '35'])).
% 0.60/0.79  
% 0.60/0.79  % SZS output end Refutation
% 0.60/0.79  
% 0.60/0.80  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
