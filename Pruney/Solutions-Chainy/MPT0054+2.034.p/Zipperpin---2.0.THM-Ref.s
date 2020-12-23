%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.rhCu1P3zWQ

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:12 EST 2020

% Result     : Theorem 11.09s
% Output     : Refutation 11.09s
% Verified   : 
% Statistics : Number of formulae       :   61 (  75 expanded)
%              Number of leaves         :   18 (  30 expanded)
%              Depth                    :   11
%              Number of atoms          :  473 ( 594 expanded)
%              Number of equality atoms :   49 (  62 expanded)
%              Maximal formula depth    :   10 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t47_xboole_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
        = ( k4_xboole_0 @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t47_xboole_1])).

thf('0',plain,(
    ( k4_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_A @ sk_B ) )
 != ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('2',plain,(
    ( k4_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_A ) )
 != ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X18 ) )
      = ( k2_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t24_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ C ) ) ) )).

thf('5',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k2_xboole_0 @ X11 @ ( k3_xboole_0 @ X12 @ X13 ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X11 @ X12 ) @ ( k2_xboole_0 @ X11 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t24_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X2 ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X1 @ X2 ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['3','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X2 ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ X1 ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X2 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['7','10'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('12',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X16 @ X17 ) @ X16 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('13',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_xboole_0 @ X8 @ X7 )
        = X7 )
      | ~ ( r1_tarski @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k2_xboole_0 @ X11 @ ( k3_xboole_0 @ X12 @ X13 ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X11 @ X12 ) @ ( k2_xboole_0 @ X11 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t24_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X0 @ X2 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) )
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('21',plain,(
    ! [X20: $i] :
      ( ( k4_xboole_0 @ X20 @ k1_xboole_0 )
      = X20 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('22',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X16 @ X17 ) @ X16 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_xboole_0 @ X8 @ X7 )
        = X7 )
      | ~ ( r1_tarski @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k2_xboole_0 @ X11 @ ( k3_xboole_0 @ X12 @ X13 ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X11 @ X12 ) @ ( k2_xboole_0 @ X11 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t24_xboole_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = A ) )).

thf('28',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k2_xboole_0 @ X9 @ ( k3_xboole_0 @ X9 @ X10 ) )
      = X9 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) )
      = X0 ) ),
    inference(demod,[status(thm)],['20','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['11','30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('34',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X21 @ X22 ) @ X22 )
      = ( k4_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['32','35'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('37',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X23 @ X24 ) @ X25 )
      = ( k4_xboole_0 @ X23 @ ( k2_xboole_0 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('38',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k2_xboole_0 @ X9 @ ( k3_xboole_0 @ X9 @ X10 ) )
      = X9 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,(
    ( k4_xboole_0 @ sk_A @ sk_B )
 != ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['2','39'])).

thf('41',plain,(
    $false ),
    inference(simplify,[status(thm)],['40'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.rhCu1P3zWQ
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:55:49 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 11.09/11.27  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 11.09/11.27  % Solved by: fo/fo7.sh
% 11.09/11.27  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 11.09/11.27  % done 7292 iterations in 10.813s
% 11.09/11.27  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 11.09/11.27  % SZS output start Refutation
% 11.09/11.27  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 11.09/11.27  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 11.09/11.27  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 11.09/11.27  thf(sk_A_type, type, sk_A: $i).
% 11.09/11.27  thf(sk_B_type, type, sk_B: $i).
% 11.09/11.27  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 11.09/11.27  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 11.09/11.27  thf(t47_xboole_1, conjecture,
% 11.09/11.27    (![A:$i,B:$i]:
% 11.09/11.27     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 11.09/11.27  thf(zf_stmt_0, negated_conjecture,
% 11.09/11.27    (~( ![A:$i,B:$i]:
% 11.09/11.27        ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) =
% 11.09/11.27          ( k4_xboole_0 @ A @ B ) ) )),
% 11.09/11.27    inference('cnf.neg', [status(esa)], [t47_xboole_1])).
% 11.09/11.27  thf('0', plain,
% 11.09/11.27      (((k4_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_A @ sk_B))
% 11.09/11.27         != (k4_xboole_0 @ sk_A @ sk_B))),
% 11.09/11.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.09/11.27  thf(commutativity_k3_xboole_0, axiom,
% 11.09/11.27    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 11.09/11.27  thf('1', plain,
% 11.09/11.27      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 11.09/11.27      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 11.09/11.27  thf('2', plain,
% 11.09/11.27      (((k4_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_A))
% 11.09/11.27         != (k4_xboole_0 @ sk_A @ sk_B))),
% 11.09/11.27      inference('demod', [status(thm)], ['0', '1'])).
% 11.09/11.27  thf(t39_xboole_1, axiom,
% 11.09/11.27    (![A:$i,B:$i]:
% 11.09/11.27     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 11.09/11.27  thf('3', plain,
% 11.09/11.27      (![X18 : $i, X19 : $i]:
% 11.09/11.27         ((k2_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X18))
% 11.09/11.27           = (k2_xboole_0 @ X18 @ X19))),
% 11.09/11.27      inference('cnf', [status(esa)], [t39_xboole_1])).
% 11.09/11.27  thf(commutativity_k2_xboole_0, axiom,
% 11.09/11.27    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 11.09/11.27  thf('4', plain,
% 11.09/11.27      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 11.09/11.27      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 11.09/11.27  thf(t24_xboole_1, axiom,
% 11.09/11.27    (![A:$i,B:$i,C:$i]:
% 11.09/11.27     ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) =
% 11.09/11.27       ( k3_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ C ) ) ))).
% 11.09/11.27  thf('5', plain,
% 11.09/11.27      (![X11 : $i, X12 : $i, X13 : $i]:
% 11.09/11.27         ((k2_xboole_0 @ X11 @ (k3_xboole_0 @ X12 @ X13))
% 11.09/11.27           = (k3_xboole_0 @ (k2_xboole_0 @ X11 @ X12) @ 
% 11.09/11.27              (k2_xboole_0 @ X11 @ X13)))),
% 11.09/11.27      inference('cnf', [status(esa)], [t24_xboole_1])).
% 11.09/11.27  thf('6', plain,
% 11.09/11.27      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.09/11.27         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X2))
% 11.09/11.27           = (k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X0 @ X2)))),
% 11.09/11.27      inference('sup+', [status(thm)], ['4', '5'])).
% 11.09/11.27  thf('7', plain,
% 11.09/11.27      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.09/11.27         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X1 @ X2))
% 11.09/11.27           = (k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ 
% 11.09/11.27              (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X2)))),
% 11.09/11.27      inference('sup+', [status(thm)], ['3', '6'])).
% 11.09/11.27  thf('8', plain,
% 11.09/11.27      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 11.09/11.27      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 11.09/11.27  thf('9', plain,
% 11.09/11.27      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.09/11.27         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X2))
% 11.09/11.27           = (k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X0 @ X2)))),
% 11.09/11.27      inference('sup+', [status(thm)], ['4', '5'])).
% 11.09/11.27  thf('10', plain,
% 11.09/11.27      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.09/11.27         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ X1))
% 11.09/11.27           = (k3_xboole_0 @ (k2_xboole_0 @ X2 @ X0) @ (k2_xboole_0 @ X1 @ X0)))),
% 11.09/11.27      inference('sup+', [status(thm)], ['8', '9'])).
% 11.09/11.27  thf('11', plain,
% 11.09/11.27      (![X0 : $i, X1 : $i]:
% 11.09/11.27         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1)))
% 11.09/11.27           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X1 @ X0)))),
% 11.09/11.27      inference('sup+', [status(thm)], ['7', '10'])).
% 11.09/11.27  thf(t36_xboole_1, axiom,
% 11.09/11.27    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 11.09/11.27  thf('12', plain,
% 11.09/11.27      (![X16 : $i, X17 : $i]: (r1_tarski @ (k4_xboole_0 @ X16 @ X17) @ X16)),
% 11.09/11.27      inference('cnf', [status(esa)], [t36_xboole_1])).
% 11.09/11.27  thf(t12_xboole_1, axiom,
% 11.09/11.27    (![A:$i,B:$i]:
% 11.09/11.27     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 11.09/11.27  thf('13', plain,
% 11.09/11.27      (![X7 : $i, X8 : $i]:
% 11.09/11.27         (((k2_xboole_0 @ X8 @ X7) = (X7)) | ~ (r1_tarski @ X8 @ X7))),
% 11.09/11.27      inference('cnf', [status(esa)], [t12_xboole_1])).
% 11.09/11.27  thf('14', plain,
% 11.09/11.27      (![X0 : $i, X1 : $i]:
% 11.09/11.27         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 11.09/11.27      inference('sup-', [status(thm)], ['12', '13'])).
% 11.09/11.27  thf('15', plain,
% 11.09/11.27      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 11.09/11.27      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 11.09/11.27  thf('16', plain,
% 11.09/11.27      (![X0 : $i, X1 : $i]:
% 11.09/11.27         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)) = (X0))),
% 11.09/11.27      inference('demod', [status(thm)], ['14', '15'])).
% 11.09/11.27  thf('17', plain,
% 11.09/11.27      (![X11 : $i, X12 : $i, X13 : $i]:
% 11.09/11.27         ((k2_xboole_0 @ X11 @ (k3_xboole_0 @ X12 @ X13))
% 11.09/11.27           = (k3_xboole_0 @ (k2_xboole_0 @ X11 @ X12) @ 
% 11.09/11.27              (k2_xboole_0 @ X11 @ X13)))),
% 11.09/11.27      inference('cnf', [status(esa)], [t24_xboole_1])).
% 11.09/11.27  thf('18', plain,
% 11.09/11.27      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.09/11.27         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X0 @ X1)))
% 11.09/11.27           = (k3_xboole_0 @ (k2_xboole_0 @ X0 @ X2) @ X0))),
% 11.09/11.27      inference('sup+', [status(thm)], ['16', '17'])).
% 11.09/11.27  thf('19', plain,
% 11.09/11.27      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 11.09/11.27      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 11.09/11.27  thf('20', plain,
% 11.09/11.27      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.09/11.27         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X0 @ X1)))
% 11.09/11.27           = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X2)))),
% 11.09/11.27      inference('demod', [status(thm)], ['18', '19'])).
% 11.09/11.27  thf(t3_boole, axiom,
% 11.09/11.27    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 11.09/11.27  thf('21', plain, (![X20 : $i]: ((k4_xboole_0 @ X20 @ k1_xboole_0) = (X20))),
% 11.09/11.27      inference('cnf', [status(esa)], [t3_boole])).
% 11.09/11.27  thf('22', plain,
% 11.09/11.27      (![X16 : $i, X17 : $i]: (r1_tarski @ (k4_xboole_0 @ X16 @ X17) @ X16)),
% 11.09/11.27      inference('cnf', [status(esa)], [t36_xboole_1])).
% 11.09/11.27  thf('23', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 11.09/11.27      inference('sup+', [status(thm)], ['21', '22'])).
% 11.09/11.27  thf('24', plain,
% 11.09/11.27      (![X7 : $i, X8 : $i]:
% 11.09/11.27         (((k2_xboole_0 @ X8 @ X7) = (X7)) | ~ (r1_tarski @ X8 @ X7))),
% 11.09/11.27      inference('cnf', [status(esa)], [t12_xboole_1])).
% 11.09/11.27  thf('25', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 11.09/11.27      inference('sup-', [status(thm)], ['23', '24'])).
% 11.09/11.27  thf('26', plain,
% 11.09/11.27      (![X11 : $i, X12 : $i, X13 : $i]:
% 11.09/11.27         ((k2_xboole_0 @ X11 @ (k3_xboole_0 @ X12 @ X13))
% 11.09/11.27           = (k3_xboole_0 @ (k2_xboole_0 @ X11 @ X12) @ 
% 11.09/11.27              (k2_xboole_0 @ X11 @ X13)))),
% 11.09/11.27      inference('cnf', [status(esa)], [t24_xboole_1])).
% 11.09/11.27  thf('27', plain,
% 11.09/11.27      (![X0 : $i, X1 : $i]:
% 11.09/11.27         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 11.09/11.27           = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 11.09/11.27      inference('sup+', [status(thm)], ['25', '26'])).
% 11.09/11.27  thf(t22_xboole_1, axiom,
% 11.09/11.27    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 11.09/11.27  thf('28', plain,
% 11.09/11.27      (![X9 : $i, X10 : $i]:
% 11.09/11.27         ((k2_xboole_0 @ X9 @ (k3_xboole_0 @ X9 @ X10)) = (X9))),
% 11.09/11.27      inference('cnf', [status(esa)], [t22_xboole_1])).
% 11.09/11.27  thf('29', plain,
% 11.09/11.27      (![X0 : $i, X1 : $i]:
% 11.09/11.27         ((X0) = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 11.09/11.27      inference('demod', [status(thm)], ['27', '28'])).
% 11.09/11.27  thf('30', plain,
% 11.09/11.27      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.09/11.27         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X0 @ X1)))
% 11.09/11.27           = (X0))),
% 11.09/11.27      inference('demod', [status(thm)], ['20', '29'])).
% 11.09/11.27  thf('31', plain,
% 11.09/11.27      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 11.09/11.27      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 11.09/11.27  thf('32', plain,
% 11.09/11.27      (![X0 : $i, X1 : $i]:
% 11.09/11.27         ((X0)
% 11.09/11.27           = (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1)))),
% 11.09/11.27      inference('demod', [status(thm)], ['11', '30', '31'])).
% 11.09/11.27  thf('33', plain,
% 11.09/11.27      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 11.09/11.27      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 11.09/11.27  thf(t40_xboole_1, axiom,
% 11.09/11.27    (![A:$i,B:$i]:
% 11.09/11.27     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 11.09/11.27  thf('34', plain,
% 11.09/11.27      (![X21 : $i, X22 : $i]:
% 11.09/11.27         ((k4_xboole_0 @ (k2_xboole_0 @ X21 @ X22) @ X22)
% 11.09/11.27           = (k4_xboole_0 @ X21 @ X22))),
% 11.09/11.27      inference('cnf', [status(esa)], [t40_xboole_1])).
% 11.09/11.27  thf('35', plain,
% 11.09/11.27      (![X0 : $i, X1 : $i]:
% 11.09/11.27         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 11.09/11.27           = (k4_xboole_0 @ X0 @ X1))),
% 11.09/11.27      inference('sup+', [status(thm)], ['33', '34'])).
% 11.09/11.27  thf('36', plain,
% 11.09/11.27      (![X0 : $i, X1 : $i]:
% 11.09/11.27         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 11.09/11.27           = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X1 @ X0)))),
% 11.09/11.27      inference('sup+', [status(thm)], ['32', '35'])).
% 11.09/11.27  thf(t41_xboole_1, axiom,
% 11.09/11.27    (![A:$i,B:$i,C:$i]:
% 11.09/11.27     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 11.09/11.27       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 11.09/11.27  thf('37', plain,
% 11.09/11.27      (![X23 : $i, X24 : $i, X25 : $i]:
% 11.09/11.27         ((k4_xboole_0 @ (k4_xboole_0 @ X23 @ X24) @ X25)
% 11.09/11.27           = (k4_xboole_0 @ X23 @ (k2_xboole_0 @ X24 @ X25)))),
% 11.09/11.27      inference('cnf', [status(esa)], [t41_xboole_1])).
% 11.09/11.27  thf('38', plain,
% 11.09/11.27      (![X9 : $i, X10 : $i]:
% 11.09/11.27         ((k2_xboole_0 @ X9 @ (k3_xboole_0 @ X9 @ X10)) = (X9))),
% 11.09/11.27      inference('cnf', [status(esa)], [t22_xboole_1])).
% 11.09/11.27  thf('39', plain,
% 11.09/11.27      (![X0 : $i, X1 : $i]:
% 11.09/11.27         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 11.09/11.27           = (k4_xboole_0 @ X0 @ X1))),
% 11.09/11.27      inference('demod', [status(thm)], ['36', '37', '38'])).
% 11.09/11.27  thf('40', plain,
% 11.09/11.27      (((k4_xboole_0 @ sk_A @ sk_B) != (k4_xboole_0 @ sk_A @ sk_B))),
% 11.09/11.27      inference('demod', [status(thm)], ['2', '39'])).
% 11.09/11.27  thf('41', plain, ($false), inference('simplify', [status(thm)], ['40'])).
% 11.09/11.27  
% 11.09/11.27  % SZS output end Refutation
% 11.09/11.27  
% 11.09/11.28  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
