%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.mKnn0QMFLo

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:12 EST 2020

% Result     : Theorem 22.48s
% Output     : Refutation 22.48s
% Verified   : 
% Statistics : Number of formulae       :   58 (  78 expanded)
%              Number of leaves         :   16 (  30 expanded)
%              Depth                    :   12
%              Number of atoms          :  474 ( 638 expanded)
%              Number of equality atoms :   49 (  67 expanded)
%              Maximal formula depth    :   10 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

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
    ! [X15: $i,X16: $i] :
      ( ( k2_xboole_0 @ X15 @ ( k4_xboole_0 @ X16 @ X15 ) )
      = ( k2_xboole_0 @ X15 @ X16 ) ) ),
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
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k2_xboole_0 @ X8 @ ( k3_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X8 @ X9 ) @ ( k2_xboole_0 @ X8 @ X10 ) ) ) ),
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
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X13 @ X14 ) @ X13 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('13',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_xboole_0 @ X5 @ X4 )
        = X4 )
      | ~ ( r1_tarski @ X5 @ X4 ) ) ),
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
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k2_xboole_0 @ X8 @ ( k3_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X8 @ X9 ) @ ( k2_xboole_0 @ X8 @ X10 ) ) ) ),
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

thf('21',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_xboole_0 @ X15 @ ( k4_xboole_0 @ X16 @ X15 ) )
      = ( k2_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k2_xboole_0 @ X8 @ ( k3_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X8 @ X9 ) @ ( k2_xboole_0 @ X8 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t24_xboole_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = A ) )).

thf('26',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) )
      = X6 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) )
      = X0 ) ),
    inference(demod,[status(thm)],['20','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['11','28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('32',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X17 @ X18 ) @ X18 )
      = ( k4_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['30','33'])).

thf('35',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) )
      = X6 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('36',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X19 @ X20 ) @ X21 )
      = ( k4_xboole_0 @ X19 @ ( k2_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['34','37'])).

thf('39',plain,(
    ( k4_xboole_0 @ sk_A @ sk_B )
 != ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['2','38'])).

thf('40',plain,(
    $false ),
    inference(simplify,[status(thm)],['39'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.mKnn0QMFLo
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:56:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 22.48/22.66  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 22.48/22.66  % Solved by: fo/fo7.sh
% 22.48/22.66  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 22.48/22.66  % done 12082 iterations in 22.193s
% 22.48/22.66  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 22.48/22.66  % SZS output start Refutation
% 22.48/22.66  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 22.48/22.66  thf(sk_A_type, type, sk_A: $i).
% 22.48/22.66  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 22.48/22.66  thf(sk_B_type, type, sk_B: $i).
% 22.48/22.66  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 22.48/22.66  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 22.48/22.66  thf(t47_xboole_1, conjecture,
% 22.48/22.66    (![A:$i,B:$i]:
% 22.48/22.66     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 22.48/22.66  thf(zf_stmt_0, negated_conjecture,
% 22.48/22.66    (~( ![A:$i,B:$i]:
% 22.48/22.66        ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) =
% 22.48/22.66          ( k4_xboole_0 @ A @ B ) ) )),
% 22.48/22.66    inference('cnf.neg', [status(esa)], [t47_xboole_1])).
% 22.48/22.66  thf('0', plain,
% 22.48/22.66      (((k4_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_A @ sk_B))
% 22.48/22.66         != (k4_xboole_0 @ sk_A @ sk_B))),
% 22.48/22.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.48/22.66  thf(commutativity_k3_xboole_0, axiom,
% 22.48/22.66    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 22.48/22.66  thf('1', plain,
% 22.48/22.66      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 22.48/22.66      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 22.48/22.66  thf('2', plain,
% 22.48/22.66      (((k4_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_A))
% 22.48/22.66         != (k4_xboole_0 @ sk_A @ sk_B))),
% 22.48/22.66      inference('demod', [status(thm)], ['0', '1'])).
% 22.48/22.66  thf(t39_xboole_1, axiom,
% 22.48/22.66    (![A:$i,B:$i]:
% 22.48/22.66     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 22.48/22.66  thf('3', plain,
% 22.48/22.66      (![X15 : $i, X16 : $i]:
% 22.48/22.66         ((k2_xboole_0 @ X15 @ (k4_xboole_0 @ X16 @ X15))
% 22.48/22.66           = (k2_xboole_0 @ X15 @ X16))),
% 22.48/22.66      inference('cnf', [status(esa)], [t39_xboole_1])).
% 22.48/22.66  thf(commutativity_k2_xboole_0, axiom,
% 22.48/22.66    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 22.48/22.66  thf('4', plain,
% 22.48/22.66      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 22.48/22.66      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 22.48/22.66  thf(t24_xboole_1, axiom,
% 22.48/22.66    (![A:$i,B:$i,C:$i]:
% 22.48/22.66     ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) =
% 22.48/22.66       ( k3_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ C ) ) ))).
% 22.48/22.66  thf('5', plain,
% 22.48/22.66      (![X8 : $i, X9 : $i, X10 : $i]:
% 22.48/22.66         ((k2_xboole_0 @ X8 @ (k3_xboole_0 @ X9 @ X10))
% 22.48/22.66           = (k3_xboole_0 @ (k2_xboole_0 @ X8 @ X9) @ (k2_xboole_0 @ X8 @ X10)))),
% 22.48/22.66      inference('cnf', [status(esa)], [t24_xboole_1])).
% 22.48/22.66  thf('6', plain,
% 22.48/22.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 22.48/22.66         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X2))
% 22.48/22.66           = (k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X0 @ X2)))),
% 22.48/22.66      inference('sup+', [status(thm)], ['4', '5'])).
% 22.48/22.66  thf('7', plain,
% 22.48/22.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 22.48/22.66         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X1 @ X2))
% 22.48/22.66           = (k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ 
% 22.48/22.66              (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X2)))),
% 22.48/22.66      inference('sup+', [status(thm)], ['3', '6'])).
% 22.48/22.66  thf('8', plain,
% 22.48/22.66      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 22.48/22.66      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 22.48/22.66  thf('9', plain,
% 22.48/22.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 22.48/22.66         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X2))
% 22.48/22.66           = (k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X0 @ X2)))),
% 22.48/22.66      inference('sup+', [status(thm)], ['4', '5'])).
% 22.48/22.66  thf('10', plain,
% 22.48/22.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 22.48/22.66         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ X1))
% 22.48/22.66           = (k3_xboole_0 @ (k2_xboole_0 @ X2 @ X0) @ (k2_xboole_0 @ X1 @ X0)))),
% 22.48/22.66      inference('sup+', [status(thm)], ['8', '9'])).
% 22.48/22.66  thf('11', plain,
% 22.48/22.66      (![X0 : $i, X1 : $i]:
% 22.48/22.66         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1)))
% 22.48/22.66           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X1 @ X0)))),
% 22.48/22.66      inference('sup+', [status(thm)], ['7', '10'])).
% 22.48/22.66  thf(t36_xboole_1, axiom,
% 22.48/22.66    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 22.48/22.66  thf('12', plain,
% 22.48/22.66      (![X13 : $i, X14 : $i]: (r1_tarski @ (k4_xboole_0 @ X13 @ X14) @ X13)),
% 22.48/22.66      inference('cnf', [status(esa)], [t36_xboole_1])).
% 22.48/22.66  thf(t12_xboole_1, axiom,
% 22.48/22.66    (![A:$i,B:$i]:
% 22.48/22.66     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 22.48/22.66  thf('13', plain,
% 22.48/22.66      (![X4 : $i, X5 : $i]:
% 22.48/22.66         (((k2_xboole_0 @ X5 @ X4) = (X4)) | ~ (r1_tarski @ X5 @ X4))),
% 22.48/22.66      inference('cnf', [status(esa)], [t12_xboole_1])).
% 22.48/22.66  thf('14', plain,
% 22.48/22.66      (![X0 : $i, X1 : $i]:
% 22.48/22.66         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 22.48/22.66      inference('sup-', [status(thm)], ['12', '13'])).
% 22.48/22.66  thf('15', plain,
% 22.48/22.66      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 22.48/22.66      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 22.48/22.66  thf('16', plain,
% 22.48/22.66      (![X0 : $i, X1 : $i]:
% 22.48/22.66         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)) = (X0))),
% 22.48/22.66      inference('demod', [status(thm)], ['14', '15'])).
% 22.48/22.66  thf('17', plain,
% 22.48/22.66      (![X8 : $i, X9 : $i, X10 : $i]:
% 22.48/22.66         ((k2_xboole_0 @ X8 @ (k3_xboole_0 @ X9 @ X10))
% 22.48/22.66           = (k3_xboole_0 @ (k2_xboole_0 @ X8 @ X9) @ (k2_xboole_0 @ X8 @ X10)))),
% 22.48/22.66      inference('cnf', [status(esa)], [t24_xboole_1])).
% 22.48/22.66  thf('18', plain,
% 22.48/22.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 22.48/22.66         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X0 @ X1)))
% 22.48/22.66           = (k3_xboole_0 @ (k2_xboole_0 @ X0 @ X2) @ X0))),
% 22.48/22.66      inference('sup+', [status(thm)], ['16', '17'])).
% 22.48/22.66  thf('19', plain,
% 22.48/22.66      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 22.48/22.66      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 22.48/22.66  thf('20', plain,
% 22.48/22.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 22.48/22.66         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X0 @ X1)))
% 22.48/22.66           = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X2)))),
% 22.48/22.66      inference('demod', [status(thm)], ['18', '19'])).
% 22.48/22.66  thf('21', plain,
% 22.48/22.66      (![X15 : $i, X16 : $i]:
% 22.48/22.66         ((k2_xboole_0 @ X15 @ (k4_xboole_0 @ X16 @ X15))
% 22.48/22.66           = (k2_xboole_0 @ X15 @ X16))),
% 22.48/22.66      inference('cnf', [status(esa)], [t39_xboole_1])).
% 22.48/22.66  thf('22', plain,
% 22.48/22.66      (![X0 : $i, X1 : $i]:
% 22.48/22.66         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)) = (X0))),
% 22.48/22.66      inference('demod', [status(thm)], ['14', '15'])).
% 22.48/22.66  thf('23', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 22.48/22.66      inference('sup+', [status(thm)], ['21', '22'])).
% 22.48/22.66  thf('24', plain,
% 22.48/22.66      (![X8 : $i, X9 : $i, X10 : $i]:
% 22.48/22.66         ((k2_xboole_0 @ X8 @ (k3_xboole_0 @ X9 @ X10))
% 22.48/22.66           = (k3_xboole_0 @ (k2_xboole_0 @ X8 @ X9) @ (k2_xboole_0 @ X8 @ X10)))),
% 22.48/22.66      inference('cnf', [status(esa)], [t24_xboole_1])).
% 22.48/22.66  thf('25', plain,
% 22.48/22.66      (![X0 : $i, X1 : $i]:
% 22.48/22.66         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 22.48/22.66           = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 22.48/22.66      inference('sup+', [status(thm)], ['23', '24'])).
% 22.48/22.66  thf(t22_xboole_1, axiom,
% 22.48/22.66    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 22.48/22.66  thf('26', plain,
% 22.48/22.66      (![X6 : $i, X7 : $i]:
% 22.48/22.66         ((k2_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)) = (X6))),
% 22.48/22.66      inference('cnf', [status(esa)], [t22_xboole_1])).
% 22.48/22.66  thf('27', plain,
% 22.48/22.66      (![X0 : $i, X1 : $i]:
% 22.48/22.66         ((X0) = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 22.48/22.66      inference('demod', [status(thm)], ['25', '26'])).
% 22.48/22.66  thf('28', plain,
% 22.48/22.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 22.48/22.66         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X0 @ X1)))
% 22.48/22.66           = (X0))),
% 22.48/22.66      inference('demod', [status(thm)], ['20', '27'])).
% 22.48/22.66  thf('29', plain,
% 22.48/22.66      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 22.48/22.66      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 22.48/22.66  thf('30', plain,
% 22.48/22.66      (![X0 : $i, X1 : $i]:
% 22.48/22.66         ((X0)
% 22.48/22.66           = (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1)))),
% 22.48/22.66      inference('demod', [status(thm)], ['11', '28', '29'])).
% 22.48/22.66  thf('31', plain,
% 22.48/22.66      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 22.48/22.66      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 22.48/22.66  thf(t40_xboole_1, axiom,
% 22.48/22.66    (![A:$i,B:$i]:
% 22.48/22.66     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 22.48/22.66  thf('32', plain,
% 22.48/22.66      (![X17 : $i, X18 : $i]:
% 22.48/22.66         ((k4_xboole_0 @ (k2_xboole_0 @ X17 @ X18) @ X18)
% 22.48/22.66           = (k4_xboole_0 @ X17 @ X18))),
% 22.48/22.66      inference('cnf', [status(esa)], [t40_xboole_1])).
% 22.48/22.66  thf('33', plain,
% 22.48/22.66      (![X0 : $i, X1 : $i]:
% 22.48/22.66         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 22.48/22.66           = (k4_xboole_0 @ X0 @ X1))),
% 22.48/22.66      inference('sup+', [status(thm)], ['31', '32'])).
% 22.48/22.66  thf('34', plain,
% 22.48/22.66      (![X0 : $i, X1 : $i]:
% 22.48/22.66         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 22.48/22.66           = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X1 @ X0)))),
% 22.48/22.66      inference('sup+', [status(thm)], ['30', '33'])).
% 22.48/22.66  thf('35', plain,
% 22.48/22.66      (![X6 : $i, X7 : $i]:
% 22.48/22.66         ((k2_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)) = (X6))),
% 22.48/22.66      inference('cnf', [status(esa)], [t22_xboole_1])).
% 22.48/22.66  thf(t41_xboole_1, axiom,
% 22.48/22.66    (![A:$i,B:$i,C:$i]:
% 22.48/22.66     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 22.48/22.66       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 22.48/22.66  thf('36', plain,
% 22.48/22.66      (![X19 : $i, X20 : $i, X21 : $i]:
% 22.48/22.66         ((k4_xboole_0 @ (k4_xboole_0 @ X19 @ X20) @ X21)
% 22.48/22.66           = (k4_xboole_0 @ X19 @ (k2_xboole_0 @ X20 @ X21)))),
% 22.48/22.66      inference('cnf', [status(esa)], [t41_xboole_1])).
% 22.48/22.66  thf('37', plain,
% 22.48/22.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 22.48/22.66         ((k4_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ (k3_xboole_0 @ X0 @ X1))
% 22.48/22.66           = (k4_xboole_0 @ X2 @ X0))),
% 22.48/22.66      inference('sup+', [status(thm)], ['35', '36'])).
% 22.48/22.66  thf('38', plain,
% 22.48/22.66      (![X0 : $i, X1 : $i]:
% 22.48/22.66         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 22.48/22.66           = (k4_xboole_0 @ X0 @ X1))),
% 22.48/22.66      inference('demod', [status(thm)], ['34', '37'])).
% 22.48/22.66  thf('39', plain,
% 22.48/22.66      (((k4_xboole_0 @ sk_A @ sk_B) != (k4_xboole_0 @ sk_A @ sk_B))),
% 22.48/22.66      inference('demod', [status(thm)], ['2', '38'])).
% 22.48/22.66  thf('40', plain, ($false), inference('simplify', [status(thm)], ['39'])).
% 22.48/22.66  
% 22.48/22.66  % SZS output end Refutation
% 22.48/22.66  
% 22.48/22.67  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
