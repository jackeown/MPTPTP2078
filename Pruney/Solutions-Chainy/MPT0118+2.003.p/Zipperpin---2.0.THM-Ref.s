%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.j6LMWKooEV

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:50 EST 2020

% Result     : Theorem 6.43s
% Output     : Refutation 6.43s
% Verified   : 
% Statistics : Number of formulae       :   46 (  69 expanded)
%              Number of leaves         :   14 (  29 expanded)
%              Depth                    :    8
%              Number of atoms          :  415 ( 640 expanded)
%              Number of equality atoms :   36 (  57 expanded)
%              Maximal formula depth    :   11 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t111_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ B ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ A @ C ) @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ B ) )
        = ( k3_xboole_0 @ ( k4_xboole_0 @ A @ C ) @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t111_xboole_1])).

thf('0',plain,(
    ( k4_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B ) @ ( k3_xboole_0 @ sk_C @ sk_B ) )
 != ( k3_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_C ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('4',plain,(
    ( k4_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ ( k3_xboole_0 @ sk_B @ sk_C ) )
 != ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['0','1','2','3'])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('5',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k3_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X13 @ X14 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('6',plain,(
    ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) )
 != ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('7',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X7 @ X8 ) @ X7 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('8',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_xboole_0 @ X11 @ X12 )
        = X11 )
      | ~ ( r1_tarski @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t16_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C )
      = ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('10',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X4 @ X5 ) @ X6 )
      = ( k3_xboole_0 @ X4 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X4 @ X5 ) @ X6 )
      = ( k3_xboole_0 @ X4 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('13',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k3_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X13 @ X14 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X2 ) )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X2 ) ) ) ) ),
    inference('sup+',[status(thm)],['11','16'])).

thf('18',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k3_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X13 @ X14 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('19',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X4 @ X5 ) @ X6 )
      = ( k3_xboole_0 @ X4 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ) ),
    inference(demod,[status(thm)],['17','18','19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('23',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k3_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X13 @ X14 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X2 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k3_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X13 @ X14 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('26',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k3_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X13 @ X14 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X2 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ) ),
    inference(demod,[status(thm)],['21','27'])).

thf('29',plain,(
    ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_C ) )
 != ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['6','28'])).

thf('30',plain,(
    $false ),
    inference(simplify,[status(thm)],['29'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.j6LMWKooEV
% 0.13/0.33  % Computer   : n011.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 18:31:57 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running portfolio for 600 s
% 0.13/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.33  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 6.43/6.61  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 6.43/6.61  % Solved by: fo/fo7.sh
% 6.43/6.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 6.43/6.61  % done 2063 iterations in 6.168s
% 6.43/6.61  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 6.43/6.61  % SZS output start Refutation
% 6.43/6.61  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 6.43/6.61  thf(sk_A_type, type, sk_A: $i).
% 6.43/6.61  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 6.43/6.61  thf(sk_B_type, type, sk_B: $i).
% 6.43/6.61  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 6.43/6.61  thf(sk_C_type, type, sk_C: $i).
% 6.43/6.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 6.43/6.61  thf(t111_xboole_1, conjecture,
% 6.43/6.61    (![A:$i,B:$i,C:$i]:
% 6.43/6.61     ( ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ B ) ) =
% 6.43/6.61       ( k3_xboole_0 @ ( k4_xboole_0 @ A @ C ) @ B ) ))).
% 6.43/6.61  thf(zf_stmt_0, negated_conjecture,
% 6.43/6.61    (~( ![A:$i,B:$i,C:$i]:
% 6.43/6.61        ( ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ B ) ) =
% 6.43/6.61          ( k3_xboole_0 @ ( k4_xboole_0 @ A @ C ) @ B ) ) )),
% 6.43/6.61    inference('cnf.neg', [status(esa)], [t111_xboole_1])).
% 6.43/6.61  thf('0', plain,
% 6.43/6.61      (((k4_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B) @ 
% 6.43/6.61         (k3_xboole_0 @ sk_C @ sk_B))
% 6.43/6.61         != (k3_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_C) @ sk_B))),
% 6.43/6.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.43/6.61  thf(commutativity_k3_xboole_0, axiom,
% 6.43/6.61    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 6.43/6.61  thf('1', plain,
% 6.43/6.61      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 6.43/6.61      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 6.43/6.61  thf('2', plain,
% 6.43/6.61      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 6.43/6.61      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 6.43/6.61  thf('3', plain,
% 6.43/6.61      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 6.43/6.61      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 6.43/6.61  thf('4', plain,
% 6.43/6.61      (((k4_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ 
% 6.43/6.61         (k3_xboole_0 @ sk_B @ sk_C))
% 6.43/6.61         != (k3_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_C)))),
% 6.43/6.61      inference('demod', [status(thm)], ['0', '1', '2', '3'])).
% 6.43/6.61  thf(t49_xboole_1, axiom,
% 6.43/6.61    (![A:$i,B:$i,C:$i]:
% 6.43/6.61     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 6.43/6.61       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 6.43/6.61  thf('5', plain,
% 6.43/6.61      (![X13 : $i, X14 : $i, X15 : $i]:
% 6.43/6.61         ((k3_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X15))
% 6.43/6.61           = (k4_xboole_0 @ (k3_xboole_0 @ X13 @ X14) @ X15))),
% 6.43/6.61      inference('cnf', [status(esa)], [t49_xboole_1])).
% 6.43/6.61  thf('6', plain,
% 6.43/6.61      (((k3_xboole_0 @ sk_B @ 
% 6.43/6.61         (k4_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)))
% 6.43/6.61         != (k3_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_C)))),
% 6.43/6.61      inference('demod', [status(thm)], ['4', '5'])).
% 6.43/6.61  thf(t17_xboole_1, axiom,
% 6.43/6.61    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 6.43/6.61  thf('7', plain,
% 6.43/6.61      (![X7 : $i, X8 : $i]: (r1_tarski @ (k3_xboole_0 @ X7 @ X8) @ X7)),
% 6.43/6.61      inference('cnf', [status(esa)], [t17_xboole_1])).
% 6.43/6.61  thf(t28_xboole_1, axiom,
% 6.43/6.61    (![A:$i,B:$i]:
% 6.43/6.61     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 6.43/6.61  thf('8', plain,
% 6.43/6.61      (![X11 : $i, X12 : $i]:
% 6.43/6.61         (((k3_xboole_0 @ X11 @ X12) = (X11)) | ~ (r1_tarski @ X11 @ X12))),
% 6.43/6.61      inference('cnf', [status(esa)], [t28_xboole_1])).
% 6.43/6.61  thf('9', plain,
% 6.43/6.61      (![X0 : $i, X1 : $i]:
% 6.43/6.61         ((k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0)
% 6.43/6.61           = (k3_xboole_0 @ X0 @ X1))),
% 6.43/6.61      inference('sup-', [status(thm)], ['7', '8'])).
% 6.43/6.61  thf(t16_xboole_1, axiom,
% 6.43/6.61    (![A:$i,B:$i,C:$i]:
% 6.43/6.61     ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) =
% 6.43/6.61       ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 6.43/6.61  thf('10', plain,
% 6.43/6.61      (![X4 : $i, X5 : $i, X6 : $i]:
% 6.43/6.61         ((k3_xboole_0 @ (k3_xboole_0 @ X4 @ X5) @ X6)
% 6.43/6.61           = (k3_xboole_0 @ X4 @ (k3_xboole_0 @ X5 @ X6)))),
% 6.43/6.61      inference('cnf', [status(esa)], [t16_xboole_1])).
% 6.43/6.61  thf('11', plain,
% 6.43/6.61      (![X0 : $i, X1 : $i]:
% 6.43/6.61         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 6.43/6.61           = (k3_xboole_0 @ X0 @ X1))),
% 6.43/6.61      inference('demod', [status(thm)], ['9', '10'])).
% 6.43/6.61  thf('12', plain,
% 6.43/6.61      (![X4 : $i, X5 : $i, X6 : $i]:
% 6.43/6.61         ((k3_xboole_0 @ (k3_xboole_0 @ X4 @ X5) @ X6)
% 6.43/6.61           = (k3_xboole_0 @ X4 @ (k3_xboole_0 @ X5 @ X6)))),
% 6.43/6.61      inference('cnf', [status(esa)], [t16_xboole_1])).
% 6.43/6.61  thf(t100_xboole_1, axiom,
% 6.43/6.61    (![A:$i,B:$i]:
% 6.43/6.61     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 6.43/6.61  thf('13', plain,
% 6.43/6.61      (![X2 : $i, X3 : $i]:
% 6.43/6.61         ((k4_xboole_0 @ X2 @ X3)
% 6.43/6.61           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 6.43/6.61      inference('cnf', [status(esa)], [t100_xboole_1])).
% 6.43/6.61  thf('14', plain,
% 6.43/6.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.43/6.61         ((k4_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0)
% 6.43/6.61           = (k5_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ 
% 6.43/6.61              (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0))))),
% 6.43/6.61      inference('sup+', [status(thm)], ['12', '13'])).
% 6.43/6.61  thf('15', plain,
% 6.43/6.61      (![X13 : $i, X14 : $i, X15 : $i]:
% 6.43/6.61         ((k3_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X15))
% 6.43/6.61           = (k4_xboole_0 @ (k3_xboole_0 @ X13 @ X14) @ X15))),
% 6.43/6.61      inference('cnf', [status(esa)], [t49_xboole_1])).
% 6.43/6.61  thf('16', plain,
% 6.43/6.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.43/6.61         ((k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0))
% 6.43/6.61           = (k5_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ 
% 6.43/6.61              (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0))))),
% 6.43/6.61      inference('demod', [status(thm)], ['14', '15'])).
% 6.43/6.61  thf('17', plain,
% 6.43/6.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.43/6.61         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X2))
% 6.43/6.61           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ 
% 6.43/6.61              (k3_xboole_0 @ X1 @ (k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X2))))),
% 6.43/6.61      inference('sup+', [status(thm)], ['11', '16'])).
% 6.43/6.61  thf('18', plain,
% 6.43/6.61      (![X13 : $i, X14 : $i, X15 : $i]:
% 6.43/6.61         ((k3_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X15))
% 6.43/6.61           = (k4_xboole_0 @ (k3_xboole_0 @ X13 @ X14) @ X15))),
% 6.43/6.61      inference('cnf', [status(esa)], [t49_xboole_1])).
% 6.43/6.61  thf('19', plain,
% 6.43/6.61      (![X4 : $i, X5 : $i, X6 : $i]:
% 6.43/6.61         ((k3_xboole_0 @ (k3_xboole_0 @ X4 @ X5) @ X6)
% 6.43/6.61           = (k3_xboole_0 @ X4 @ (k3_xboole_0 @ X5 @ X6)))),
% 6.43/6.61      inference('cnf', [status(esa)], [t16_xboole_1])).
% 6.43/6.61  thf('20', plain,
% 6.43/6.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.43/6.61         ((k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0))
% 6.43/6.61           = (k5_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ 
% 6.43/6.61              (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0))))),
% 6.43/6.61      inference('demod', [status(thm)], ['14', '15'])).
% 6.43/6.61  thf('21', plain,
% 6.43/6.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.43/6.61         ((k3_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X2)))
% 6.43/6.61           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X2))))),
% 6.43/6.61      inference('demod', [status(thm)], ['17', '18', '19', '20'])).
% 6.43/6.61  thf('22', plain,
% 6.43/6.61      (![X0 : $i, X1 : $i]:
% 6.43/6.61         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 6.43/6.61           = (k3_xboole_0 @ X0 @ X1))),
% 6.43/6.61      inference('demod', [status(thm)], ['9', '10'])).
% 6.43/6.61  thf('23', plain,
% 6.43/6.61      (![X13 : $i, X14 : $i, X15 : $i]:
% 6.43/6.61         ((k3_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X15))
% 6.43/6.61           = (k4_xboole_0 @ (k3_xboole_0 @ X13 @ X14) @ X15))),
% 6.43/6.61      inference('cnf', [status(esa)], [t49_xboole_1])).
% 6.43/6.61  thf('24', plain,
% 6.43/6.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.43/6.61         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X2))
% 6.43/6.61           = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2))),
% 6.43/6.61      inference('sup+', [status(thm)], ['22', '23'])).
% 6.43/6.61  thf('25', plain,
% 6.43/6.61      (![X13 : $i, X14 : $i, X15 : $i]:
% 6.43/6.61         ((k3_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X15))
% 6.43/6.61           = (k4_xboole_0 @ (k3_xboole_0 @ X13 @ X14) @ X15))),
% 6.43/6.61      inference('cnf', [status(esa)], [t49_xboole_1])).
% 6.43/6.61  thf('26', plain,
% 6.43/6.61      (![X13 : $i, X14 : $i, X15 : $i]:
% 6.43/6.61         ((k3_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X15))
% 6.43/6.61           = (k4_xboole_0 @ (k3_xboole_0 @ X13 @ X14) @ X15))),
% 6.43/6.61      inference('cnf', [status(esa)], [t49_xboole_1])).
% 6.43/6.61  thf('27', plain,
% 6.43/6.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.43/6.61         ((k3_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X2)))
% 6.43/6.61           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X2)))),
% 6.43/6.61      inference('demod', [status(thm)], ['24', '25', '26'])).
% 6.43/6.61  thf('28', plain,
% 6.43/6.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.43/6.61         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X2))
% 6.43/6.61           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X2))))),
% 6.43/6.61      inference('demod', [status(thm)], ['21', '27'])).
% 6.43/6.61  thf('29', plain,
% 6.43/6.61      (((k3_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_C))
% 6.43/6.61         != (k3_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_C)))),
% 6.43/6.61      inference('demod', [status(thm)], ['6', '28'])).
% 6.43/6.61  thf('30', plain, ($false), inference('simplify', [status(thm)], ['29'])).
% 6.43/6.61  
% 6.43/6.61  % SZS output end Refutation
% 6.43/6.61  
% 6.43/6.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
