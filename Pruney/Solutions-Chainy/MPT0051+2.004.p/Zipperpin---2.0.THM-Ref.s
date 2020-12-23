%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Ho5xGFNQHe

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:05 EST 2020

% Result     : Theorem 1.51s
% Output     : Refutation 1.51s
% Verified   : 
% Statistics : Number of formulae       :   44 (  59 expanded)
%              Number of leaves         :   12 (  24 expanded)
%              Depth                    :   12
%              Number of atoms          :  289 ( 411 expanded)
%              Number of equality atoms :   24 (  36 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t44_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
       => ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t44_xboole_1])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('2',plain,(
    ~ ( r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_C @ sk_B ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ X4 @ ( k4_xboole_0 @ X5 @ X4 ) )
      = ( k2_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('5',plain,(
    r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('6',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_xboole_0 @ X3 @ X2 )
        = X2 )
      | ~ ( r1_tarski @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('7',plain,
    ( ( k2_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_C )
    = sk_C ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('9',plain,
    ( ( k2_xboole_0 @ sk_C @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = sk_C ),
    inference(demod,[status(thm)],['7','8'])).

thf(t4_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C )
      = ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('10',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X6 @ X7 ) @ X8 )
      = ( k2_xboole_0 @ X6 @ ( k2_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('12',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ X9 @ ( k2_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_B ) @ ( k2_xboole_0 @ X0 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['9','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_B ) @ ( k2_xboole_0 @ sk_C @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','15'])).

thf('17',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_xboole_0 @ X3 @ X2 )
        = X2 )
      | ~ ( r1_tarski @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ ( k2_xboole_0 @ sk_C @ X0 ) )
      = ( k2_xboole_0 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X6 @ X7 ) @ X8 )
      = ( k2_xboole_0 @ X6 @ ( k2_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X2 @ X1 ) )
      = ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ sk_C @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ sk_A @ sk_B ) ) )
      = ( k2_xboole_0 @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['18','21'])).

thf('23',plain,
    ( ( k2_xboole_0 @ sk_C @ ( k2_xboole_0 @ sk_B @ sk_A ) )
    = ( k2_xboole_0 @ sk_C @ sk_B ) ),
    inference('sup+',[status(thm)],['3','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X2 @ X1 ) )
      = ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('27',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_C @ sk_B ) )
    = ( k2_xboole_0 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['23','24','25','26'])).

thf('28',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ X9 @ ( k2_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('29',plain,(
    r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_C @ sk_B ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    $false ),
    inference(demod,[status(thm)],['2','29'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Ho5xGFNQHe
% 0.13/0.35  % Computer   : n015.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:34:23 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 1.51/1.73  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.51/1.73  % Solved by: fo/fo7.sh
% 1.51/1.73  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.51/1.73  % done 1201 iterations in 1.265s
% 1.51/1.73  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.51/1.73  % SZS output start Refutation
% 1.51/1.73  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.51/1.73  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.51/1.73  thf(sk_C_type, type, sk_C: $i).
% 1.51/1.73  thf(sk_B_type, type, sk_B: $i).
% 1.51/1.73  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.51/1.73  thf(sk_A_type, type, sk_A: $i).
% 1.51/1.73  thf(t44_xboole_1, conjecture,
% 1.51/1.73    (![A:$i,B:$i,C:$i]:
% 1.51/1.73     ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) =>
% 1.51/1.73       ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 1.51/1.73  thf(zf_stmt_0, negated_conjecture,
% 1.51/1.73    (~( ![A:$i,B:$i,C:$i]:
% 1.51/1.73        ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) =>
% 1.51/1.73          ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ) )),
% 1.51/1.73    inference('cnf.neg', [status(esa)], [t44_xboole_1])).
% 1.51/1.73  thf('0', plain, (~ (r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))),
% 1.51/1.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.73  thf(commutativity_k2_xboole_0, axiom,
% 1.51/1.73    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 1.51/1.73  thf('1', plain,
% 1.51/1.73      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.51/1.73      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.51/1.73  thf('2', plain, (~ (r1_tarski @ sk_A @ (k2_xboole_0 @ sk_C @ sk_B))),
% 1.51/1.73      inference('demod', [status(thm)], ['0', '1'])).
% 1.51/1.73  thf(t39_xboole_1, axiom,
% 1.51/1.73    (![A:$i,B:$i]:
% 1.51/1.73     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 1.51/1.73  thf('3', plain,
% 1.51/1.73      (![X4 : $i, X5 : $i]:
% 1.51/1.73         ((k2_xboole_0 @ X4 @ (k4_xboole_0 @ X5 @ X4))
% 1.51/1.73           = (k2_xboole_0 @ X4 @ X5))),
% 1.51/1.73      inference('cnf', [status(esa)], [t39_xboole_1])).
% 1.51/1.73  thf('4', plain,
% 1.51/1.73      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.51/1.73      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.51/1.73  thf('5', plain, ((r1_tarski @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_C)),
% 1.51/1.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.73  thf(t12_xboole_1, axiom,
% 1.51/1.73    (![A:$i,B:$i]:
% 1.51/1.73     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 1.51/1.73  thf('6', plain,
% 1.51/1.73      (![X2 : $i, X3 : $i]:
% 1.51/1.73         (((k2_xboole_0 @ X3 @ X2) = (X2)) | ~ (r1_tarski @ X3 @ X2))),
% 1.51/1.73      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.51/1.73  thf('7', plain,
% 1.51/1.73      (((k2_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_C) = (sk_C))),
% 1.51/1.73      inference('sup-', [status(thm)], ['5', '6'])).
% 1.51/1.73  thf('8', plain,
% 1.51/1.73      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.51/1.73      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.51/1.73  thf('9', plain,
% 1.51/1.73      (((k2_xboole_0 @ sk_C @ (k4_xboole_0 @ sk_A @ sk_B)) = (sk_C))),
% 1.51/1.73      inference('demod', [status(thm)], ['7', '8'])).
% 1.51/1.73  thf(t4_xboole_1, axiom,
% 1.51/1.73    (![A:$i,B:$i,C:$i]:
% 1.51/1.73     ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 1.51/1.73       ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 1.51/1.73  thf('10', plain,
% 1.51/1.73      (![X6 : $i, X7 : $i, X8 : $i]:
% 1.51/1.73         ((k2_xboole_0 @ (k2_xboole_0 @ X6 @ X7) @ X8)
% 1.51/1.73           = (k2_xboole_0 @ X6 @ (k2_xboole_0 @ X7 @ X8)))),
% 1.51/1.73      inference('cnf', [status(esa)], [t4_xboole_1])).
% 1.51/1.73  thf('11', plain,
% 1.51/1.73      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.51/1.73      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.51/1.73  thf(t7_xboole_1, axiom,
% 1.51/1.73    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 1.51/1.73  thf('12', plain,
% 1.51/1.73      (![X9 : $i, X10 : $i]: (r1_tarski @ X9 @ (k2_xboole_0 @ X9 @ X10))),
% 1.51/1.73      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.51/1.73  thf('13', plain,
% 1.51/1.73      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 1.51/1.73      inference('sup+', [status(thm)], ['11', '12'])).
% 1.51/1.73  thf('14', plain,
% 1.51/1.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.51/1.73         (r1_tarski @ X0 @ (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.51/1.73      inference('sup+', [status(thm)], ['10', '13'])).
% 1.51/1.73  thf('15', plain,
% 1.51/1.73      (![X0 : $i]:
% 1.51/1.73         (r1_tarski @ (k4_xboole_0 @ sk_A @ sk_B) @ (k2_xboole_0 @ X0 @ sk_C))),
% 1.51/1.73      inference('sup+', [status(thm)], ['9', '14'])).
% 1.51/1.73  thf('16', plain,
% 1.51/1.73      (![X0 : $i]:
% 1.51/1.73         (r1_tarski @ (k4_xboole_0 @ sk_A @ sk_B) @ (k2_xboole_0 @ sk_C @ X0))),
% 1.51/1.73      inference('sup+', [status(thm)], ['4', '15'])).
% 1.51/1.73  thf('17', plain,
% 1.51/1.73      (![X2 : $i, X3 : $i]:
% 1.51/1.73         (((k2_xboole_0 @ X3 @ X2) = (X2)) | ~ (r1_tarski @ X3 @ X2))),
% 1.51/1.73      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.51/1.73  thf('18', plain,
% 1.51/1.73      (![X0 : $i]:
% 1.51/1.73         ((k2_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ 
% 1.51/1.73           (k2_xboole_0 @ sk_C @ X0)) = (k2_xboole_0 @ sk_C @ X0))),
% 1.51/1.73      inference('sup-', [status(thm)], ['16', '17'])).
% 1.51/1.73  thf('19', plain,
% 1.51/1.73      (![X6 : $i, X7 : $i, X8 : $i]:
% 1.51/1.73         ((k2_xboole_0 @ (k2_xboole_0 @ X6 @ X7) @ X8)
% 1.51/1.73           = (k2_xboole_0 @ X6 @ (k2_xboole_0 @ X7 @ X8)))),
% 1.51/1.73      inference('cnf', [status(esa)], [t4_xboole_1])).
% 1.51/1.73  thf('20', plain,
% 1.51/1.73      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.51/1.73      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.51/1.73  thf('21', plain,
% 1.51/1.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.51/1.73         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X2 @ X1))
% 1.51/1.73           = (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.51/1.73      inference('sup+', [status(thm)], ['19', '20'])).
% 1.51/1.73  thf('22', plain,
% 1.51/1.73      (![X0 : $i]:
% 1.51/1.73         ((k2_xboole_0 @ sk_C @ 
% 1.51/1.73           (k2_xboole_0 @ X0 @ (k4_xboole_0 @ sk_A @ sk_B)))
% 1.51/1.73           = (k2_xboole_0 @ sk_C @ X0))),
% 1.51/1.73      inference('demod', [status(thm)], ['18', '21'])).
% 1.51/1.73  thf('23', plain,
% 1.51/1.73      (((k2_xboole_0 @ sk_C @ (k2_xboole_0 @ sk_B @ sk_A))
% 1.51/1.73         = (k2_xboole_0 @ sk_C @ sk_B))),
% 1.51/1.73      inference('sup+', [status(thm)], ['3', '22'])).
% 1.51/1.73  thf('24', plain,
% 1.51/1.73      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.51/1.73      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.51/1.73  thf('25', plain,
% 1.51/1.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.51/1.73         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X2 @ X1))
% 1.51/1.73           = (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.51/1.73      inference('sup+', [status(thm)], ['19', '20'])).
% 1.51/1.73  thf('26', plain,
% 1.51/1.73      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.51/1.73      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.51/1.73  thf('27', plain,
% 1.51/1.73      (((k2_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_C @ sk_B))
% 1.51/1.73         = (k2_xboole_0 @ sk_C @ sk_B))),
% 1.51/1.73      inference('demod', [status(thm)], ['23', '24', '25', '26'])).
% 1.51/1.73  thf('28', plain,
% 1.51/1.73      (![X9 : $i, X10 : $i]: (r1_tarski @ X9 @ (k2_xboole_0 @ X9 @ X10))),
% 1.51/1.73      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.51/1.73  thf('29', plain, ((r1_tarski @ sk_A @ (k2_xboole_0 @ sk_C @ sk_B))),
% 1.51/1.73      inference('sup+', [status(thm)], ['27', '28'])).
% 1.51/1.73  thf('30', plain, ($false), inference('demod', [status(thm)], ['2', '29'])).
% 1.51/1.73  
% 1.51/1.73  % SZS output end Refutation
% 1.51/1.73  
% 1.51/1.74  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
