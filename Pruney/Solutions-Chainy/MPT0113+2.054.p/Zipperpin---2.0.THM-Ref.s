%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7vfk3qXWia

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:35 EST 2020

% Result     : Theorem 0.59s
% Output     : Refutation 0.59s
% Verified   : 
% Statistics : Number of formulae       :   46 (  59 expanded)
%              Number of leaves         :   15 (  22 expanded)
%              Depth                    :    8
%              Number of atoms          :  265 ( 385 expanded)
%              Number of equality atoms :   14 (  16 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t106_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) )
       => ( ( r1_tarski @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t106_xboole_1])).

thf('0',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_B )
    | ~ ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_B )
   <= ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('2',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X16 @ X17 ) @ X17 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('3',plain,(
    r1_tarski @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t63_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf('4',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ X13 @ X14 )
      | ~ ( r1_xboole_0 @ X14 @ X15 )
      | ( r1_xboole_0 @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_A @ X0 )
      | ~ ( r1_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    r1_xboole_0 @ sk_A @ sk_C ),
    inference('sup-',[status(thm)],['2','5'])).

thf('7',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ sk_C )
   <= ~ ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('8',plain,(
    r1_xboole_0 @ sk_A @ sk_C ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_B )
    | ~ ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('10',plain,(
    ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['8','9'])).

thf('11',plain,(
    ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['1','10'])).

thf('12',plain,(
    r1_tarski @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('13',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k3_xboole_0 @ X7 @ X8 )
        = X7 )
      | ~ ( r1_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('14',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) )
    = sk_A ),
    inference('sup-',[status(thm)],['12','13'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('16',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X9 @ X10 ) @ X9 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('17',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k3_xboole_0 @ X7 @ X8 )
        = X7 )
      | ~ ( r1_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf(t16_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C )
      = ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('21',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X4 @ X5 ) @ X6 )
      = ( k3_xboole_0 @ X4 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('23',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('24',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X9 @ X10 ) @ X9 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) @ X2 ) ),
    inference('sup+',[status(thm)],['22','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X1 ) ),
    inference('sup+',[status(thm)],['15','26'])).

thf('28',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference('sup+',[status(thm)],['14','27'])).

thf('29',plain,(
    $false ),
    inference(demod,[status(thm)],['11','28'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7vfk3qXWia
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:43:36 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  % Running portfolio for 600 s
% 0.14/0.36  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.59/0.77  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.59/0.77  % Solved by: fo/fo7.sh
% 0.59/0.77  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.59/0.77  % done 665 iterations in 0.303s
% 0.59/0.77  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.59/0.77  % SZS output start Refutation
% 0.59/0.77  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.59/0.77  thf(sk_B_type, type, sk_B: $i).
% 0.59/0.77  thf(sk_A_type, type, sk_A: $i).
% 0.59/0.77  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.59/0.77  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.59/0.77  thf(sk_C_type, type, sk_C: $i).
% 0.59/0.77  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.59/0.77  thf(t106_xboole_1, conjecture,
% 0.59/0.77    (![A:$i,B:$i,C:$i]:
% 0.59/0.77     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.59/0.77       ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ))).
% 0.59/0.77  thf(zf_stmt_0, negated_conjecture,
% 0.59/0.77    (~( ![A:$i,B:$i,C:$i]:
% 0.59/0.77        ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.59/0.77          ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) )),
% 0.59/0.77    inference('cnf.neg', [status(esa)], [t106_xboole_1])).
% 0.59/0.77  thf('0', plain,
% 0.59/0.77      ((~ (r1_tarski @ sk_A @ sk_B) | ~ (r1_xboole_0 @ sk_A @ sk_C))),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('1', plain,
% 0.59/0.77      ((~ (r1_tarski @ sk_A @ sk_B)) <= (~ ((r1_tarski @ sk_A @ sk_B)))),
% 0.59/0.77      inference('split', [status(esa)], ['0'])).
% 0.59/0.77  thf(t79_xboole_1, axiom,
% 0.59/0.77    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.59/0.77  thf('2', plain,
% 0.59/0.77      (![X16 : $i, X17 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X16 @ X17) @ X17)),
% 0.59/0.77      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.59/0.77  thf('3', plain, ((r1_tarski @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf(t63_xboole_1, axiom,
% 0.59/0.77    (![A:$i,B:$i,C:$i]:
% 0.59/0.77     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 0.59/0.77       ( r1_xboole_0 @ A @ C ) ))).
% 0.59/0.77  thf('4', plain,
% 0.59/0.77      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.59/0.77         (~ (r1_tarski @ X13 @ X14)
% 0.59/0.77          | ~ (r1_xboole_0 @ X14 @ X15)
% 0.59/0.77          | (r1_xboole_0 @ X13 @ X15))),
% 0.59/0.77      inference('cnf', [status(esa)], [t63_xboole_1])).
% 0.59/0.77  thf('5', plain,
% 0.59/0.77      (![X0 : $i]:
% 0.59/0.77         ((r1_xboole_0 @ sk_A @ X0)
% 0.59/0.77          | ~ (r1_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_C) @ X0))),
% 0.59/0.77      inference('sup-', [status(thm)], ['3', '4'])).
% 0.59/0.77  thf('6', plain, ((r1_xboole_0 @ sk_A @ sk_C)),
% 0.59/0.77      inference('sup-', [status(thm)], ['2', '5'])).
% 0.59/0.77  thf('7', plain,
% 0.59/0.77      ((~ (r1_xboole_0 @ sk_A @ sk_C)) <= (~ ((r1_xboole_0 @ sk_A @ sk_C)))),
% 0.59/0.77      inference('split', [status(esa)], ['0'])).
% 0.59/0.77  thf('8', plain, (((r1_xboole_0 @ sk_A @ sk_C))),
% 0.59/0.77      inference('sup-', [status(thm)], ['6', '7'])).
% 0.59/0.77  thf('9', plain,
% 0.59/0.77      (~ ((r1_tarski @ sk_A @ sk_B)) | ~ ((r1_xboole_0 @ sk_A @ sk_C))),
% 0.59/0.77      inference('split', [status(esa)], ['0'])).
% 0.59/0.77  thf('10', plain, (~ ((r1_tarski @ sk_A @ sk_B))),
% 0.59/0.77      inference('sat_resolution*', [status(thm)], ['8', '9'])).
% 0.59/0.77  thf('11', plain, (~ (r1_tarski @ sk_A @ sk_B)),
% 0.59/0.77      inference('simpl_trail', [status(thm)], ['1', '10'])).
% 0.59/0.77  thf('12', plain, ((r1_tarski @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf(t28_xboole_1, axiom,
% 0.59/0.77    (![A:$i,B:$i]:
% 0.59/0.77     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.59/0.77  thf('13', plain,
% 0.59/0.77      (![X7 : $i, X8 : $i]:
% 0.59/0.77         (((k3_xboole_0 @ X7 @ X8) = (X7)) | ~ (r1_tarski @ X7 @ X8))),
% 0.59/0.77      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.59/0.77  thf('14', plain,
% 0.59/0.77      (((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) = (sk_A))),
% 0.59/0.77      inference('sup-', [status(thm)], ['12', '13'])).
% 0.59/0.77  thf(commutativity_k3_xboole_0, axiom,
% 0.59/0.77    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.59/0.77  thf('15', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.59/0.77      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.59/0.77  thf(t36_xboole_1, axiom,
% 0.59/0.77    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.59/0.77  thf('16', plain,
% 0.59/0.77      (![X9 : $i, X10 : $i]: (r1_tarski @ (k4_xboole_0 @ X9 @ X10) @ X9)),
% 0.59/0.77      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.59/0.77  thf('17', plain,
% 0.59/0.77      (![X7 : $i, X8 : $i]:
% 0.59/0.77         (((k3_xboole_0 @ X7 @ X8) = (X7)) | ~ (r1_tarski @ X7 @ X8))),
% 0.59/0.77      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.59/0.77  thf('18', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i]:
% 0.59/0.77         ((k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0)
% 0.59/0.77           = (k4_xboole_0 @ X0 @ X1))),
% 0.59/0.77      inference('sup-', [status(thm)], ['16', '17'])).
% 0.59/0.77  thf('19', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.59/0.77      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.59/0.77  thf('20', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i]:
% 0.59/0.77         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.59/0.77           = (k4_xboole_0 @ X0 @ X1))),
% 0.59/0.77      inference('demod', [status(thm)], ['18', '19'])).
% 0.59/0.77  thf(t16_xboole_1, axiom,
% 0.59/0.77    (![A:$i,B:$i,C:$i]:
% 0.59/0.77     ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) =
% 0.59/0.77       ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 0.59/0.77  thf('21', plain,
% 0.59/0.77      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.59/0.77         ((k3_xboole_0 @ (k3_xboole_0 @ X4 @ X5) @ X6)
% 0.59/0.77           = (k3_xboole_0 @ X4 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.59/0.77      inference('cnf', [status(esa)], [t16_xboole_1])).
% 0.59/0.77  thf('22', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.77         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 0.59/0.77           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)))),
% 0.59/0.77      inference('sup+', [status(thm)], ['20', '21'])).
% 0.59/0.77  thf(t48_xboole_1, axiom,
% 0.59/0.77    (![A:$i,B:$i]:
% 0.59/0.77     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.59/0.77  thf('23', plain,
% 0.59/0.77      (![X11 : $i, X12 : $i]:
% 0.59/0.77         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 0.59/0.77           = (k3_xboole_0 @ X11 @ X12))),
% 0.59/0.77      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.59/0.77  thf('24', plain,
% 0.59/0.77      (![X9 : $i, X10 : $i]: (r1_tarski @ (k4_xboole_0 @ X9 @ X10) @ X9)),
% 0.59/0.77      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.59/0.77  thf('25', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 0.59/0.77      inference('sup+', [status(thm)], ['23', '24'])).
% 0.59/0.77  thf('26', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.77         (r1_tarski @ (k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0) @ X2)),
% 0.59/0.77      inference('sup+', [status(thm)], ['22', '25'])).
% 0.59/0.77  thf('27', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.77         (r1_tarski @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X1)),
% 0.59/0.77      inference('sup+', [status(thm)], ['15', '26'])).
% 0.59/0.77  thf('28', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.59/0.77      inference('sup+', [status(thm)], ['14', '27'])).
% 0.59/0.77  thf('29', plain, ($false), inference('demod', [status(thm)], ['11', '28'])).
% 0.59/0.77  
% 0.59/0.77  % SZS output end Refutation
% 0.59/0.77  
% 0.59/0.78  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
