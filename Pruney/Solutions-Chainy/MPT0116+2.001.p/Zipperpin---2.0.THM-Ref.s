%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.W8zVWkqUDE

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:45 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   51 (  60 expanded)
%              Number of leaves         :   19 (  26 expanded)
%              Depth                    :   11
%              Number of atoms          :  280 ( 351 expanded)
%              Number of equality atoms :   27 (  31 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(t109_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ C ) @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_tarski @ A @ B )
       => ( r1_tarski @ ( k4_xboole_0 @ A @ C ) @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t109_xboole_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_C_1 ) @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('2',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ X15 @ X16 )
      | ( r1_tarski @ X15 @ ( k2_xboole_0 @ X17 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_A @ ( k2_xboole_0 @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('4',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k3_xboole_0 @ X20 @ X21 )
        = X20 )
      | ~ ( r1_tarski @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ X0 @ sk_B_1 ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('6',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k3_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ X0 @ sk_B_1 ) )
      = ( k5_xboole_0 @ sk_A @ sk_A ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    r1_tarski @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k3_xboole_0 @ X20 @ X21 )
        = X20 )
      | ~ ( r1_tarski @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('10',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B_1 )
    = sk_A ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k3_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('12',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B_1 )
    = ( k5_xboole_0 @ sk_A @ sk_A ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ X0 @ sk_B_1 ) )
      = ( k4_xboole_0 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['7','12'])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('14',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k4_xboole_0 @ X24 @ ( k2_xboole_0 @ X24 @ X25 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('15',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B_1 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['13','14'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('16',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k2_xboole_0 @ X27 @ X28 )
      = ( k5_xboole_0 @ X27 @ ( k4_xboole_0 @ X28 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('17',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ sk_A )
    = ( k5_xboole_0 @ sk_B_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('19',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X5 @ X4 )
      = ( k5_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('20',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X5 @ X4 )
      = ( k5_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('21',plain,(
    ! [X26: $i] :
      ( ( k5_xboole_0 @ X26 @ k1_xboole_0 )
      = X26 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B_1 )
    = sk_B_1 ),
    inference(demod,[status(thm)],['17','18','19','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('25',plain,(
    ! [X22: $i,X23: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X22 @ X23 ) @ X22 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('26',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ X15 @ X16 )
      | ( r1_tarski @ X15 @ ( k2_xboole_0 @ X17 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X1 @ X2 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['24','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_A @ X0 ) @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['23','28'])).

thf('30',plain,(
    $false ),
    inference(demod,[status(thm)],['0','29'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.W8zVWkqUDE
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:02:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.20/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.54  % Solved by: fo/fo7.sh
% 0.20/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.54  % done 346 iterations in 0.097s
% 0.20/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.54  % SZS output start Refutation
% 0.20/0.54  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.54  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.54  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.54  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.20/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.54  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.54  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.20/0.54  thf(t109_xboole_1, conjecture,
% 0.20/0.54    (![A:$i,B:$i,C:$i]:
% 0.20/0.54     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ ( k4_xboole_0 @ A @ C ) @ B ) ))).
% 0.20/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.54    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.54        ( ( r1_tarski @ A @ B ) => ( r1_tarski @ ( k4_xboole_0 @ A @ C ) @ B ) ) )),
% 0.20/0.54    inference('cnf.neg', [status(esa)], [t109_xboole_1])).
% 0.20/0.54  thf('0', plain, (~ (r1_tarski @ (k4_xboole_0 @ sk_A @ sk_C_1) @ sk_B_1)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('1', plain, ((r1_tarski @ sk_A @ sk_B_1)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf(t10_xboole_1, axiom,
% 0.20/0.54    (![A:$i,B:$i,C:$i]:
% 0.20/0.54     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 0.20/0.54  thf('2', plain,
% 0.20/0.54      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.20/0.54         (~ (r1_tarski @ X15 @ X16)
% 0.20/0.54          | (r1_tarski @ X15 @ (k2_xboole_0 @ X17 @ X16)))),
% 0.20/0.54      inference('cnf', [status(esa)], [t10_xboole_1])).
% 0.20/0.54  thf('3', plain,
% 0.20/0.54      (![X0 : $i]: (r1_tarski @ sk_A @ (k2_xboole_0 @ X0 @ sk_B_1))),
% 0.20/0.54      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.54  thf(t28_xboole_1, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.20/0.54  thf('4', plain,
% 0.20/0.54      (![X20 : $i, X21 : $i]:
% 0.20/0.54         (((k3_xboole_0 @ X20 @ X21) = (X20)) | ~ (r1_tarski @ X20 @ X21))),
% 0.20/0.54      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.20/0.54  thf('5', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         ((k3_xboole_0 @ sk_A @ (k2_xboole_0 @ X0 @ sk_B_1)) = (sk_A))),
% 0.20/0.54      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.54  thf(t100_xboole_1, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.20/0.54  thf('6', plain,
% 0.20/0.54      (![X13 : $i, X14 : $i]:
% 0.20/0.54         ((k4_xboole_0 @ X13 @ X14)
% 0.20/0.54           = (k5_xboole_0 @ X13 @ (k3_xboole_0 @ X13 @ X14)))),
% 0.20/0.54      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.20/0.54  thf('7', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         ((k4_xboole_0 @ sk_A @ (k2_xboole_0 @ X0 @ sk_B_1))
% 0.20/0.54           = (k5_xboole_0 @ sk_A @ sk_A))),
% 0.20/0.54      inference('sup+', [status(thm)], ['5', '6'])).
% 0.20/0.54  thf('8', plain, ((r1_tarski @ sk_A @ sk_B_1)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('9', plain,
% 0.20/0.54      (![X20 : $i, X21 : $i]:
% 0.20/0.54         (((k3_xboole_0 @ X20 @ X21) = (X20)) | ~ (r1_tarski @ X20 @ X21))),
% 0.20/0.54      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.20/0.54  thf('10', plain, (((k3_xboole_0 @ sk_A @ sk_B_1) = (sk_A))),
% 0.20/0.54      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.54  thf('11', plain,
% 0.20/0.54      (![X13 : $i, X14 : $i]:
% 0.20/0.54         ((k4_xboole_0 @ X13 @ X14)
% 0.20/0.54           = (k5_xboole_0 @ X13 @ (k3_xboole_0 @ X13 @ X14)))),
% 0.20/0.54      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.20/0.54  thf('12', plain,
% 0.20/0.54      (((k4_xboole_0 @ sk_A @ sk_B_1) = (k5_xboole_0 @ sk_A @ sk_A))),
% 0.20/0.54      inference('sup+', [status(thm)], ['10', '11'])).
% 0.20/0.54  thf('13', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         ((k4_xboole_0 @ sk_A @ (k2_xboole_0 @ X0 @ sk_B_1))
% 0.20/0.54           = (k4_xboole_0 @ sk_A @ sk_B_1))),
% 0.20/0.54      inference('demod', [status(thm)], ['7', '12'])).
% 0.20/0.54  thf(t46_xboole_1, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.20/0.54  thf('14', plain,
% 0.20/0.54      (![X24 : $i, X25 : $i]:
% 0.20/0.54         ((k4_xboole_0 @ X24 @ (k2_xboole_0 @ X24 @ X25)) = (k1_xboole_0))),
% 0.20/0.54      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.20/0.54  thf('15', plain, (((k4_xboole_0 @ sk_A @ sk_B_1) = (k1_xboole_0))),
% 0.20/0.54      inference('sup+', [status(thm)], ['13', '14'])).
% 0.20/0.54  thf(t98_xboole_1, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.20/0.54  thf('16', plain,
% 0.20/0.54      (![X27 : $i, X28 : $i]:
% 0.20/0.54         ((k2_xboole_0 @ X27 @ X28)
% 0.20/0.54           = (k5_xboole_0 @ X27 @ (k4_xboole_0 @ X28 @ X27)))),
% 0.20/0.54      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.20/0.54  thf('17', plain,
% 0.20/0.54      (((k2_xboole_0 @ sk_B_1 @ sk_A) = (k5_xboole_0 @ sk_B_1 @ k1_xboole_0))),
% 0.20/0.54      inference('sup+', [status(thm)], ['15', '16'])).
% 0.20/0.54  thf(commutativity_k2_xboole_0, axiom,
% 0.20/0.54    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.20/0.54  thf('18', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.20/0.54      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.20/0.54  thf(commutativity_k5_xboole_0, axiom,
% 0.20/0.54    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.20/0.54  thf('19', plain,
% 0.20/0.54      (![X4 : $i, X5 : $i]: ((k5_xboole_0 @ X5 @ X4) = (k5_xboole_0 @ X4 @ X5))),
% 0.20/0.54      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.20/0.54  thf('20', plain,
% 0.20/0.54      (![X4 : $i, X5 : $i]: ((k5_xboole_0 @ X5 @ X4) = (k5_xboole_0 @ X4 @ X5))),
% 0.20/0.54      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.20/0.54  thf(t5_boole, axiom,
% 0.20/0.54    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.20/0.54  thf('21', plain, (![X26 : $i]: ((k5_xboole_0 @ X26 @ k1_xboole_0) = (X26))),
% 0.20/0.54      inference('cnf', [status(esa)], [t5_boole])).
% 0.20/0.54  thf('22', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.20/0.54      inference('sup+', [status(thm)], ['20', '21'])).
% 0.20/0.54  thf('23', plain, (((k2_xboole_0 @ sk_A @ sk_B_1) = (sk_B_1))),
% 0.20/0.54      inference('demod', [status(thm)], ['17', '18', '19', '22'])).
% 0.20/0.54  thf('24', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.20/0.54      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.20/0.54  thf(t36_xboole_1, axiom,
% 0.20/0.54    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.20/0.54  thf('25', plain,
% 0.20/0.54      (![X22 : $i, X23 : $i]: (r1_tarski @ (k4_xboole_0 @ X22 @ X23) @ X22)),
% 0.20/0.54      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.20/0.54  thf('26', plain,
% 0.20/0.54      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.20/0.54         (~ (r1_tarski @ X15 @ X16)
% 0.20/0.54          | (r1_tarski @ X15 @ (k2_xboole_0 @ X17 @ X16)))),
% 0.20/0.54      inference('cnf', [status(esa)], [t10_xboole_1])).
% 0.20/0.54  thf('27', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.54         (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X2 @ X0))),
% 0.20/0.54      inference('sup-', [status(thm)], ['25', '26'])).
% 0.20/0.54  thf('28', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.54         (r1_tarski @ (k4_xboole_0 @ X1 @ X2) @ (k2_xboole_0 @ X1 @ X0))),
% 0.20/0.54      inference('sup+', [status(thm)], ['24', '27'])).
% 0.20/0.54  thf('29', plain,
% 0.20/0.54      (![X0 : $i]: (r1_tarski @ (k4_xboole_0 @ sk_A @ X0) @ sk_B_1)),
% 0.20/0.54      inference('sup+', [status(thm)], ['23', '28'])).
% 0.20/0.54  thf('30', plain, ($false), inference('demod', [status(thm)], ['0', '29'])).
% 0.20/0.54  
% 0.20/0.54  % SZS output end Refutation
% 0.20/0.54  
% 0.20/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
