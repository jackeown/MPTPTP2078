%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.w2V8e9ySn6

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:47 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 114 expanded)
%              Number of leaves         :   19 (  44 expanded)
%              Depth                    :   14
%              Number of atoms          :  440 ( 753 expanded)
%              Number of equality atoms :   52 (  83 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(t110_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k5_xboole_0 @ A @ C ) @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( r1_tarski @ A @ B )
          & ( r1_tarski @ C @ B ) )
       => ( r1_tarski @ ( k5_xboole_0 @ A @ C ) @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t110_xboole_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k5_xboole_0 @ sk_A @ sk_C ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('2',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_xboole_0 @ X6 @ X7 )
        = X6 )
      | ~ ( r1_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('3',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('5',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_A ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('6',plain,(
    ! [X12: $i] :
      ( ( k5_xboole_0 @ X12 @ X12 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('7',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    r1_tarski @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_xboole_0 @ X6 @ X7 )
        = X6 )
      | ~ ( r1_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('10',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_B )
    = sk_C ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('12',plain,
    ( ( k4_xboole_0 @ sk_C @ sk_B )
    = ( k5_xboole_0 @ sk_C @ sk_C ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X12: $i] :
      ( ( k5_xboole_0 @ X12 @ X12 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('14',plain,
    ( ( k4_xboole_0 @ sk_C @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['12','13'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('15',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('16',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_C )
    = ( k5_xboole_0 @ sk_B @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('18',plain,(
    ! [X9: $i] :
      ( ( k5_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('19',plain,
    ( ( k2_xboole_0 @ sk_C @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['16','17','18'])).

thf(t99_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) @ ( k4_xboole_0 @ B @ ( k2_xboole_0 @ A @ C ) ) ) ) )).

thf('20',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ X15 @ X16 ) @ X17 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X15 @ ( k2_xboole_0 @ X16 @ X17 ) ) @ ( k4_xboole_0 @ X16 @ ( k2_xboole_0 @ X15 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[t99_xboole_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ X0 @ sk_C ) @ sk_B )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_B ) @ ( k4_xboole_0 @ sk_C @ ( k2_xboole_0 @ X0 @ sk_B ) ) ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( k4_xboole_0 @ ( k5_xboole_0 @ sk_A @ sk_C ) @ sk_B )
    = ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_C @ ( k2_xboole_0 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['7','21'])).

thf('23',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['5','6'])).

thf('24',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('25',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = ( k5_xboole_0 @ sk_B @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('27',plain,(
    ! [X9: $i] :
      ( ( k5_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('28',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('29',plain,
    ( ( k4_xboole_0 @ sk_C @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['12','13'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('30',plain,(
    ! [X8: $i] :
      ( r1_tarski @ k1_xboole_0 @ X8 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('31',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_xboole_0 @ X6 @ X7 )
        = X6 )
      | ~ ( r1_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X9: $i] :
      ( ( k5_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X9: $i] :
      ( ( k5_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( k4_xboole_0 @ ( k5_xboole_0 @ sk_A @ sk_C ) @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['22','28','29','42'])).

thf('44',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('45',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_A @ sk_C ) )
    = ( k5_xboole_0 @ sk_B @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X9: $i] :
      ( ( k5_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('47',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_A @ sk_C ) )
    = sk_B ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('49',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_tarski @ X10 @ ( k2_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    r1_tarski @ ( k5_xboole_0 @ sk_A @ sk_C ) @ sk_B ),
    inference('sup+',[status(thm)],['47','50'])).

thf('52',plain,(
    $false ),
    inference(demod,[status(thm)],['0','51'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.w2V8e9ySn6
% 0.14/0.35  % Computer   : n009.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:24:26 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.21/0.35  % Number of cores: 8
% 0.21/0.35  % Python version: Python 3.6.8
% 0.21/0.35  % Running in FO mode
% 0.46/0.64  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.46/0.64  % Solved by: fo/fo7.sh
% 0.46/0.64  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.64  % done 324 iterations in 0.187s
% 0.46/0.64  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.46/0.64  % SZS output start Refutation
% 0.46/0.64  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.46/0.64  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.64  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.64  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.46/0.64  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.46/0.64  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.64  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.46/0.64  thf(sk_C_type, type, sk_C: $i).
% 0.46/0.64  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.46/0.64  thf(t110_xboole_1, conjecture,
% 0.46/0.64    (![A:$i,B:$i,C:$i]:
% 0.46/0.64     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 0.46/0.64       ( r1_tarski @ ( k5_xboole_0 @ A @ C ) @ B ) ))).
% 0.46/0.64  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.64    (~( ![A:$i,B:$i,C:$i]:
% 0.46/0.64        ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 0.46/0.64          ( r1_tarski @ ( k5_xboole_0 @ A @ C ) @ B ) ) )),
% 0.46/0.64    inference('cnf.neg', [status(esa)], [t110_xboole_1])).
% 0.46/0.64  thf('0', plain, (~ (r1_tarski @ (k5_xboole_0 @ sk_A @ sk_C) @ sk_B)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('1', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf(t28_xboole_1, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.46/0.64  thf('2', plain,
% 0.46/0.64      (![X6 : $i, X7 : $i]:
% 0.46/0.64         (((k3_xboole_0 @ X6 @ X7) = (X6)) | ~ (r1_tarski @ X6 @ X7))),
% 0.46/0.64      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.46/0.64  thf('3', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 0.46/0.64      inference('sup-', [status(thm)], ['1', '2'])).
% 0.46/0.64  thf(t100_xboole_1, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.46/0.64  thf('4', plain,
% 0.46/0.64      (![X4 : $i, X5 : $i]:
% 0.46/0.64         ((k4_xboole_0 @ X4 @ X5)
% 0.46/0.64           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 0.46/0.64      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.46/0.64  thf('5', plain,
% 0.46/0.64      (((k4_xboole_0 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_A))),
% 0.46/0.64      inference('sup+', [status(thm)], ['3', '4'])).
% 0.46/0.64  thf(t92_xboole_1, axiom,
% 0.46/0.64    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.46/0.64  thf('6', plain, (![X12 : $i]: ((k5_xboole_0 @ X12 @ X12) = (k1_xboole_0))),
% 0.46/0.64      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.46/0.64  thf('7', plain, (((k4_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.46/0.64      inference('demod', [status(thm)], ['5', '6'])).
% 0.46/0.64  thf('8', plain, ((r1_tarski @ sk_C @ sk_B)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('9', plain,
% 0.46/0.64      (![X6 : $i, X7 : $i]:
% 0.46/0.64         (((k3_xboole_0 @ X6 @ X7) = (X6)) | ~ (r1_tarski @ X6 @ X7))),
% 0.46/0.64      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.46/0.64  thf('10', plain, (((k3_xboole_0 @ sk_C @ sk_B) = (sk_C))),
% 0.46/0.64      inference('sup-', [status(thm)], ['8', '9'])).
% 0.46/0.64  thf('11', plain,
% 0.46/0.64      (![X4 : $i, X5 : $i]:
% 0.46/0.64         ((k4_xboole_0 @ X4 @ X5)
% 0.46/0.64           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 0.46/0.64      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.46/0.64  thf('12', plain,
% 0.46/0.64      (((k4_xboole_0 @ sk_C @ sk_B) = (k5_xboole_0 @ sk_C @ sk_C))),
% 0.46/0.64      inference('sup+', [status(thm)], ['10', '11'])).
% 0.46/0.64  thf('13', plain, (![X12 : $i]: ((k5_xboole_0 @ X12 @ X12) = (k1_xboole_0))),
% 0.46/0.64      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.46/0.64  thf('14', plain, (((k4_xboole_0 @ sk_C @ sk_B) = (k1_xboole_0))),
% 0.46/0.64      inference('demod', [status(thm)], ['12', '13'])).
% 0.46/0.64  thf(t98_xboole_1, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.46/0.64  thf('15', plain,
% 0.46/0.64      (![X13 : $i, X14 : $i]:
% 0.46/0.64         ((k2_xboole_0 @ X13 @ X14)
% 0.46/0.64           = (k5_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X13)))),
% 0.46/0.64      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.46/0.64  thf('16', plain,
% 0.46/0.64      (((k2_xboole_0 @ sk_B @ sk_C) = (k5_xboole_0 @ sk_B @ k1_xboole_0))),
% 0.46/0.64      inference('sup+', [status(thm)], ['14', '15'])).
% 0.46/0.64  thf(commutativity_k2_xboole_0, axiom,
% 0.46/0.64    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.46/0.64  thf('17', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.46/0.64      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.46/0.64  thf(t5_boole, axiom,
% 0.46/0.64    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.46/0.64  thf('18', plain, (![X9 : $i]: ((k5_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 0.46/0.64      inference('cnf', [status(esa)], [t5_boole])).
% 0.46/0.64  thf('19', plain, (((k2_xboole_0 @ sk_C @ sk_B) = (sk_B))),
% 0.46/0.64      inference('demod', [status(thm)], ['16', '17', '18'])).
% 0.46/0.64  thf(t99_xboole_1, axiom,
% 0.46/0.64    (![A:$i,B:$i,C:$i]:
% 0.46/0.64     ( ( k4_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.46/0.64       ( k2_xboole_0 @
% 0.46/0.64         ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) @ 
% 0.46/0.64         ( k4_xboole_0 @ B @ ( k2_xboole_0 @ A @ C ) ) ) ))).
% 0.46/0.64  thf('20', plain,
% 0.46/0.64      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.46/0.64         ((k4_xboole_0 @ (k5_xboole_0 @ X15 @ X16) @ X17)
% 0.46/0.64           = (k2_xboole_0 @ (k4_xboole_0 @ X15 @ (k2_xboole_0 @ X16 @ X17)) @ 
% 0.46/0.64              (k4_xboole_0 @ X16 @ (k2_xboole_0 @ X15 @ X17))))),
% 0.46/0.64      inference('cnf', [status(esa)], [t99_xboole_1])).
% 0.46/0.64  thf('21', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         ((k4_xboole_0 @ (k5_xboole_0 @ X0 @ sk_C) @ sk_B)
% 0.46/0.64           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ sk_B) @ 
% 0.46/0.64              (k4_xboole_0 @ sk_C @ (k2_xboole_0 @ X0 @ sk_B))))),
% 0.46/0.64      inference('sup+', [status(thm)], ['19', '20'])).
% 0.46/0.64  thf('22', plain,
% 0.46/0.64      (((k4_xboole_0 @ (k5_xboole_0 @ sk_A @ sk_C) @ sk_B)
% 0.46/0.64         = (k2_xboole_0 @ k1_xboole_0 @ 
% 0.46/0.64            (k4_xboole_0 @ sk_C @ (k2_xboole_0 @ sk_A @ sk_B))))),
% 0.46/0.64      inference('sup+', [status(thm)], ['7', '21'])).
% 0.46/0.64  thf('23', plain, (((k4_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.46/0.64      inference('demod', [status(thm)], ['5', '6'])).
% 0.46/0.64  thf('24', plain,
% 0.46/0.64      (![X13 : $i, X14 : $i]:
% 0.46/0.64         ((k2_xboole_0 @ X13 @ X14)
% 0.46/0.64           = (k5_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X13)))),
% 0.46/0.64      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.46/0.64  thf('25', plain,
% 0.46/0.64      (((k2_xboole_0 @ sk_B @ sk_A) = (k5_xboole_0 @ sk_B @ k1_xboole_0))),
% 0.46/0.64      inference('sup+', [status(thm)], ['23', '24'])).
% 0.46/0.64  thf('26', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.46/0.64      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.46/0.64  thf('27', plain, (![X9 : $i]: ((k5_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 0.46/0.64      inference('cnf', [status(esa)], [t5_boole])).
% 0.46/0.64  thf('28', plain, (((k2_xboole_0 @ sk_A @ sk_B) = (sk_B))),
% 0.46/0.64      inference('demod', [status(thm)], ['25', '26', '27'])).
% 0.46/0.64  thf('29', plain, (((k4_xboole_0 @ sk_C @ sk_B) = (k1_xboole_0))),
% 0.46/0.64      inference('demod', [status(thm)], ['12', '13'])).
% 0.46/0.64  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.46/0.64  thf('30', plain, (![X8 : $i]: (r1_tarski @ k1_xboole_0 @ X8)),
% 0.46/0.64      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.46/0.64  thf('31', plain,
% 0.46/0.64      (![X6 : $i, X7 : $i]:
% 0.46/0.64         (((k3_xboole_0 @ X6 @ X7) = (X6)) | ~ (r1_tarski @ X6 @ X7))),
% 0.46/0.64      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.46/0.64  thf('32', plain,
% 0.46/0.64      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.46/0.64      inference('sup-', [status(thm)], ['30', '31'])).
% 0.46/0.64  thf('33', plain,
% 0.46/0.64      (![X4 : $i, X5 : $i]:
% 0.46/0.64         ((k4_xboole_0 @ X4 @ X5)
% 0.46/0.64           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 0.46/0.64      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.46/0.64  thf('34', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 0.46/0.64           = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.46/0.64      inference('sup+', [status(thm)], ['32', '33'])).
% 0.46/0.64  thf('35', plain, (![X9 : $i]: ((k5_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 0.46/0.64      inference('cnf', [status(esa)], [t5_boole])).
% 0.46/0.64  thf('36', plain,
% 0.46/0.64      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.46/0.64      inference('demod', [status(thm)], ['34', '35'])).
% 0.46/0.64  thf('37', plain,
% 0.46/0.64      (![X13 : $i, X14 : $i]:
% 0.46/0.64         ((k2_xboole_0 @ X13 @ X14)
% 0.46/0.64           = (k5_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X13)))),
% 0.46/0.64      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.46/0.64  thf('38', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.46/0.64      inference('sup+', [status(thm)], ['36', '37'])).
% 0.46/0.64  thf('39', plain, (![X9 : $i]: ((k5_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 0.46/0.64      inference('cnf', [status(esa)], [t5_boole])).
% 0.46/0.64  thf('40', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.46/0.64      inference('demod', [status(thm)], ['38', '39'])).
% 0.46/0.64  thf('41', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.46/0.64      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.46/0.64  thf('42', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.46/0.64      inference('sup+', [status(thm)], ['40', '41'])).
% 0.46/0.64  thf('43', plain,
% 0.46/0.64      (((k4_xboole_0 @ (k5_xboole_0 @ sk_A @ sk_C) @ sk_B) = (k1_xboole_0))),
% 0.46/0.64      inference('demod', [status(thm)], ['22', '28', '29', '42'])).
% 0.46/0.64  thf('44', plain,
% 0.46/0.64      (![X13 : $i, X14 : $i]:
% 0.46/0.64         ((k2_xboole_0 @ X13 @ X14)
% 0.46/0.64           = (k5_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X13)))),
% 0.46/0.64      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.46/0.64  thf('45', plain,
% 0.46/0.64      (((k2_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_A @ sk_C))
% 0.46/0.64         = (k5_xboole_0 @ sk_B @ k1_xboole_0))),
% 0.46/0.64      inference('sup+', [status(thm)], ['43', '44'])).
% 0.46/0.64  thf('46', plain, (![X9 : $i]: ((k5_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 0.46/0.64      inference('cnf', [status(esa)], [t5_boole])).
% 0.46/0.64  thf('47', plain,
% 0.46/0.64      (((k2_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_A @ sk_C)) = (sk_B))),
% 0.46/0.64      inference('demod', [status(thm)], ['45', '46'])).
% 0.46/0.64  thf('48', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.46/0.64      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.46/0.64  thf(t7_xboole_1, axiom,
% 0.46/0.64    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.46/0.64  thf('49', plain,
% 0.46/0.64      (![X10 : $i, X11 : $i]: (r1_tarski @ X10 @ (k2_xboole_0 @ X10 @ X11))),
% 0.46/0.64      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.46/0.64  thf('50', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.46/0.64      inference('sup+', [status(thm)], ['48', '49'])).
% 0.46/0.64  thf('51', plain, ((r1_tarski @ (k5_xboole_0 @ sk_A @ sk_C) @ sk_B)),
% 0.46/0.64      inference('sup+', [status(thm)], ['47', '50'])).
% 0.46/0.64  thf('52', plain, ($false), inference('demod', [status(thm)], ['0', '51'])).
% 0.46/0.64  
% 0.46/0.64  % SZS output end Refutation
% 0.46/0.64  
% 0.52/0.65  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
