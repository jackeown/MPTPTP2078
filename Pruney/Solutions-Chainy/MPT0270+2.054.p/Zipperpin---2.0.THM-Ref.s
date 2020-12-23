%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CnFpTcsDih

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:18 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 137 expanded)
%              Number of leaves         :   19 (  44 expanded)
%              Depth                    :   16
%              Number of atoms          :  445 (1102 expanded)
%              Number of equality atoms :   34 (  90 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(t67_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = ( k1_tarski @ A ) )
    <=> ~ ( r2_hidden @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
          = ( k1_tarski @ A ) )
      <=> ~ ( r2_hidden @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t67_zfmisc_1])).

thf('0',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('3',plain,(
    ! [X2: $i] :
      ( ( k3_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('4',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X9 @ X10 ) @ X9 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('6',plain,(
    ! [X16: $i] :
      ( ( k2_tarski @ X16 @ X16 )
      = ( k1_tarski @ X16 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('7',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ( r2_hidden @ X46 @ X47 )
      | ~ ( r1_tarski @ ( k2_tarski @ X46 @ X48 ) @ X47 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('11',plain,(
    ! [X13: $i,X15: $i] :
      ( ( r1_xboole_0 @ X13 @ X15 )
      | ( ( k4_xboole_0 @ X13 @ X15 )
       != X13 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('12',plain,
    ( ( ( ( k1_tarski @ sk_A )
       != ( k1_tarski @ sk_A ) )
      | ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['14'])).

thf('16',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['14'])).

thf('17',plain,(
    ! [X46: $i,X48: $i,X49: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X46 @ X48 ) @ X49 )
      | ~ ( r2_hidden @ X48 @ X49 )
      | ~ ( r2_hidden @ X46 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('18',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ sk_B )
        | ( r1_tarski @ ( k2_tarski @ X0 @ sk_A ) @ sk_B ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( r1_tarski @ ( k2_tarski @ sk_A @ sk_A ) @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X16: $i] :
      ( ( k2_tarski @ X16 @ X16 )
      = ( k1_tarski @ X16 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('21',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['19','20'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('22',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_xboole_0 @ X11 @ X12 )
        = X11 )
      | ~ ( r1_tarski @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('23',plain,
    ( ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('25',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
      = ( k1_tarski @ sk_A ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('27',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ ( k3_xboole_0 @ X3 @ X6 ) )
      | ~ ( r1_xboole_0 @ X3 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
        | ~ ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['25','28'])).

thf('30',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
        = ( k1_tarski @ sk_A ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['13','29'])).

thf('31',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != ( k1_tarski @ sk_A ) )
    | ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['9','30'])).

thf('32',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['2','31'])).

thf('33',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['1','32'])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('34',plain,(
    ! [X44: $i,X45: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X44 ) @ X45 )
      | ( r2_hidden @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf('35',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k4_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
        = ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != ( k1_tarski @ sk_A ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['14'])).

thf('38',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['14'])).

thf('39',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['2','31','38'])).

thf('40',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['37','39'])).

thf('41',plain,
    ( ( ( k1_tarski @ sk_A )
     != ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['36','40'])).

thf('42',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    $false ),
    inference(demod,[status(thm)],['33','42'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CnFpTcsDih
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:47:48 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.37/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.37/0.55  % Solved by: fo/fo7.sh
% 0.37/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.55  % done 183 iterations in 0.082s
% 0.37/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.37/0.55  % SZS output start Refutation
% 0.37/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.37/0.55  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.37/0.55  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.37/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.55  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.37/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.55  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.37/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.55  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.37/0.55  thf(t67_zfmisc_1, conjecture,
% 0.37/0.55    (![A:$i,B:$i]:
% 0.37/0.55     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) <=>
% 0.37/0.55       ( ~( r2_hidden @ A @ B ) ) ))).
% 0.37/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.55    (~( ![A:$i,B:$i]:
% 0.37/0.55        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) <=>
% 0.37/0.55          ( ~( r2_hidden @ A @ B ) ) ) )),
% 0.37/0.55    inference('cnf.neg', [status(esa)], [t67_zfmisc_1])).
% 0.37/0.55  thf('0', plain,
% 0.37/0.55      ((~ (r2_hidden @ sk_A @ sk_B)
% 0.37/0.55        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A)))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('1', plain,
% 0.37/0.55      ((~ (r2_hidden @ sk_A @ sk_B)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.37/0.55      inference('split', [status(esa)], ['0'])).
% 0.37/0.55  thf('2', plain,
% 0.37/0.55      (~ ((r2_hidden @ sk_A @ sk_B)) | 
% 0.37/0.55       (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A)))),
% 0.37/0.55      inference('split', [status(esa)], ['0'])).
% 0.37/0.55  thf(idempotence_k3_xboole_0, axiom,
% 0.37/0.55    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.37/0.55  thf('3', plain, (![X2 : $i]: ((k3_xboole_0 @ X2 @ X2) = (X2))),
% 0.37/0.55      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.37/0.55  thf(t17_xboole_1, axiom,
% 0.37/0.55    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.37/0.55  thf('4', plain,
% 0.37/0.55      (![X9 : $i, X10 : $i]: (r1_tarski @ (k3_xboole_0 @ X9 @ X10) @ X9)),
% 0.37/0.55      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.37/0.55  thf('5', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.37/0.55      inference('sup+', [status(thm)], ['3', '4'])).
% 0.37/0.55  thf(t69_enumset1, axiom,
% 0.37/0.55    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.37/0.55  thf('6', plain, (![X16 : $i]: ((k2_tarski @ X16 @ X16) = (k1_tarski @ X16))),
% 0.37/0.55      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.37/0.55  thf(t38_zfmisc_1, axiom,
% 0.37/0.55    (![A:$i,B:$i,C:$i]:
% 0.37/0.55     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.37/0.55       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.37/0.55  thf('7', plain,
% 0.37/0.55      (![X46 : $i, X47 : $i, X48 : $i]:
% 0.37/0.55         ((r2_hidden @ X46 @ X47)
% 0.37/0.55          | ~ (r1_tarski @ (k2_tarski @ X46 @ X48) @ X47))),
% 0.37/0.55      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.37/0.55  thf('8', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i]:
% 0.37/0.55         (~ (r1_tarski @ (k1_tarski @ X0) @ X1) | (r2_hidden @ X0 @ X1))),
% 0.37/0.55      inference('sup-', [status(thm)], ['6', '7'])).
% 0.37/0.55  thf('9', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.37/0.55      inference('sup-', [status(thm)], ['5', '8'])).
% 0.37/0.55  thf('10', plain,
% 0.37/0.55      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A)))
% 0.37/0.55         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))))),
% 0.37/0.55      inference('split', [status(esa)], ['0'])).
% 0.37/0.55  thf(t83_xboole_1, axiom,
% 0.37/0.55    (![A:$i,B:$i]:
% 0.37/0.55     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.37/0.55  thf('11', plain,
% 0.37/0.55      (![X13 : $i, X15 : $i]:
% 0.37/0.55         ((r1_xboole_0 @ X13 @ X15) | ((k4_xboole_0 @ X13 @ X15) != (X13)))),
% 0.37/0.55      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.37/0.55  thf('12', plain,
% 0.37/0.55      (((((k1_tarski @ sk_A) != (k1_tarski @ sk_A))
% 0.37/0.55         | (r1_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)))
% 0.37/0.55         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))))),
% 0.37/0.55      inference('sup-', [status(thm)], ['10', '11'])).
% 0.37/0.55  thf('13', plain,
% 0.37/0.55      (((r1_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))
% 0.37/0.55         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))))),
% 0.37/0.55      inference('simplify', [status(thm)], ['12'])).
% 0.37/0.55  thf('14', plain,
% 0.37/0.55      (((r2_hidden @ sk_A @ sk_B)
% 0.37/0.55        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_tarski @ sk_A)))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('15', plain,
% 0.37/0.55      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.37/0.55      inference('split', [status(esa)], ['14'])).
% 0.37/0.55  thf('16', plain,
% 0.37/0.55      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.37/0.55      inference('split', [status(esa)], ['14'])).
% 0.37/0.55  thf('17', plain,
% 0.37/0.55      (![X46 : $i, X48 : $i, X49 : $i]:
% 0.37/0.55         ((r1_tarski @ (k2_tarski @ X46 @ X48) @ X49)
% 0.37/0.55          | ~ (r2_hidden @ X48 @ X49)
% 0.37/0.55          | ~ (r2_hidden @ X46 @ X49))),
% 0.37/0.55      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.37/0.55  thf('18', plain,
% 0.37/0.55      ((![X0 : $i]:
% 0.37/0.55          (~ (r2_hidden @ X0 @ sk_B)
% 0.37/0.55           | (r1_tarski @ (k2_tarski @ X0 @ sk_A) @ sk_B)))
% 0.37/0.55         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['16', '17'])).
% 0.37/0.55  thf('19', plain,
% 0.37/0.55      (((r1_tarski @ (k2_tarski @ sk_A @ sk_A) @ sk_B))
% 0.37/0.55         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['15', '18'])).
% 0.37/0.55  thf('20', plain,
% 0.37/0.55      (![X16 : $i]: ((k2_tarski @ X16 @ X16) = (k1_tarski @ X16))),
% 0.37/0.55      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.37/0.55  thf('21', plain,
% 0.37/0.55      (((r1_tarski @ (k1_tarski @ sk_A) @ sk_B))
% 0.37/0.55         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.37/0.55      inference('demod', [status(thm)], ['19', '20'])).
% 0.37/0.55  thf(t28_xboole_1, axiom,
% 0.37/0.55    (![A:$i,B:$i]:
% 0.37/0.55     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.37/0.55  thf('22', plain,
% 0.37/0.55      (![X11 : $i, X12 : $i]:
% 0.37/0.55         (((k3_xboole_0 @ X11 @ X12) = (X11)) | ~ (r1_tarski @ X11 @ X12))),
% 0.37/0.55      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.37/0.55  thf('23', plain,
% 0.37/0.55      ((((k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A)))
% 0.37/0.55         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['21', '22'])).
% 0.37/0.55  thf(commutativity_k3_xboole_0, axiom,
% 0.37/0.55    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.37/0.55  thf('24', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.37/0.55      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.37/0.55  thf('25', plain,
% 0.37/0.55      ((((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A)))
% 0.37/0.55         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.37/0.55      inference('demod', [status(thm)], ['23', '24'])).
% 0.37/0.55  thf('26', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.37/0.55      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.37/0.55  thf(t4_xboole_0, axiom,
% 0.37/0.55    (![A:$i,B:$i]:
% 0.37/0.55     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.37/0.55            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.37/0.55       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.37/0.55            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.37/0.55  thf('27', plain,
% 0.37/0.55      (![X3 : $i, X5 : $i, X6 : $i]:
% 0.37/0.55         (~ (r2_hidden @ X5 @ (k3_xboole_0 @ X3 @ X6))
% 0.37/0.55          | ~ (r1_xboole_0 @ X3 @ X6))),
% 0.37/0.55      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.37/0.55  thf('28', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.55         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.37/0.55          | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.37/0.55      inference('sup-', [status(thm)], ['26', '27'])).
% 0.37/0.55  thf('29', plain,
% 0.37/0.55      ((![X0 : $i]:
% 0.37/0.55          (~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.37/0.55           | ~ (r1_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)))
% 0.37/0.55         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['25', '28'])).
% 0.37/0.55  thf('30', plain,
% 0.37/0.55      ((![X0 : $i]: ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))
% 0.37/0.55         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))) & 
% 0.37/0.55             ((r2_hidden @ sk_A @ sk_B)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['13', '29'])).
% 0.37/0.55  thf('31', plain,
% 0.37/0.55      (~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))) | 
% 0.37/0.55       ~ ((r2_hidden @ sk_A @ sk_B))),
% 0.37/0.55      inference('sup-', [status(thm)], ['9', '30'])).
% 0.37/0.55  thf('32', plain, (~ ((r2_hidden @ sk_A @ sk_B))),
% 0.37/0.55      inference('sat_resolution*', [status(thm)], ['2', '31'])).
% 0.37/0.55  thf('33', plain, (~ (r2_hidden @ sk_A @ sk_B)),
% 0.37/0.55      inference('simpl_trail', [status(thm)], ['1', '32'])).
% 0.37/0.55  thf(l27_zfmisc_1, axiom,
% 0.37/0.55    (![A:$i,B:$i]:
% 0.37/0.55     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.37/0.55  thf('34', plain,
% 0.37/0.55      (![X44 : $i, X45 : $i]:
% 0.37/0.55         ((r1_xboole_0 @ (k1_tarski @ X44) @ X45) | (r2_hidden @ X44 @ X45))),
% 0.37/0.55      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.37/0.55  thf('35', plain,
% 0.37/0.55      (![X13 : $i, X14 : $i]:
% 0.37/0.55         (((k4_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_xboole_0 @ X13 @ X14))),
% 0.37/0.55      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.37/0.55  thf('36', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i]:
% 0.37/0.55         ((r2_hidden @ X1 @ X0)
% 0.37/0.55          | ((k4_xboole_0 @ (k1_tarski @ X1) @ X0) = (k1_tarski @ X1)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['34', '35'])).
% 0.37/0.55  thf('37', plain,
% 0.37/0.55      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_tarski @ sk_A)))
% 0.37/0.55         <= (~
% 0.37/0.55             (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))))),
% 0.37/0.55      inference('split', [status(esa)], ['14'])).
% 0.37/0.55  thf('38', plain,
% 0.37/0.55      (~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))) | 
% 0.37/0.55       ((r2_hidden @ sk_A @ sk_B))),
% 0.37/0.55      inference('split', [status(esa)], ['14'])).
% 0.37/0.55  thf('39', plain,
% 0.37/0.55      (~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A)))),
% 0.37/0.55      inference('sat_resolution*', [status(thm)], ['2', '31', '38'])).
% 0.37/0.55  thf('40', plain,
% 0.37/0.55      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_tarski @ sk_A))),
% 0.37/0.55      inference('simpl_trail', [status(thm)], ['37', '39'])).
% 0.37/0.55  thf('41', plain,
% 0.37/0.55      ((((k1_tarski @ sk_A) != (k1_tarski @ sk_A)) | (r2_hidden @ sk_A @ sk_B))),
% 0.37/0.55      inference('sup-', [status(thm)], ['36', '40'])).
% 0.37/0.55  thf('42', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.37/0.55      inference('simplify', [status(thm)], ['41'])).
% 0.37/0.55  thf('43', plain, ($false), inference('demod', [status(thm)], ['33', '42'])).
% 0.37/0.55  
% 0.37/0.55  % SZS output end Refutation
% 0.37/0.55  
% 0.37/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
