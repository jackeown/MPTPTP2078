%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.u5WZEkoC0F

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:42:59 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 109 expanded)
%              Number of leaves         :   28 (  45 expanded)
%              Depth                    :   13
%              Number of atoms          :  398 ( 549 expanded)
%              Number of equality atoms :   53 (  69 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(t172_relat_1,conjecture,(
    ! [A: $i] :
      ( ( k10_relat_1 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( k10_relat_1 @ k1_xboole_0 @ A )
        = k1_xboole_0 ) ),
    inference('cnf.neg',[status(esa)],[t172_relat_1])).

thf('0',plain,(
    ( k10_relat_1 @ k1_xboole_0 @ sk_A )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('1',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('2',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_xboole_0 @ X5 )
      | ~ ( v1_xboole_0 @ X6 )
      | ( X5 = X6 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('4',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('5',plain,(
    ! [X48: $i] :
      ( ( ( k10_relat_1 @ X48 @ ( k2_relat_1 @ X48 ) )
        = ( k1_relat_1 @ X48 ) )
      | ~ ( v1_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('6',plain,
    ( ( ( k10_relat_1 @ k1_xboole_0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('8',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('9',plain,(
    ! [X49: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X49 ) )
      = X49 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(fc8_relat_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A ) )
     => ~ ( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) )).

thf('10',plain,(
    ! [X45: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ X45 ) )
      | ~ ( v1_relat_1 @ X45 )
      | ( v1_xboole_0 @ X45 ) ) ),
    inference(cnf,[status(esa)],[fc8_relat_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('12',plain,(
    ! [X44: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( k1_xboole_0
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X44: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['8','17'])).

thf('19',plain,
    ( ( k10_relat_1 @ k1_xboole_0 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['6','7','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','19'])).

thf(t168_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k10_relat_1 @ B @ A )
        = ( k10_relat_1 @ B @ ( k3_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ) ) )).

thf('21',plain,(
    ! [X46: $i,X47: $i] :
      ( ( ( k10_relat_1 @ X46 @ X47 )
        = ( k10_relat_1 @ X46 @ ( k3_xboole_0 @ ( k2_relat_1 @ X46 ) @ X47 ) ) )
      | ~ ( v1_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t168_relat_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ ( k3_xboole_0 @ ( k2_relat_1 @ k1_xboole_0 ) @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('24',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['8','17'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('26',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('27',plain,(
    ! [X10: $i] :
      ( ( k5_xboole_0 @ X10 @ X10 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('28',plain,(
    ! [X10: $i] :
      ( ( k5_xboole_0 @ X10 @ X10 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('29',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X7 @ X8 ) @ X9 )
      = ( k5_xboole_0 @ X7 @ ( k5_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['27','30'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('32',plain,(
    ! [X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X1 )
      = X1 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('33',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X10: $i] :
      ( ( k5_xboole_0 @ X10 @ X10 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('37',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k2_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k4_xboole_0 @ X12 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('40',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['31','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['26','41'])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('43',plain,(
    ! [X4: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X4 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('44',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['25','44','45'])).

thf('47',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','46'])).

thf('48',plain,(
    $false ),
    inference(simplify,[status(thm)],['47'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.u5WZEkoC0F
% 0.13/0.33  % Computer   : n013.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:52:40 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.37/0.61  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.37/0.61  % Solved by: fo/fo7.sh
% 0.37/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.61  % done 355 iterations in 0.165s
% 0.37/0.61  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.37/0.61  % SZS output start Refutation
% 0.37/0.61  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.37/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.61  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.37/0.61  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.37/0.61  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.37/0.61  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.37/0.61  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.37/0.61  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.37/0.61  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.37/0.61  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.37/0.61  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.37/0.61  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.37/0.61  thf(t172_relat_1, conjecture,
% 0.37/0.61    (![A:$i]: ( ( k10_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.37/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.61    (~( ![A:$i]: ( ( k10_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) )),
% 0.37/0.61    inference('cnf.neg', [status(esa)], [t172_relat_1])).
% 0.37/0.61  thf('0', plain, (((k10_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.37/0.61  thf('1', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.37/0.61      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.37/0.61  thf(t8_boole, axiom,
% 0.37/0.61    (![A:$i,B:$i]:
% 0.37/0.61     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 0.37/0.61  thf('2', plain,
% 0.37/0.61      (![X5 : $i, X6 : $i]:
% 0.37/0.61         (~ (v1_xboole_0 @ X5) | ~ (v1_xboole_0 @ X6) | ((X5) = (X6)))),
% 0.37/0.61      inference('cnf', [status(esa)], [t8_boole])).
% 0.37/0.61  thf('3', plain,
% 0.37/0.61      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.37/0.61      inference('sup-', [status(thm)], ['1', '2'])).
% 0.37/0.61  thf(t60_relat_1, axiom,
% 0.37/0.61    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.37/0.61     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.37/0.61  thf('4', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.37/0.61      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.37/0.61  thf(t169_relat_1, axiom,
% 0.37/0.61    (![A:$i]:
% 0.37/0.61     ( ( v1_relat_1 @ A ) =>
% 0.37/0.61       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.37/0.61  thf('5', plain,
% 0.37/0.61      (![X48 : $i]:
% 0.37/0.61         (((k10_relat_1 @ X48 @ (k2_relat_1 @ X48)) = (k1_relat_1 @ X48))
% 0.37/0.61          | ~ (v1_relat_1 @ X48))),
% 0.37/0.61      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.37/0.61  thf('6', plain,
% 0.37/0.61      ((((k10_relat_1 @ k1_xboole_0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))
% 0.37/0.61        | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.37/0.61      inference('sup+', [status(thm)], ['4', '5'])).
% 0.37/0.61  thf('7', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.37/0.61      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.37/0.61  thf('8', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.37/0.61      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.37/0.61  thf(t71_relat_1, axiom,
% 0.37/0.61    (![A:$i]:
% 0.37/0.61     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.37/0.61       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.37/0.61  thf('9', plain, (![X49 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X49)) = (X49))),
% 0.37/0.61      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.37/0.61  thf(fc8_relat_1, axiom,
% 0.37/0.61    (![A:$i]:
% 0.37/0.61     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_relat_1 @ A ) ) =>
% 0.37/0.61       ( ~( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) ))).
% 0.37/0.61  thf('10', plain,
% 0.37/0.61      (![X45 : $i]:
% 0.37/0.61         (~ (v1_xboole_0 @ (k1_relat_1 @ X45))
% 0.37/0.61          | ~ (v1_relat_1 @ X45)
% 0.37/0.61          | (v1_xboole_0 @ X45))),
% 0.37/0.61      inference('cnf', [status(esa)], [fc8_relat_1])).
% 0.37/0.61  thf('11', plain,
% 0.37/0.61      (![X0 : $i]:
% 0.37/0.61         (~ (v1_xboole_0 @ X0)
% 0.37/0.61          | (v1_xboole_0 @ (k6_relat_1 @ X0))
% 0.37/0.61          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.37/0.61      inference('sup-', [status(thm)], ['9', '10'])).
% 0.37/0.61  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.37/0.61  thf('12', plain, (![X44 : $i]: (v1_relat_1 @ (k6_relat_1 @ X44))),
% 0.37/0.61      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.37/0.61  thf('13', plain,
% 0.37/0.61      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (v1_xboole_0 @ (k6_relat_1 @ X0)))),
% 0.37/0.61      inference('demod', [status(thm)], ['11', '12'])).
% 0.37/0.61  thf('14', plain,
% 0.37/0.61      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.37/0.61      inference('sup-', [status(thm)], ['1', '2'])).
% 0.37/0.61  thf('15', plain,
% 0.37/0.61      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k1_xboole_0) = (k6_relat_1 @ X0)))),
% 0.37/0.61      inference('sup-', [status(thm)], ['13', '14'])).
% 0.37/0.61  thf('16', plain, (![X44 : $i]: (v1_relat_1 @ (k6_relat_1 @ X44))),
% 0.37/0.61      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.37/0.61  thf('17', plain,
% 0.37/0.61      (![X0 : $i]: ((v1_relat_1 @ k1_xboole_0) | ~ (v1_xboole_0 @ X0))),
% 0.37/0.61      inference('sup+', [status(thm)], ['15', '16'])).
% 0.37/0.61  thf('18', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.37/0.61      inference('sup-', [status(thm)], ['8', '17'])).
% 0.37/0.61  thf('19', plain,
% 0.37/0.61      (((k10_relat_1 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.37/0.61      inference('demod', [status(thm)], ['6', '7', '18'])).
% 0.37/0.61  thf('20', plain,
% 0.37/0.61      (![X0 : $i]:
% 0.37/0.61         (((k10_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))
% 0.37/0.61          | ~ (v1_xboole_0 @ X0))),
% 0.37/0.61      inference('sup+', [status(thm)], ['3', '19'])).
% 0.37/0.61  thf(t168_relat_1, axiom,
% 0.37/0.61    (![A:$i,B:$i]:
% 0.37/0.61     ( ( v1_relat_1 @ B ) =>
% 0.37/0.61       ( ( k10_relat_1 @ B @ A ) =
% 0.37/0.61         ( k10_relat_1 @ B @ ( k3_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ) ))).
% 0.37/0.61  thf('21', plain,
% 0.37/0.61      (![X46 : $i, X47 : $i]:
% 0.37/0.61         (((k10_relat_1 @ X46 @ X47)
% 0.37/0.61            = (k10_relat_1 @ X46 @ (k3_xboole_0 @ (k2_relat_1 @ X46) @ X47)))
% 0.37/0.61          | ~ (v1_relat_1 @ X46))),
% 0.37/0.61      inference('cnf', [status(esa)], [t168_relat_1])).
% 0.37/0.61  thf('22', plain,
% 0.37/0.61      (![X0 : $i]:
% 0.37/0.61         (((k10_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))
% 0.37/0.61          | ~ (v1_xboole_0 @ (k3_xboole_0 @ (k2_relat_1 @ k1_xboole_0) @ X0))
% 0.37/0.61          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.37/0.61      inference('sup+', [status(thm)], ['20', '21'])).
% 0.37/0.61  thf('23', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.37/0.61      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.37/0.61  thf('24', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.37/0.61      inference('sup-', [status(thm)], ['8', '17'])).
% 0.37/0.61  thf('25', plain,
% 0.37/0.61      (![X0 : $i]:
% 0.37/0.61         (((k10_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))
% 0.37/0.61          | ~ (v1_xboole_0 @ (k3_xboole_0 @ k1_xboole_0 @ X0)))),
% 0.37/0.61      inference('demod', [status(thm)], ['22', '23', '24'])).
% 0.37/0.61  thf(t100_xboole_1, axiom,
% 0.37/0.61    (![A:$i,B:$i]:
% 0.37/0.61     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.37/0.61  thf('26', plain,
% 0.37/0.61      (![X2 : $i, X3 : $i]:
% 0.37/0.61         ((k4_xboole_0 @ X2 @ X3)
% 0.37/0.61           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 0.37/0.61      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.37/0.61  thf(t92_xboole_1, axiom,
% 0.37/0.61    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.37/0.61  thf('27', plain, (![X10 : $i]: ((k5_xboole_0 @ X10 @ X10) = (k1_xboole_0))),
% 0.37/0.61      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.37/0.61  thf('28', plain, (![X10 : $i]: ((k5_xboole_0 @ X10 @ X10) = (k1_xboole_0))),
% 0.37/0.61      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.37/0.61  thf(t91_xboole_1, axiom,
% 0.37/0.61    (![A:$i,B:$i,C:$i]:
% 0.37/0.61     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.37/0.61       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.37/0.61  thf('29', plain,
% 0.37/0.61      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.37/0.61         ((k5_xboole_0 @ (k5_xboole_0 @ X7 @ X8) @ X9)
% 0.37/0.61           = (k5_xboole_0 @ X7 @ (k5_xboole_0 @ X8 @ X9)))),
% 0.37/0.61      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.37/0.61  thf('30', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i]:
% 0.37/0.61         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.37/0.61           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.37/0.61      inference('sup+', [status(thm)], ['28', '29'])).
% 0.37/0.61  thf('31', plain,
% 0.37/0.61      (![X0 : $i]:
% 0.37/0.61         ((k5_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.37/0.61      inference('sup+', [status(thm)], ['27', '30'])).
% 0.37/0.61  thf(idempotence_k3_xboole_0, axiom,
% 0.37/0.61    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.37/0.61  thf('32', plain, (![X1 : $i]: ((k3_xboole_0 @ X1 @ X1) = (X1))),
% 0.37/0.61      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.37/0.61  thf('33', plain,
% 0.37/0.61      (![X2 : $i, X3 : $i]:
% 0.37/0.61         ((k4_xboole_0 @ X2 @ X3)
% 0.37/0.61           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 0.37/0.61      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.37/0.61  thf('34', plain,
% 0.37/0.61      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.37/0.61      inference('sup+', [status(thm)], ['32', '33'])).
% 0.37/0.61  thf('35', plain, (![X10 : $i]: ((k5_xboole_0 @ X10 @ X10) = (k1_xboole_0))),
% 0.37/0.61      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.37/0.61  thf('36', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.37/0.61      inference('sup+', [status(thm)], ['34', '35'])).
% 0.37/0.61  thf(t98_xboole_1, axiom,
% 0.37/0.61    (![A:$i,B:$i]:
% 0.37/0.61     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.37/0.61  thf('37', plain,
% 0.37/0.61      (![X11 : $i, X12 : $i]:
% 0.37/0.61         ((k2_xboole_0 @ X11 @ X12)
% 0.37/0.61           = (k5_xboole_0 @ X11 @ (k4_xboole_0 @ X12 @ X11)))),
% 0.37/0.61      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.37/0.61  thf('38', plain,
% 0.37/0.61      (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.37/0.61      inference('sup+', [status(thm)], ['36', '37'])).
% 0.37/0.61  thf(idempotence_k2_xboole_0, axiom,
% 0.37/0.61    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.37/0.61  thf('39', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.37/0.61      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.37/0.61  thf('40', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.37/0.61      inference('demod', [status(thm)], ['38', '39'])).
% 0.37/0.61  thf('41', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.37/0.61      inference('demod', [status(thm)], ['31', '40'])).
% 0.37/0.61  thf('42', plain,
% 0.37/0.61      (![X0 : $i]:
% 0.37/0.61         ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 0.37/0.61      inference('sup+', [status(thm)], ['26', '41'])).
% 0.37/0.61  thf(t4_boole, axiom,
% 0.37/0.61    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.37/0.61  thf('43', plain,
% 0.37/0.61      (![X4 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X4) = (k1_xboole_0))),
% 0.37/0.61      inference('cnf', [status(esa)], [t4_boole])).
% 0.37/0.61  thf('44', plain,
% 0.37/0.61      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 0.37/0.61      inference('demod', [status(thm)], ['42', '43'])).
% 0.37/0.61  thf('45', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.37/0.61      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.37/0.61  thf('46', plain,
% 0.37/0.61      (![X0 : $i]: ((k10_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.37/0.61      inference('demod', [status(thm)], ['25', '44', '45'])).
% 0.37/0.61  thf('47', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.37/0.61      inference('demod', [status(thm)], ['0', '46'])).
% 0.37/0.61  thf('48', plain, ($false), inference('simplify', [status(thm)], ['47'])).
% 0.37/0.61  
% 0.37/0.61  % SZS output end Refutation
% 0.37/0.61  
% 0.49/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
