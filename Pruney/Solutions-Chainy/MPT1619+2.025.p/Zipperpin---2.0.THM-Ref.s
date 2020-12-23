%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.v88ik8LGs9

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:27 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 120 expanded)
%              Number of leaves         :   28 (  52 expanded)
%              Depth                    :   12
%              Number of atoms          :  379 ( 614 expanded)
%              Number of equality atoms :   35 (  62 expanded)
%              Maximal formula depth    :   10 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k6_yellow_1_type,type,(
    k6_yellow_1: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_funcop_1_type,type,(
    k2_funcop_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k7_funcop_1_type,type,(
    k7_funcop_1: $i > $i > $i )).

thf(v1_yellow_1_type,type,(
    v1_yellow_1: $i > $o )).

thf(g1_orders_2_type,type,(
    g1_orders_2: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k5_yellow_1_type,type,(
    k5_yellow_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(d5_yellow_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( l1_orders_2 @ B )
     => ( ( k6_yellow_1 @ A @ B )
        = ( k5_yellow_1 @ A @ ( k7_funcop_1 @ A @ B ) ) ) ) )).

thf('0',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k6_yellow_1 @ X17 @ X18 )
        = ( k5_yellow_1 @ X17 @ ( k7_funcop_1 @ X17 @ X18 ) ) )
      | ~ ( l1_orders_2 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d5_yellow_1])).

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
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t27_yellow_1,conjecture,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( k6_yellow_1 @ k1_xboole_0 @ A )
        = ( g1_orders_2 @ ( k1_tarski @ k1_xboole_0 ) @ ( k6_partfun1 @ ( k1_tarski @ k1_xboole_0 ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_orders_2 @ A )
       => ( ( k6_yellow_1 @ k1_xboole_0 @ A )
          = ( g1_orders_2 @ ( k1_tarski @ k1_xboole_0 ) @ ( k6_partfun1 @ ( k1_tarski @ k1_xboole_0 ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t27_yellow_1])).

thf('4',plain,(
    ( k6_yellow_1 @ k1_xboole_0 @ sk_A )
 != ( g1_orders_2 @ ( k1_tarski @ k1_xboole_0 ) @ ( k6_partfun1 @ ( k1_tarski @ k1_xboole_0 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t81_relat_1,axiom,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('6',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('7',plain,(
    ! [X16: $i] :
      ( ( k6_partfun1 @ X16 )
      = ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('8',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['6','7'])).

thf(fc11_funct_2,axiom,(
    ! [A: $i] :
      ( ( v1_partfun1 @ ( k6_relat_1 @ A ) @ A )
      & ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v4_relat_1 @ ( k6_relat_1 @ A ) @ A )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('9',plain,(
    ! [X15: $i] :
      ( v1_partfun1 @ ( k6_relat_1 @ X15 ) @ X15 ) ),
    inference(cnf,[status(esa)],[fc11_funct_2])).

thf('10',plain,(
    ! [X16: $i] :
      ( ( k6_partfun1 @ X16 )
      = ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('11',plain,(
    ! [X15: $i] :
      ( v1_partfun1 @ ( k6_partfun1 @ X15 ) @ X15 ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    v1_partfun1 @ k1_xboole_0 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['8','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( v1_partfun1 @ k1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','12'])).

thf(t26_yellow_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v4_relat_1 @ A @ k1_xboole_0 )
        & ( v1_funct_1 @ A )
        & ( v1_partfun1 @ A @ k1_xboole_0 )
        & ( v1_yellow_1 @ A ) )
     => ( ( k5_yellow_1 @ k1_xboole_0 @ A )
        = ( g1_orders_2 @ ( k1_tarski @ k1_xboole_0 ) @ ( k6_partfun1 @ ( k1_tarski @ k1_xboole_0 ) ) ) ) ) )).

thf('14',plain,(
    ! [X24: $i] :
      ( ( ( k5_yellow_1 @ k1_xboole_0 @ X24 )
        = ( g1_orders_2 @ ( k1_tarski @ k1_xboole_0 ) @ ( k6_partfun1 @ ( k1_tarski @ k1_xboole_0 ) ) ) )
      | ~ ( v1_yellow_1 @ X24 )
      | ~ ( v1_partfun1 @ X24 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v4_relat_1 @ X24 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t26_yellow_1])).

thf('15',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 )
    | ~ ( v4_relat_1 @ k1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_funct_1 @ k1_xboole_0 )
    | ~ ( v1_yellow_1 @ k1_xboole_0 )
    | ( ( k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0 )
      = ( g1_orders_2 @ ( k1_tarski @ k1_xboole_0 ) @ ( k6_partfun1 @ ( k1_tarski @ k1_xboole_0 ) ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('17',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['6','7'])).

thf('18',plain,(
    ! [X12: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc11_funct_2])).

thf('19',plain,(
    ! [X16: $i] :
      ( ( k6_partfun1 @ X16 )
      = ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('20',plain,(
    ! [X12: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X12 ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['17','20'])).

thf('22',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['6','7'])).

thf('23',plain,(
    ! [X13: $i] :
      ( v4_relat_1 @ ( k6_relat_1 @ X13 ) @ X13 ) ),
    inference(cnf,[status(esa)],[fc11_funct_2])).

thf('24',plain,(
    ! [X16: $i] :
      ( ( k6_partfun1 @ X16 )
      = ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('25',plain,(
    ! [X13: $i] :
      ( v4_relat_1 @ ( k6_partfun1 @ X13 ) @ X13 ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    v4_relat_1 @ k1_xboole_0 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['22','25'])).

thf('27',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['6','7'])).

thf('28',plain,(
    ! [X14: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc11_funct_2])).

thf('29',plain,(
    ! [X16: $i] :
      ( ( k6_partfun1 @ X16 )
      = ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('30',plain,(
    ! [X14: $i] :
      ( v1_funct_1 @ ( k6_partfun1 @ X14 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['27','30'])).

thf('32',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc2_funcop_1,axiom,(
    ! [A: $i] :
      ( v1_xboole_0 @ ( k2_funcop_1 @ k1_xboole_0 @ A ) ) )).

thf('33',plain,(
    ! [X21: $i] :
      ( v1_xboole_0 @ ( k2_funcop_1 @ k1_xboole_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc2_funcop_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('35',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k2_funcop_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf(fc10_yellow_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( l1_orders_2 @ B )
     => ( v1_yellow_1 @ ( k2_funcop_1 @ A @ B ) ) ) )).

thf('36',plain,(
    ! [X19: $i,X20: $i] :
      ( ( v1_yellow_1 @ ( k2_funcop_1 @ X19 @ X20 ) )
      | ~ ( l1_orders_2 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc10_yellow_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( v1_yellow_1 @ k1_xboole_0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    v1_yellow_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['32','37'])).

thf('39',plain,
    ( ( k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0 )
    = ( g1_orders_2 @ ( k1_tarski @ k1_xboole_0 ) @ ( k6_partfun1 @ ( k1_tarski @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['15','16','21','26','31','38'])).

thf('40',plain,(
    ( k6_yellow_1 @ k1_xboole_0 @ sk_A )
 != ( k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['4','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( ( k6_yellow_1 @ k1_xboole_0 @ sk_A )
       != ( k5_yellow_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( ( k6_yellow_1 @ k1_xboole_0 @ sk_A )
       != ( k6_yellow_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v1_xboole_0 @ ( k7_funcop_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['0','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k2_funcop_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf(redefinition_k7_funcop_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k7_funcop_1 @ A @ B )
      = ( k2_funcop_1 @ A @ B ) ) )).

thf('44',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k7_funcop_1 @ X22 @ X23 )
      = ( k2_funcop_1 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_funcop_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k7_funcop_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( ( k6_yellow_1 @ k1_xboole_0 @ sk_A )
       != ( k6_yellow_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(demod,[status(thm)],['42','45','46'])).

thf('48',plain,(
    ~ ( l1_orders_2 @ sk_A ) ),
    inference(eq_res,[status(thm)],['47'])).

thf('49',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    $false ),
    inference(demod,[status(thm)],['48','49'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.v88ik8LGs9
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:08:06 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  % Running portfolio for 600 s
% 0.14/0.36  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.21/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.54  % Solved by: fo/fo7.sh
% 0.21/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.54  % done 107 iterations in 0.081s
% 0.21/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.54  % SZS output start Refutation
% 0.21/0.54  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.21/0.54  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.54  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.21/0.54  thf(k6_yellow_1_type, type, k6_yellow_1: $i > $i > $i).
% 0.21/0.54  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.54  thf(k2_funcop_1_type, type, k2_funcop_1: $i > $i > $i).
% 0.21/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.54  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.54  thf(k7_funcop_1_type, type, k7_funcop_1: $i > $i > $i).
% 0.21/0.54  thf(v1_yellow_1_type, type, v1_yellow_1: $i > $o).
% 0.21/0.54  thf(g1_orders_2_type, type, g1_orders_2: $i > $i > $i).
% 0.21/0.54  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.21/0.54  thf(k5_yellow_1_type, type, k5_yellow_1: $i > $i > $i).
% 0.21/0.54  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.54  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.21/0.54  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.21/0.54  thf(d5_yellow_1, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( l1_orders_2 @ B ) =>
% 0.21/0.54       ( ( k6_yellow_1 @ A @ B ) =
% 0.21/0.54         ( k5_yellow_1 @ A @ ( k7_funcop_1 @ A @ B ) ) ) ))).
% 0.21/0.54  thf('0', plain,
% 0.21/0.54      (![X17 : $i, X18 : $i]:
% 0.21/0.54         (((k6_yellow_1 @ X17 @ X18)
% 0.21/0.54            = (k5_yellow_1 @ X17 @ (k7_funcop_1 @ X17 @ X18)))
% 0.21/0.54          | ~ (l1_orders_2 @ X18))),
% 0.21/0.54      inference('cnf', [status(esa)], [d5_yellow_1])).
% 0.21/0.54  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.21/0.54  thf('1', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.54      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.54  thf(t8_boole, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 0.21/0.54  thf('2', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]:
% 0.21/0.54         (~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1) | ((X0) = (X1)))),
% 0.21/0.54      inference('cnf', [status(esa)], [t8_boole])).
% 0.21/0.54  thf('3', plain,
% 0.21/0.54      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.54  thf(t27_yellow_1, conjecture,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( l1_orders_2 @ A ) =>
% 0.21/0.54       ( ( k6_yellow_1 @ k1_xboole_0 @ A ) =
% 0.21/0.54         ( g1_orders_2 @
% 0.21/0.54           ( k1_tarski @ k1_xboole_0 ) @ 
% 0.21/0.54           ( k6_partfun1 @ ( k1_tarski @ k1_xboole_0 ) ) ) ) ))).
% 0.21/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.54    (~( ![A:$i]:
% 0.21/0.54        ( ( l1_orders_2 @ A ) =>
% 0.21/0.54          ( ( k6_yellow_1 @ k1_xboole_0 @ A ) =
% 0.21/0.54            ( g1_orders_2 @
% 0.21/0.54              ( k1_tarski @ k1_xboole_0 ) @ 
% 0.21/0.54              ( k6_partfun1 @ ( k1_tarski @ k1_xboole_0 ) ) ) ) ) )),
% 0.21/0.54    inference('cnf.neg', [status(esa)], [t27_yellow_1])).
% 0.21/0.54  thf('4', plain,
% 0.21/0.54      (((k6_yellow_1 @ k1_xboole_0 @ sk_A)
% 0.21/0.54         != (g1_orders_2 @ (k1_tarski @ k1_xboole_0) @ 
% 0.21/0.54             (k6_partfun1 @ (k1_tarski @ k1_xboole_0))))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('5', plain,
% 0.21/0.54      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.54  thf(t81_relat_1, axiom, (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.21/0.54  thf('6', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.54      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.21/0.54  thf(redefinition_k6_partfun1, axiom,
% 0.21/0.54    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.21/0.54  thf('7', plain, (![X16 : $i]: ((k6_partfun1 @ X16) = (k6_relat_1 @ X16))),
% 0.21/0.54      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.21/0.54  thf('8', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.54      inference('demod', [status(thm)], ['6', '7'])).
% 0.21/0.54  thf(fc11_funct_2, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( v1_partfun1 @ ( k6_relat_1 @ A ) @ A ) & 
% 0.21/0.54       ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.21/0.54       ( v4_relat_1 @ ( k6_relat_1 @ A ) @ A ) & 
% 0.21/0.54       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.21/0.54  thf('9', plain, (![X15 : $i]: (v1_partfun1 @ (k6_relat_1 @ X15) @ X15)),
% 0.21/0.54      inference('cnf', [status(esa)], [fc11_funct_2])).
% 0.21/0.54  thf('10', plain, (![X16 : $i]: ((k6_partfun1 @ X16) = (k6_relat_1 @ X16))),
% 0.21/0.54      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.21/0.54  thf('11', plain, (![X15 : $i]: (v1_partfun1 @ (k6_partfun1 @ X15) @ X15)),
% 0.21/0.54      inference('demod', [status(thm)], ['9', '10'])).
% 0.21/0.54  thf('12', plain, ((v1_partfun1 @ k1_xboole_0 @ k1_xboole_0)),
% 0.21/0.54      inference('sup+', [status(thm)], ['8', '11'])).
% 0.21/0.54  thf('13', plain,
% 0.21/0.54      (![X0 : $i]: ((v1_partfun1 @ k1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X0))),
% 0.21/0.54      inference('sup+', [status(thm)], ['5', '12'])).
% 0.21/0.54  thf(t26_yellow_1, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( ( v1_relat_1 @ A ) & ( v4_relat_1 @ A @ k1_xboole_0 ) & 
% 0.21/0.54         ( v1_funct_1 @ A ) & ( v1_partfun1 @ A @ k1_xboole_0 ) & 
% 0.21/0.54         ( v1_yellow_1 @ A ) ) =>
% 0.21/0.54       ( ( k5_yellow_1 @ k1_xboole_0 @ A ) =
% 0.21/0.54         ( g1_orders_2 @
% 0.21/0.54           ( k1_tarski @ k1_xboole_0 ) @ 
% 0.21/0.54           ( k6_partfun1 @ ( k1_tarski @ k1_xboole_0 ) ) ) ) ))).
% 0.21/0.54  thf('14', plain,
% 0.21/0.54      (![X24 : $i]:
% 0.21/0.54         (((k5_yellow_1 @ k1_xboole_0 @ X24)
% 0.21/0.54            = (g1_orders_2 @ (k1_tarski @ k1_xboole_0) @ 
% 0.21/0.54               (k6_partfun1 @ (k1_tarski @ k1_xboole_0))))
% 0.21/0.54          | ~ (v1_yellow_1 @ X24)
% 0.21/0.54          | ~ (v1_partfun1 @ X24 @ k1_xboole_0)
% 0.21/0.54          | ~ (v1_funct_1 @ X24)
% 0.21/0.54          | ~ (v4_relat_1 @ X24 @ k1_xboole_0)
% 0.21/0.54          | ~ (v1_relat_1 @ X24))),
% 0.21/0.54      inference('cnf', [status(esa)], [t26_yellow_1])).
% 0.21/0.54  thf('15', plain,
% 0.21/0.54      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.21/0.54        | ~ (v1_relat_1 @ k1_xboole_0)
% 0.21/0.54        | ~ (v4_relat_1 @ k1_xboole_0 @ k1_xboole_0)
% 0.21/0.54        | ~ (v1_funct_1 @ k1_xboole_0)
% 0.21/0.54        | ~ (v1_yellow_1 @ k1_xboole_0)
% 0.21/0.54        | ((k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0)
% 0.21/0.54            = (g1_orders_2 @ (k1_tarski @ k1_xboole_0) @ 
% 0.21/0.54               (k6_partfun1 @ (k1_tarski @ k1_xboole_0)))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.54  thf('16', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.54      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.54  thf('17', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.54      inference('demod', [status(thm)], ['6', '7'])).
% 0.21/0.54  thf('18', plain, (![X12 : $i]: (v1_relat_1 @ (k6_relat_1 @ X12))),
% 0.21/0.54      inference('cnf', [status(esa)], [fc11_funct_2])).
% 0.21/0.54  thf('19', plain, (![X16 : $i]: ((k6_partfun1 @ X16) = (k6_relat_1 @ X16))),
% 0.21/0.54      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.21/0.54  thf('20', plain, (![X12 : $i]: (v1_relat_1 @ (k6_partfun1 @ X12))),
% 0.21/0.54      inference('demod', [status(thm)], ['18', '19'])).
% 0.21/0.54  thf('21', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.21/0.54      inference('sup+', [status(thm)], ['17', '20'])).
% 0.21/0.54  thf('22', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.54      inference('demod', [status(thm)], ['6', '7'])).
% 0.21/0.54  thf('23', plain, (![X13 : $i]: (v4_relat_1 @ (k6_relat_1 @ X13) @ X13)),
% 0.21/0.54      inference('cnf', [status(esa)], [fc11_funct_2])).
% 0.21/0.54  thf('24', plain, (![X16 : $i]: ((k6_partfun1 @ X16) = (k6_relat_1 @ X16))),
% 0.21/0.54      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.21/0.54  thf('25', plain, (![X13 : $i]: (v4_relat_1 @ (k6_partfun1 @ X13) @ X13)),
% 0.21/0.54      inference('demod', [status(thm)], ['23', '24'])).
% 0.21/0.54  thf('26', plain, ((v4_relat_1 @ k1_xboole_0 @ k1_xboole_0)),
% 0.21/0.54      inference('sup+', [status(thm)], ['22', '25'])).
% 0.21/0.54  thf('27', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.54      inference('demod', [status(thm)], ['6', '7'])).
% 0.21/0.54  thf('28', plain, (![X14 : $i]: (v1_funct_1 @ (k6_relat_1 @ X14))),
% 0.21/0.54      inference('cnf', [status(esa)], [fc11_funct_2])).
% 0.21/0.54  thf('29', plain, (![X16 : $i]: ((k6_partfun1 @ X16) = (k6_relat_1 @ X16))),
% 0.21/0.54      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.21/0.54  thf('30', plain, (![X14 : $i]: (v1_funct_1 @ (k6_partfun1 @ X14))),
% 0.21/0.54      inference('demod', [status(thm)], ['28', '29'])).
% 0.21/0.54  thf('31', plain, ((v1_funct_1 @ k1_xboole_0)),
% 0.21/0.54      inference('sup+', [status(thm)], ['27', '30'])).
% 0.21/0.54  thf('32', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(fc2_funcop_1, axiom,
% 0.21/0.54    (![A:$i]: ( v1_xboole_0 @ ( k2_funcop_1 @ k1_xboole_0 @ A ) ))).
% 0.21/0.54  thf('33', plain,
% 0.21/0.54      (![X21 : $i]: (v1_xboole_0 @ (k2_funcop_1 @ k1_xboole_0 @ X21))),
% 0.21/0.54      inference('cnf', [status(esa)], [fc2_funcop_1])).
% 0.21/0.54  thf('34', plain,
% 0.21/0.54      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.54  thf('35', plain,
% 0.21/0.54      (![X0 : $i]: ((k1_xboole_0) = (k2_funcop_1 @ k1_xboole_0 @ X0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['33', '34'])).
% 0.21/0.54  thf(fc10_yellow_1, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( l1_orders_2 @ B ) => ( v1_yellow_1 @ ( k2_funcop_1 @ A @ B ) ) ))).
% 0.21/0.54  thf('36', plain,
% 0.21/0.54      (![X19 : $i, X20 : $i]:
% 0.21/0.54         ((v1_yellow_1 @ (k2_funcop_1 @ X19 @ X20)) | ~ (l1_orders_2 @ X20))),
% 0.21/0.54      inference('cnf', [status(esa)], [fc10_yellow_1])).
% 0.21/0.54  thf('37', plain,
% 0.21/0.54      (![X0 : $i]: ((v1_yellow_1 @ k1_xboole_0) | ~ (l1_orders_2 @ X0))),
% 0.21/0.54      inference('sup+', [status(thm)], ['35', '36'])).
% 0.21/0.54  thf('38', plain, ((v1_yellow_1 @ k1_xboole_0)),
% 0.21/0.54      inference('sup-', [status(thm)], ['32', '37'])).
% 0.21/0.54  thf('39', plain,
% 0.21/0.54      (((k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0)
% 0.21/0.54         = (g1_orders_2 @ (k1_tarski @ k1_xboole_0) @ 
% 0.21/0.54            (k6_partfun1 @ (k1_tarski @ k1_xboole_0))))),
% 0.21/0.54      inference('demod', [status(thm)], ['15', '16', '21', '26', '31', '38'])).
% 0.21/0.54  thf('40', plain,
% 0.21/0.54      (((k6_yellow_1 @ k1_xboole_0 @ sk_A)
% 0.21/0.54         != (k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0))),
% 0.21/0.54      inference('demod', [status(thm)], ['4', '39'])).
% 0.21/0.54  thf('41', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (((k6_yellow_1 @ k1_xboole_0 @ sk_A)
% 0.21/0.54            != (k5_yellow_1 @ k1_xboole_0 @ X0))
% 0.21/0.54          | ~ (v1_xboole_0 @ X0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['3', '40'])).
% 0.21/0.54  thf('42', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (((k6_yellow_1 @ k1_xboole_0 @ sk_A)
% 0.21/0.54            != (k6_yellow_1 @ k1_xboole_0 @ X0))
% 0.21/0.54          | ~ (l1_orders_2 @ X0)
% 0.21/0.54          | ~ (v1_xboole_0 @ (k7_funcop_1 @ k1_xboole_0 @ X0)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['0', '41'])).
% 0.21/0.54  thf('43', plain,
% 0.21/0.54      (![X0 : $i]: ((k1_xboole_0) = (k2_funcop_1 @ k1_xboole_0 @ X0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['33', '34'])).
% 0.21/0.54  thf(redefinition_k7_funcop_1, axiom,
% 0.21/0.54    (![A:$i,B:$i]: ( ( k7_funcop_1 @ A @ B ) = ( k2_funcop_1 @ A @ B ) ))).
% 0.21/0.54  thf('44', plain,
% 0.21/0.54      (![X22 : $i, X23 : $i]:
% 0.21/0.54         ((k7_funcop_1 @ X22 @ X23) = (k2_funcop_1 @ X22 @ X23))),
% 0.21/0.54      inference('cnf', [status(esa)], [redefinition_k7_funcop_1])).
% 0.21/0.54  thf('45', plain,
% 0.21/0.54      (![X0 : $i]: ((k1_xboole_0) = (k7_funcop_1 @ k1_xboole_0 @ X0))),
% 0.21/0.54      inference('demod', [status(thm)], ['43', '44'])).
% 0.21/0.54  thf('46', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.54      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.54  thf('47', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (((k6_yellow_1 @ k1_xboole_0 @ sk_A)
% 0.21/0.54            != (k6_yellow_1 @ k1_xboole_0 @ X0))
% 0.21/0.54          | ~ (l1_orders_2 @ X0))),
% 0.21/0.54      inference('demod', [status(thm)], ['42', '45', '46'])).
% 0.21/0.54  thf('48', plain, (~ (l1_orders_2 @ sk_A)),
% 0.21/0.54      inference('eq_res', [status(thm)], ['47'])).
% 0.21/0.54  thf('49', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('50', plain, ($false), inference('demod', [status(thm)], ['48', '49'])).
% 0.21/0.54  
% 0.21/0.54  % SZS output end Refutation
% 0.21/0.54  
% 0.21/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
