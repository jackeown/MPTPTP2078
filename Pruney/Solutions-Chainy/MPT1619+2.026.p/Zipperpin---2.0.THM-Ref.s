%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.fCwZG6BIgP

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:27 EST 2020

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 116 expanded)
%              Number of leaves         :   27 (  50 expanded)
%              Depth                    :   11
%              Number of atoms          :  383 ( 618 expanded)
%              Number of equality atoms :   36 (  65 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(g1_orders_2_type,type,(
    g1_orders_2: $i > $i > $i )).

thf(v1_yellow_1_type,type,(
    v1_yellow_1: $i > $o )).

thf(k5_yellow_1_type,type,(
    k5_yellow_1: $i > $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_yellow_1_type,type,(
    k6_yellow_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(k7_funcop_1_type,type,(
    k7_funcop_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_funcop_1_type,type,(
    k2_funcop_1: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(fc2_funcop_1,axiom,(
    ! [A: $i] :
      ( v1_xboole_0 @ ( k2_funcop_1 @ k1_xboole_0 @ A ) ) )).

thf('0',plain,(
    ! [X13: $i] :
      ( v1_xboole_0 @ ( k2_funcop_1 @ k1_xboole_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc2_funcop_1])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('1',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( k2_funcop_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(redefinition_k7_funcop_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k7_funcop_1 @ A @ B )
      = ( k2_funcop_1 @ A @ B ) ) )).

thf('3',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k7_funcop_1 @ X14 @ X15 )
      = ( k2_funcop_1 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_funcop_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k7_funcop_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(d5_yellow_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( l1_orders_2 @ B )
     => ( ( k6_yellow_1 @ A @ B )
        = ( k5_yellow_1 @ A @ ( k7_funcop_1 @ A @ B ) ) ) ) )).

thf('5',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k6_yellow_1 @ X9 @ X10 )
        = ( k5_yellow_1 @ X9 @ ( k7_funcop_1 @ X9 @ X10 ) ) )
      | ~ ( l1_orders_2 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d5_yellow_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( ( k6_yellow_1 @ k1_xboole_0 @ X0 )
        = ( k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

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

thf('7',plain,(
    ( k6_yellow_1 @ k1_xboole_0 @ sk_A )
 != ( g1_orders_2 @ ( k1_tarski @ k1_xboole_0 ) @ ( k6_partfun1 @ ( k1_tarski @ k1_xboole_0 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t81_relat_1,axiom,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('9',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('10',plain,(
    ! [X8: $i] :
      ( ( k6_partfun1 @ X8 )
      = ( k6_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('11',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( ( k6_partfun1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','11'])).

thf(fc11_funct_2,axiom,(
    ! [A: $i] :
      ( ( v1_partfun1 @ ( k6_relat_1 @ A ) @ A )
      & ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v4_relat_1 @ ( k6_relat_1 @ A ) @ A )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('13',plain,(
    ! [X7: $i] :
      ( v1_partfun1 @ ( k6_relat_1 @ X7 ) @ X7 ) ),
    inference(cnf,[status(esa)],[fc11_funct_2])).

thf('14',plain,(
    ! [X8: $i] :
      ( ( k6_partfun1 @ X8 )
      = ( k6_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('15',plain,(
    ! [X7: $i] :
      ( v1_partfun1 @ ( k6_partfun1 @ X7 ) @ X7 ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( v1_partfun1 @ k1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','15'])).

thf(t26_yellow_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v4_relat_1 @ A @ k1_xboole_0 )
        & ( v1_funct_1 @ A )
        & ( v1_partfun1 @ A @ k1_xboole_0 )
        & ( v1_yellow_1 @ A ) )
     => ( ( k5_yellow_1 @ k1_xboole_0 @ A )
        = ( g1_orders_2 @ ( k1_tarski @ k1_xboole_0 ) @ ( k6_partfun1 @ ( k1_tarski @ k1_xboole_0 ) ) ) ) ) )).

thf('17',plain,(
    ! [X16: $i] :
      ( ( ( k5_yellow_1 @ k1_xboole_0 @ X16 )
        = ( g1_orders_2 @ ( k1_tarski @ k1_xboole_0 ) @ ( k6_partfun1 @ ( k1_tarski @ k1_xboole_0 ) ) ) )
      | ~ ( v1_yellow_1 @ X16 )
      | ~ ( v1_partfun1 @ X16 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v4_relat_1 @ X16 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t26_yellow_1])).

thf('18',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 )
    | ~ ( v4_relat_1 @ k1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_funct_1 @ k1_xboole_0 )
    | ~ ( v1_yellow_1 @ k1_xboole_0 )
    | ( ( k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0 )
      = ( g1_orders_2 @ ( k1_tarski @ k1_xboole_0 ) @ ( k6_partfun1 @ ( k1_tarski @ k1_xboole_0 ) ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X13: $i] :
      ( v1_xboole_0 @ ( k2_funcop_1 @ k1_xboole_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc2_funcop_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k2_funcop_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('21',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['9','10'])).

thf('23',plain,(
    ! [X4: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc11_funct_2])).

thf('24',plain,(
    ! [X8: $i] :
      ( ( k6_partfun1 @ X8 )
      = ( k6_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('25',plain,(
    ! [X4: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X4 ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['22','25'])).

thf('27',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['9','10'])).

thf('28',plain,(
    ! [X5: $i] :
      ( v4_relat_1 @ ( k6_relat_1 @ X5 ) @ X5 ) ),
    inference(cnf,[status(esa)],[fc11_funct_2])).

thf('29',plain,(
    ! [X8: $i] :
      ( ( k6_partfun1 @ X8 )
      = ( k6_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('30',plain,(
    ! [X5: $i] :
      ( v4_relat_1 @ ( k6_partfun1 @ X5 ) @ X5 ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    v4_relat_1 @ k1_xboole_0 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['27','30'])).

thf('32',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['9','10'])).

thf('33',plain,(
    ! [X6: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc11_funct_2])).

thf('34',plain,(
    ! [X8: $i] :
      ( ( k6_partfun1 @ X8 )
      = ( k6_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('35',plain,(
    ! [X6: $i] :
      ( v1_funct_1 @ ( k6_partfun1 @ X6 ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['32','35'])).

thf('37',plain,
    ( ~ ( v1_yellow_1 @ k1_xboole_0 )
    | ( ( k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0 )
      = ( g1_orders_2 @ ( k1_tarski @ k1_xboole_0 ) @ ( k6_partfun1 @ ( k1_tarski @ k1_xboole_0 ) ) ) ) ),
    inference(demod,[status(thm)],['18','21','26','31','36'])).

thf('38',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k7_funcop_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(fc10_yellow_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( l1_orders_2 @ B )
     => ( v1_yellow_1 @ ( k2_funcop_1 @ A @ B ) ) ) )).

thf('40',plain,(
    ! [X11: $i,X12: $i] :
      ( ( v1_yellow_1 @ ( k2_funcop_1 @ X11 @ X12 ) )
      | ~ ( l1_orders_2 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc10_yellow_1])).

thf('41',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k7_funcop_1 @ X14 @ X15 )
      = ( k2_funcop_1 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_funcop_1])).

thf('42',plain,(
    ! [X11: $i,X12: $i] :
      ( ( v1_yellow_1 @ ( k7_funcop_1 @ X11 @ X12 ) )
      | ~ ( l1_orders_2 @ X12 ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( v1_yellow_1 @ k1_xboole_0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['39','42'])).

thf('44',plain,(
    v1_yellow_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['38','43'])).

thf('45',plain,
    ( ( k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0 )
    = ( g1_orders_2 @ ( k1_tarski @ k1_xboole_0 ) @ ( k6_partfun1 @ ( k1_tarski @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['37','44'])).

thf('46',plain,(
    ( k6_yellow_1 @ k1_xboole_0 @ sk_A )
 != ( k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['7','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( ( k6_yellow_1 @ k1_xboole_0 @ sk_A )
       != ( k6_yellow_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','46'])).

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
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.fCwZG6BIgP
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:37:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.21/0.35  % Python version: Python 3.6.8
% 0.21/0.35  % Running in FO mode
% 0.47/0.66  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.47/0.66  % Solved by: fo/fo7.sh
% 0.47/0.66  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.47/0.66  % done 174 iterations in 0.199s
% 0.47/0.66  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.47/0.66  % SZS output start Refutation
% 0.47/0.66  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.47/0.66  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.47/0.66  thf(g1_orders_2_type, type, g1_orders_2: $i > $i > $i).
% 0.47/0.66  thf(v1_yellow_1_type, type, v1_yellow_1: $i > $o).
% 0.47/0.66  thf(k5_yellow_1_type, type, k5_yellow_1: $i > $i > $i).
% 0.47/0.66  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.47/0.66  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.47/0.66  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.47/0.66  thf(sk_A_type, type, sk_A: $i).
% 0.47/0.66  thf(k6_yellow_1_type, type, k6_yellow_1: $i > $i > $i).
% 0.47/0.66  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.47/0.66  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.47/0.66  thf(k7_funcop_1_type, type, k7_funcop_1: $i > $i > $i).
% 0.47/0.66  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.47/0.66  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.47/0.66  thf(k2_funcop_1_type, type, k2_funcop_1: $i > $i > $i).
% 0.47/0.66  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.47/0.66  thf(fc2_funcop_1, axiom,
% 0.47/0.66    (![A:$i]: ( v1_xboole_0 @ ( k2_funcop_1 @ k1_xboole_0 @ A ) ))).
% 0.47/0.66  thf('0', plain,
% 0.47/0.66      (![X13 : $i]: (v1_xboole_0 @ (k2_funcop_1 @ k1_xboole_0 @ X13))),
% 0.47/0.66      inference('cnf', [status(esa)], [fc2_funcop_1])).
% 0.47/0.66  thf(l13_xboole_0, axiom,
% 0.47/0.66    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.47/0.66  thf('1', plain,
% 0.47/0.66      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.47/0.66      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.47/0.66  thf('2', plain,
% 0.47/0.66      (![X0 : $i]: ((k2_funcop_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.47/0.66      inference('sup-', [status(thm)], ['0', '1'])).
% 0.47/0.66  thf(redefinition_k7_funcop_1, axiom,
% 0.47/0.66    (![A:$i,B:$i]: ( ( k7_funcop_1 @ A @ B ) = ( k2_funcop_1 @ A @ B ) ))).
% 0.47/0.66  thf('3', plain,
% 0.47/0.66      (![X14 : $i, X15 : $i]:
% 0.47/0.66         ((k7_funcop_1 @ X14 @ X15) = (k2_funcop_1 @ X14 @ X15))),
% 0.47/0.66      inference('cnf', [status(esa)], [redefinition_k7_funcop_1])).
% 0.47/0.66  thf('4', plain,
% 0.47/0.66      (![X0 : $i]: ((k7_funcop_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.47/0.66      inference('demod', [status(thm)], ['2', '3'])).
% 0.47/0.66  thf(d5_yellow_1, axiom,
% 0.47/0.66    (![A:$i,B:$i]:
% 0.47/0.66     ( ( l1_orders_2 @ B ) =>
% 0.47/0.66       ( ( k6_yellow_1 @ A @ B ) =
% 0.47/0.66         ( k5_yellow_1 @ A @ ( k7_funcop_1 @ A @ B ) ) ) ))).
% 0.47/0.66  thf('5', plain,
% 0.47/0.66      (![X9 : $i, X10 : $i]:
% 0.47/0.66         (((k6_yellow_1 @ X9 @ X10)
% 0.47/0.66            = (k5_yellow_1 @ X9 @ (k7_funcop_1 @ X9 @ X10)))
% 0.47/0.66          | ~ (l1_orders_2 @ X10))),
% 0.47/0.66      inference('cnf', [status(esa)], [d5_yellow_1])).
% 0.47/0.66  thf('6', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         (((k6_yellow_1 @ k1_xboole_0 @ X0)
% 0.47/0.66            = (k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0))
% 0.47/0.66          | ~ (l1_orders_2 @ X0))),
% 0.47/0.66      inference('sup+', [status(thm)], ['4', '5'])).
% 0.47/0.66  thf(t27_yellow_1, conjecture,
% 0.47/0.66    (![A:$i]:
% 0.47/0.66     ( ( l1_orders_2 @ A ) =>
% 0.47/0.66       ( ( k6_yellow_1 @ k1_xboole_0 @ A ) =
% 0.47/0.66         ( g1_orders_2 @
% 0.47/0.66           ( k1_tarski @ k1_xboole_0 ) @ 
% 0.47/0.66           ( k6_partfun1 @ ( k1_tarski @ k1_xboole_0 ) ) ) ) ))).
% 0.47/0.66  thf(zf_stmt_0, negated_conjecture,
% 0.47/0.66    (~( ![A:$i]:
% 0.47/0.66        ( ( l1_orders_2 @ A ) =>
% 0.47/0.66          ( ( k6_yellow_1 @ k1_xboole_0 @ A ) =
% 0.47/0.66            ( g1_orders_2 @
% 0.47/0.66              ( k1_tarski @ k1_xboole_0 ) @ 
% 0.47/0.66              ( k6_partfun1 @ ( k1_tarski @ k1_xboole_0 ) ) ) ) ) )),
% 0.47/0.66    inference('cnf.neg', [status(esa)], [t27_yellow_1])).
% 0.47/0.66  thf('7', plain,
% 0.47/0.66      (((k6_yellow_1 @ k1_xboole_0 @ sk_A)
% 0.47/0.66         != (g1_orders_2 @ (k1_tarski @ k1_xboole_0) @ 
% 0.47/0.66             (k6_partfun1 @ (k1_tarski @ k1_xboole_0))))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('8', plain,
% 0.47/0.66      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.47/0.66      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.47/0.66  thf(t81_relat_1, axiom, (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.47/0.66  thf('9', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.47/0.66      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.47/0.66  thf(redefinition_k6_partfun1, axiom,
% 0.47/0.66    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.47/0.66  thf('10', plain, (![X8 : $i]: ((k6_partfun1 @ X8) = (k6_relat_1 @ X8))),
% 0.47/0.66      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.47/0.66  thf('11', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.47/0.66      inference('demod', [status(thm)], ['9', '10'])).
% 0.47/0.66  thf('12', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         (((k6_partfun1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.47/0.66      inference('sup+', [status(thm)], ['8', '11'])).
% 0.47/0.66  thf(fc11_funct_2, axiom,
% 0.47/0.66    (![A:$i]:
% 0.47/0.66     ( ( v1_partfun1 @ ( k6_relat_1 @ A ) @ A ) & 
% 0.47/0.66       ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.47/0.66       ( v4_relat_1 @ ( k6_relat_1 @ A ) @ A ) & 
% 0.47/0.66       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.47/0.66  thf('13', plain, (![X7 : $i]: (v1_partfun1 @ (k6_relat_1 @ X7) @ X7)),
% 0.47/0.66      inference('cnf', [status(esa)], [fc11_funct_2])).
% 0.47/0.66  thf('14', plain, (![X8 : $i]: ((k6_partfun1 @ X8) = (k6_relat_1 @ X8))),
% 0.47/0.66      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.47/0.66  thf('15', plain, (![X7 : $i]: (v1_partfun1 @ (k6_partfun1 @ X7) @ X7)),
% 0.47/0.66      inference('demod', [status(thm)], ['13', '14'])).
% 0.47/0.66  thf('16', plain,
% 0.47/0.66      (![X0 : $i]: ((v1_partfun1 @ k1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X0))),
% 0.47/0.66      inference('sup+', [status(thm)], ['12', '15'])).
% 0.47/0.66  thf(t26_yellow_1, axiom,
% 0.47/0.66    (![A:$i]:
% 0.47/0.66     ( ( ( v1_relat_1 @ A ) & ( v4_relat_1 @ A @ k1_xboole_0 ) & 
% 0.47/0.66         ( v1_funct_1 @ A ) & ( v1_partfun1 @ A @ k1_xboole_0 ) & 
% 0.47/0.66         ( v1_yellow_1 @ A ) ) =>
% 0.47/0.66       ( ( k5_yellow_1 @ k1_xboole_0 @ A ) =
% 0.47/0.66         ( g1_orders_2 @
% 0.47/0.66           ( k1_tarski @ k1_xboole_0 ) @ 
% 0.47/0.66           ( k6_partfun1 @ ( k1_tarski @ k1_xboole_0 ) ) ) ) ))).
% 0.47/0.66  thf('17', plain,
% 0.47/0.66      (![X16 : $i]:
% 0.47/0.66         (((k5_yellow_1 @ k1_xboole_0 @ X16)
% 0.47/0.66            = (g1_orders_2 @ (k1_tarski @ k1_xboole_0) @ 
% 0.47/0.66               (k6_partfun1 @ (k1_tarski @ k1_xboole_0))))
% 0.47/0.66          | ~ (v1_yellow_1 @ X16)
% 0.47/0.66          | ~ (v1_partfun1 @ X16 @ k1_xboole_0)
% 0.47/0.66          | ~ (v1_funct_1 @ X16)
% 0.47/0.66          | ~ (v4_relat_1 @ X16 @ k1_xboole_0)
% 0.47/0.66          | ~ (v1_relat_1 @ X16))),
% 0.47/0.66      inference('cnf', [status(esa)], [t26_yellow_1])).
% 0.47/0.66  thf('18', plain,
% 0.47/0.66      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.47/0.66        | ~ (v1_relat_1 @ k1_xboole_0)
% 0.47/0.66        | ~ (v4_relat_1 @ k1_xboole_0 @ k1_xboole_0)
% 0.47/0.66        | ~ (v1_funct_1 @ k1_xboole_0)
% 0.47/0.66        | ~ (v1_yellow_1 @ k1_xboole_0)
% 0.47/0.66        | ((k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0)
% 0.47/0.66            = (g1_orders_2 @ (k1_tarski @ k1_xboole_0) @ 
% 0.47/0.66               (k6_partfun1 @ (k1_tarski @ k1_xboole_0)))))),
% 0.47/0.66      inference('sup-', [status(thm)], ['16', '17'])).
% 0.47/0.66  thf('19', plain,
% 0.47/0.66      (![X13 : $i]: (v1_xboole_0 @ (k2_funcop_1 @ k1_xboole_0 @ X13))),
% 0.47/0.66      inference('cnf', [status(esa)], [fc2_funcop_1])).
% 0.47/0.66  thf('20', plain,
% 0.47/0.66      (![X0 : $i]: ((k2_funcop_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.47/0.66      inference('sup-', [status(thm)], ['0', '1'])).
% 0.47/0.66  thf('21', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.47/0.66      inference('demod', [status(thm)], ['19', '20'])).
% 0.47/0.66  thf('22', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.47/0.66      inference('demod', [status(thm)], ['9', '10'])).
% 0.47/0.66  thf('23', plain, (![X4 : $i]: (v1_relat_1 @ (k6_relat_1 @ X4))),
% 0.47/0.66      inference('cnf', [status(esa)], [fc11_funct_2])).
% 0.47/0.66  thf('24', plain, (![X8 : $i]: ((k6_partfun1 @ X8) = (k6_relat_1 @ X8))),
% 0.47/0.66      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.47/0.66  thf('25', plain, (![X4 : $i]: (v1_relat_1 @ (k6_partfun1 @ X4))),
% 0.47/0.66      inference('demod', [status(thm)], ['23', '24'])).
% 0.47/0.66  thf('26', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.47/0.66      inference('sup+', [status(thm)], ['22', '25'])).
% 0.47/0.66  thf('27', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.47/0.66      inference('demod', [status(thm)], ['9', '10'])).
% 0.47/0.66  thf('28', plain, (![X5 : $i]: (v4_relat_1 @ (k6_relat_1 @ X5) @ X5)),
% 0.47/0.66      inference('cnf', [status(esa)], [fc11_funct_2])).
% 0.47/0.66  thf('29', plain, (![X8 : $i]: ((k6_partfun1 @ X8) = (k6_relat_1 @ X8))),
% 0.47/0.66      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.47/0.66  thf('30', plain, (![X5 : $i]: (v4_relat_1 @ (k6_partfun1 @ X5) @ X5)),
% 0.47/0.66      inference('demod', [status(thm)], ['28', '29'])).
% 0.47/0.66  thf('31', plain, ((v4_relat_1 @ k1_xboole_0 @ k1_xboole_0)),
% 0.47/0.66      inference('sup+', [status(thm)], ['27', '30'])).
% 0.47/0.66  thf('32', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.47/0.66      inference('demod', [status(thm)], ['9', '10'])).
% 0.47/0.66  thf('33', plain, (![X6 : $i]: (v1_funct_1 @ (k6_relat_1 @ X6))),
% 0.47/0.66      inference('cnf', [status(esa)], [fc11_funct_2])).
% 0.47/0.66  thf('34', plain, (![X8 : $i]: ((k6_partfun1 @ X8) = (k6_relat_1 @ X8))),
% 0.47/0.66      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.47/0.66  thf('35', plain, (![X6 : $i]: (v1_funct_1 @ (k6_partfun1 @ X6))),
% 0.47/0.66      inference('demod', [status(thm)], ['33', '34'])).
% 0.47/0.66  thf('36', plain, ((v1_funct_1 @ k1_xboole_0)),
% 0.47/0.66      inference('sup+', [status(thm)], ['32', '35'])).
% 0.47/0.66  thf('37', plain,
% 0.47/0.66      ((~ (v1_yellow_1 @ k1_xboole_0)
% 0.47/0.66        | ((k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0)
% 0.47/0.66            = (g1_orders_2 @ (k1_tarski @ k1_xboole_0) @ 
% 0.47/0.66               (k6_partfun1 @ (k1_tarski @ k1_xboole_0)))))),
% 0.47/0.66      inference('demod', [status(thm)], ['18', '21', '26', '31', '36'])).
% 0.47/0.66  thf('38', plain, ((l1_orders_2 @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('39', plain,
% 0.47/0.66      (![X0 : $i]: ((k7_funcop_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.47/0.66      inference('demod', [status(thm)], ['2', '3'])).
% 0.47/0.66  thf(fc10_yellow_1, axiom,
% 0.47/0.66    (![A:$i,B:$i]:
% 0.47/0.66     ( ( l1_orders_2 @ B ) => ( v1_yellow_1 @ ( k2_funcop_1 @ A @ B ) ) ))).
% 0.47/0.66  thf('40', plain,
% 0.47/0.66      (![X11 : $i, X12 : $i]:
% 0.47/0.66         ((v1_yellow_1 @ (k2_funcop_1 @ X11 @ X12)) | ~ (l1_orders_2 @ X12))),
% 0.47/0.66      inference('cnf', [status(esa)], [fc10_yellow_1])).
% 0.47/0.66  thf('41', plain,
% 0.47/0.66      (![X14 : $i, X15 : $i]:
% 0.47/0.66         ((k7_funcop_1 @ X14 @ X15) = (k2_funcop_1 @ X14 @ X15))),
% 0.47/0.66      inference('cnf', [status(esa)], [redefinition_k7_funcop_1])).
% 0.47/0.66  thf('42', plain,
% 0.47/0.66      (![X11 : $i, X12 : $i]:
% 0.47/0.66         ((v1_yellow_1 @ (k7_funcop_1 @ X11 @ X12)) | ~ (l1_orders_2 @ X12))),
% 0.47/0.66      inference('demod', [status(thm)], ['40', '41'])).
% 0.47/0.66  thf('43', plain,
% 0.47/0.66      (![X0 : $i]: ((v1_yellow_1 @ k1_xboole_0) | ~ (l1_orders_2 @ X0))),
% 0.47/0.66      inference('sup+', [status(thm)], ['39', '42'])).
% 0.47/0.66  thf('44', plain, ((v1_yellow_1 @ k1_xboole_0)),
% 0.47/0.66      inference('sup-', [status(thm)], ['38', '43'])).
% 0.47/0.66  thf('45', plain,
% 0.47/0.66      (((k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0)
% 0.47/0.66         = (g1_orders_2 @ (k1_tarski @ k1_xboole_0) @ 
% 0.47/0.66            (k6_partfun1 @ (k1_tarski @ k1_xboole_0))))),
% 0.47/0.66      inference('demod', [status(thm)], ['37', '44'])).
% 0.47/0.66  thf('46', plain,
% 0.47/0.66      (((k6_yellow_1 @ k1_xboole_0 @ sk_A)
% 0.47/0.66         != (k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0))),
% 0.47/0.66      inference('demod', [status(thm)], ['7', '45'])).
% 0.47/0.66  thf('47', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         (((k6_yellow_1 @ k1_xboole_0 @ sk_A)
% 0.47/0.66            != (k6_yellow_1 @ k1_xboole_0 @ X0))
% 0.47/0.66          | ~ (l1_orders_2 @ X0))),
% 0.47/0.66      inference('sup-', [status(thm)], ['6', '46'])).
% 0.47/0.66  thf('48', plain, (~ (l1_orders_2 @ sk_A)),
% 0.47/0.66      inference('eq_res', [status(thm)], ['47'])).
% 0.47/0.66  thf('49', plain, ((l1_orders_2 @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('50', plain, ($false), inference('demod', [status(thm)], ['48', '49'])).
% 0.47/0.66  
% 0.47/0.66  % SZS output end Refutation
% 0.47/0.66  
% 0.47/0.66  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
