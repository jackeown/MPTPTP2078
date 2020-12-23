%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.96mOmLfGDt

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:26 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 136 expanded)
%              Number of leaves         :   30 (  58 expanded)
%              Depth                    :   12
%              Number of atoms          :  403 ( 727 expanded)
%              Number of equality atoms :   36 (  71 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k6_yellow_1_type,type,(
    k6_yellow_1: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_funcop_1_type,type,(
    k2_funcop_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(g1_orders_2_type,type,(
    g1_orders_2: $i > $i > $i )).

thf(k5_yellow_1_type,type,(
    k5_yellow_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_yellow_1_type,type,(
    v1_yellow_1: $i > $o )).

thf(k7_funcop_1_type,type,(
    k7_funcop_1: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(d5_yellow_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( l1_orders_2 @ B )
     => ( ( k6_yellow_1 @ A @ B )
        = ( k5_yellow_1 @ A @ ( k7_funcop_1 @ A @ B ) ) ) ) )).

thf('0',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k6_yellow_1 @ X15 @ X16 )
        = ( k5_yellow_1 @ X15 @ ( k7_funcop_1 @ X15 @ X16 ) ) )
      | ~ ( l1_orders_2 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d5_yellow_1])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('1',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
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

thf(t81_relat_1,axiom,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('5',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('6',plain,(
    ! [X14: $i] :
      ( ( k6_partfun1 @ X14 )
      = ( k6_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('7',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['5','6'])).

thf(fc11_funct_2,axiom,(
    ! [A: $i] :
      ( ( v1_partfun1 @ ( k6_relat_1 @ A ) @ A )
      & ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v4_relat_1 @ ( k6_relat_1 @ A ) @ A )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('8',plain,(
    ! [X13: $i] :
      ( v1_partfun1 @ ( k6_relat_1 @ X13 ) @ X13 ) ),
    inference(cnf,[status(esa)],[fc11_funct_2])).

thf('9',plain,(
    ! [X14: $i] :
      ( ( k6_partfun1 @ X14 )
      = ( k6_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('10',plain,(
    ! [X13: $i] :
      ( v1_partfun1 @ ( k6_partfun1 @ X13 ) @ X13 ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    v1_partfun1 @ k1_xboole_0 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['7','10'])).

thf(t26_yellow_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v4_relat_1 @ A @ k1_xboole_0 )
        & ( v1_funct_1 @ A )
        & ( v1_partfun1 @ A @ k1_xboole_0 )
        & ( v1_yellow_1 @ A ) )
     => ( ( k5_yellow_1 @ k1_xboole_0 @ A )
        = ( g1_orders_2 @ ( k1_tarski @ k1_xboole_0 ) @ ( k6_partfun1 @ ( k1_tarski @ k1_xboole_0 ) ) ) ) ) )).

thf('12',plain,(
    ! [X22: $i] :
      ( ( ( k5_yellow_1 @ k1_xboole_0 @ X22 )
        = ( g1_orders_2 @ ( k1_tarski @ k1_xboole_0 ) @ ( k6_partfun1 @ ( k1_tarski @ k1_xboole_0 ) ) ) )
      | ~ ( v1_yellow_1 @ X22 )
      | ~ ( v1_partfun1 @ X22 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v4_relat_1 @ X22 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t26_yellow_1])).

thf('13',plain,
    ( ~ ( v1_relat_1 @ k1_xboole_0 )
    | ~ ( v4_relat_1 @ k1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_funct_1 @ k1_xboole_0 )
    | ~ ( v1_yellow_1 @ k1_xboole_0 )
    | ( ( k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0 )
      = ( g1_orders_2 @ ( k1_tarski @ k1_xboole_0 ) @ ( k6_partfun1 @ ( k1_tarski @ k1_xboole_0 ) ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['5','6'])).

thf('15',plain,(
    ! [X10: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc11_funct_2])).

thf('16',plain,(
    ! [X14: $i] :
      ( ( k6_partfun1 @ X14 )
      = ( k6_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('17',plain,(
    ! [X10: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X10 ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['14','17'])).

thf('19',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['5','6'])).

thf('20',plain,(
    ! [X11: $i] :
      ( v4_relat_1 @ ( k6_relat_1 @ X11 ) @ X11 ) ),
    inference(cnf,[status(esa)],[fc11_funct_2])).

thf('21',plain,(
    ! [X14: $i] :
      ( ( k6_partfun1 @ X14 )
      = ( k6_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('22',plain,(
    ! [X11: $i] :
      ( v4_relat_1 @ ( k6_partfun1 @ X11 ) @ X11 ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    v4_relat_1 @ k1_xboole_0 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['19','22'])).

thf('24',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['5','6'])).

thf('25',plain,(
    ! [X12: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc11_funct_2])).

thf('26',plain,(
    ! [X14: $i] :
      ( ( k6_partfun1 @ X14 )
      = ( k6_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('27',plain,(
    ! [X12: $i] :
      ( v1_funct_1 @ ( k6_partfun1 @ X12 ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['24','27'])).

thf('29',plain,
    ( ~ ( v1_yellow_1 @ k1_xboole_0 )
    | ( ( k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0 )
      = ( g1_orders_2 @ ( k1_tarski @ k1_xboole_0 ) @ ( k6_partfun1 @ ( k1_tarski @ k1_xboole_0 ) ) ) ) ),
    inference(demod,[status(thm)],['13','18','23','28'])).

thf('30',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc2_funcop_1,axiom,(
    ! [A: $i] :
      ( v1_xboole_0 @ ( k2_funcop_1 @ k1_xboole_0 @ A ) ) )).

thf('31',plain,(
    ! [X19: $i] :
      ( v1_xboole_0 @ ( k2_funcop_1 @ k1_xboole_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc2_funcop_1])).

thf(redefinition_k7_funcop_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k7_funcop_1 @ A @ B )
      = ( k2_funcop_1 @ A @ B ) ) )).

thf('32',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k7_funcop_1 @ X20 @ X21 )
      = ( k2_funcop_1 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_funcop_1])).

thf('33',plain,(
    ! [X19: $i] :
      ( v1_xboole_0 @ ( k7_funcop_1 @ k1_xboole_0 @ X19 ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k7_funcop_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf(fc10_yellow_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( l1_orders_2 @ B )
     => ( v1_yellow_1 @ ( k2_funcop_1 @ A @ B ) ) ) )).

thf('36',plain,(
    ! [X17: $i,X18: $i] :
      ( ( v1_yellow_1 @ ( k2_funcop_1 @ X17 @ X18 ) )
      | ~ ( l1_orders_2 @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc10_yellow_1])).

thf('37',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k7_funcop_1 @ X20 @ X21 )
      = ( k2_funcop_1 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_funcop_1])).

thf('38',plain,(
    ! [X17: $i,X18: $i] :
      ( ( v1_yellow_1 @ ( k7_funcop_1 @ X17 @ X18 ) )
      | ~ ( l1_orders_2 @ X18 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( v1_yellow_1 @ k1_xboole_0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['35','38'])).

thf('40',plain,(
    v1_yellow_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['30','39'])).

thf('41',plain,
    ( ( k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0 )
    = ( g1_orders_2 @ ( k1_tarski @ k1_xboole_0 ) @ ( k6_partfun1 @ ( k1_tarski @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['29','40'])).

thf('42',plain,(
    ( k6_yellow_1 @ k1_xboole_0 @ sk_A )
 != ( k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['4','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( ( k6_yellow_1 @ k1_xboole_0 @ sk_A )
       != ( k5_yellow_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( ( k6_yellow_1 @ k1_xboole_0 @ sk_A )
       != ( k6_yellow_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v1_xboole_0 @ ( k7_funcop_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['0','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k7_funcop_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('46',plain,(
    ! [X19: $i] :
      ( v1_xboole_0 @ ( k7_funcop_1 @ k1_xboole_0 @ X19 ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k7_funcop_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('48',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( ( k6_yellow_1 @ k1_xboole_0 @ sk_A )
       != ( k6_yellow_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(demod,[status(thm)],['44','45','48'])).

thf('50',plain,(
    ~ ( l1_orders_2 @ sk_A ) ),
    inference(eq_res,[status(thm)],['49'])).

thf('51',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    $false ),
    inference(demod,[status(thm)],['50','51'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.96mOmLfGDt
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:45:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.20/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.48  % Solved by: fo/fo7.sh
% 0.20/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.48  % done 81 iterations in 0.037s
% 0.20/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.48  % SZS output start Refutation
% 0.20/0.48  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.48  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.20/0.48  thf(k6_yellow_1_type, type, k6_yellow_1: $i > $i > $i).
% 0.20/0.48  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.20/0.48  thf(k2_funcop_1_type, type, k2_funcop_1: $i > $i > $i).
% 0.20/0.48  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.48  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.20/0.48  thf(g1_orders_2_type, type, g1_orders_2: $i > $i > $i).
% 0.20/0.48  thf(k5_yellow_1_type, type, k5_yellow_1: $i > $i > $i).
% 0.20/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.48  thf(v1_yellow_1_type, type, v1_yellow_1: $i > $o).
% 0.20/0.48  thf(k7_funcop_1_type, type, k7_funcop_1: $i > $i > $i).
% 0.20/0.48  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.20/0.48  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.20/0.48  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.48  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.20/0.48  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.48  thf(d5_yellow_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( l1_orders_2 @ B ) =>
% 0.20/0.48       ( ( k6_yellow_1 @ A @ B ) =
% 0.20/0.48         ( k5_yellow_1 @ A @ ( k7_funcop_1 @ A @ B ) ) ) ))).
% 0.20/0.48  thf('0', plain,
% 0.20/0.48      (![X15 : $i, X16 : $i]:
% 0.20/0.48         (((k6_yellow_1 @ X15 @ X16)
% 0.20/0.48            = (k5_yellow_1 @ X15 @ (k7_funcop_1 @ X15 @ X16)))
% 0.20/0.48          | ~ (l1_orders_2 @ X16))),
% 0.20/0.48      inference('cnf', [status(esa)], [d5_yellow_1])).
% 0.20/0.48  thf(t7_xboole_0, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.20/0.48          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.20/0.48  thf('1', plain,
% 0.20/0.48      (![X3 : $i]: (((X3) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X3) @ X3))),
% 0.20/0.48      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.20/0.48  thf(d1_xboole_0, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.20/0.48  thf('2', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.20/0.48      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.20/0.48  thf('3', plain,
% 0.20/0.48      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.48  thf(t27_yellow_1, conjecture,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( l1_orders_2 @ A ) =>
% 0.20/0.48       ( ( k6_yellow_1 @ k1_xboole_0 @ A ) =
% 0.20/0.48         ( g1_orders_2 @
% 0.20/0.48           ( k1_tarski @ k1_xboole_0 ) @ 
% 0.20/0.48           ( k6_partfun1 @ ( k1_tarski @ k1_xboole_0 ) ) ) ) ))).
% 0.20/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.48    (~( ![A:$i]:
% 0.20/0.48        ( ( l1_orders_2 @ A ) =>
% 0.20/0.48          ( ( k6_yellow_1 @ k1_xboole_0 @ A ) =
% 0.20/0.48            ( g1_orders_2 @
% 0.20/0.48              ( k1_tarski @ k1_xboole_0 ) @ 
% 0.20/0.48              ( k6_partfun1 @ ( k1_tarski @ k1_xboole_0 ) ) ) ) ) )),
% 0.20/0.48    inference('cnf.neg', [status(esa)], [t27_yellow_1])).
% 0.20/0.48  thf('4', plain,
% 0.20/0.48      (((k6_yellow_1 @ k1_xboole_0 @ sk_A)
% 0.20/0.48         != (g1_orders_2 @ (k1_tarski @ k1_xboole_0) @ 
% 0.20/0.48             (k6_partfun1 @ (k1_tarski @ k1_xboole_0))))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(t81_relat_1, axiom, (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.20/0.48  thf('5', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.48      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.20/0.48  thf(redefinition_k6_partfun1, axiom,
% 0.20/0.48    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.20/0.48  thf('6', plain, (![X14 : $i]: ((k6_partfun1 @ X14) = (k6_relat_1 @ X14))),
% 0.20/0.48      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.20/0.48  thf('7', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.48      inference('demod', [status(thm)], ['5', '6'])).
% 0.20/0.48  thf(fc11_funct_2, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( v1_partfun1 @ ( k6_relat_1 @ A ) @ A ) & 
% 0.20/0.48       ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.20/0.48       ( v4_relat_1 @ ( k6_relat_1 @ A ) @ A ) & 
% 0.20/0.48       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.20/0.48  thf('8', plain, (![X13 : $i]: (v1_partfun1 @ (k6_relat_1 @ X13) @ X13)),
% 0.20/0.48      inference('cnf', [status(esa)], [fc11_funct_2])).
% 0.20/0.48  thf('9', plain, (![X14 : $i]: ((k6_partfun1 @ X14) = (k6_relat_1 @ X14))),
% 0.20/0.48      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.20/0.48  thf('10', plain, (![X13 : $i]: (v1_partfun1 @ (k6_partfun1 @ X13) @ X13)),
% 0.20/0.48      inference('demod', [status(thm)], ['8', '9'])).
% 0.20/0.48  thf('11', plain, ((v1_partfun1 @ k1_xboole_0 @ k1_xboole_0)),
% 0.20/0.48      inference('sup+', [status(thm)], ['7', '10'])).
% 0.20/0.48  thf(t26_yellow_1, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( ( v1_relat_1 @ A ) & ( v4_relat_1 @ A @ k1_xboole_0 ) & 
% 0.20/0.48         ( v1_funct_1 @ A ) & ( v1_partfun1 @ A @ k1_xboole_0 ) & 
% 0.20/0.48         ( v1_yellow_1 @ A ) ) =>
% 0.20/0.48       ( ( k5_yellow_1 @ k1_xboole_0 @ A ) =
% 0.20/0.48         ( g1_orders_2 @
% 0.20/0.48           ( k1_tarski @ k1_xboole_0 ) @ 
% 0.20/0.48           ( k6_partfun1 @ ( k1_tarski @ k1_xboole_0 ) ) ) ) ))).
% 0.20/0.48  thf('12', plain,
% 0.20/0.48      (![X22 : $i]:
% 0.20/0.48         (((k5_yellow_1 @ k1_xboole_0 @ X22)
% 0.20/0.48            = (g1_orders_2 @ (k1_tarski @ k1_xboole_0) @ 
% 0.20/0.48               (k6_partfun1 @ (k1_tarski @ k1_xboole_0))))
% 0.20/0.48          | ~ (v1_yellow_1 @ X22)
% 0.20/0.48          | ~ (v1_partfun1 @ X22 @ k1_xboole_0)
% 0.20/0.48          | ~ (v1_funct_1 @ X22)
% 0.20/0.48          | ~ (v4_relat_1 @ X22 @ k1_xboole_0)
% 0.20/0.48          | ~ (v1_relat_1 @ X22))),
% 0.20/0.48      inference('cnf', [status(esa)], [t26_yellow_1])).
% 0.20/0.48  thf('13', plain,
% 0.20/0.48      ((~ (v1_relat_1 @ k1_xboole_0)
% 0.20/0.48        | ~ (v4_relat_1 @ k1_xboole_0 @ k1_xboole_0)
% 0.20/0.48        | ~ (v1_funct_1 @ k1_xboole_0)
% 0.20/0.48        | ~ (v1_yellow_1 @ k1_xboole_0)
% 0.20/0.48        | ((k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0)
% 0.20/0.48            = (g1_orders_2 @ (k1_tarski @ k1_xboole_0) @ 
% 0.20/0.48               (k6_partfun1 @ (k1_tarski @ k1_xboole_0)))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.48  thf('14', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.48      inference('demod', [status(thm)], ['5', '6'])).
% 0.20/0.48  thf('15', plain, (![X10 : $i]: (v1_relat_1 @ (k6_relat_1 @ X10))),
% 0.20/0.48      inference('cnf', [status(esa)], [fc11_funct_2])).
% 0.20/0.48  thf('16', plain, (![X14 : $i]: ((k6_partfun1 @ X14) = (k6_relat_1 @ X14))),
% 0.20/0.48      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.20/0.48  thf('17', plain, (![X10 : $i]: (v1_relat_1 @ (k6_partfun1 @ X10))),
% 0.20/0.48      inference('demod', [status(thm)], ['15', '16'])).
% 0.20/0.48  thf('18', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.20/0.48      inference('sup+', [status(thm)], ['14', '17'])).
% 0.20/0.48  thf('19', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.48      inference('demod', [status(thm)], ['5', '6'])).
% 0.20/0.48  thf('20', plain, (![X11 : $i]: (v4_relat_1 @ (k6_relat_1 @ X11) @ X11)),
% 0.20/0.48      inference('cnf', [status(esa)], [fc11_funct_2])).
% 0.20/0.48  thf('21', plain, (![X14 : $i]: ((k6_partfun1 @ X14) = (k6_relat_1 @ X14))),
% 0.20/0.48      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.20/0.48  thf('22', plain, (![X11 : $i]: (v4_relat_1 @ (k6_partfun1 @ X11) @ X11)),
% 0.20/0.48      inference('demod', [status(thm)], ['20', '21'])).
% 0.20/0.48  thf('23', plain, ((v4_relat_1 @ k1_xboole_0 @ k1_xboole_0)),
% 0.20/0.48      inference('sup+', [status(thm)], ['19', '22'])).
% 0.20/0.48  thf('24', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.48      inference('demod', [status(thm)], ['5', '6'])).
% 0.20/0.48  thf('25', plain, (![X12 : $i]: (v1_funct_1 @ (k6_relat_1 @ X12))),
% 0.20/0.48      inference('cnf', [status(esa)], [fc11_funct_2])).
% 0.20/0.48  thf('26', plain, (![X14 : $i]: ((k6_partfun1 @ X14) = (k6_relat_1 @ X14))),
% 0.20/0.48      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.20/0.48  thf('27', plain, (![X12 : $i]: (v1_funct_1 @ (k6_partfun1 @ X12))),
% 0.20/0.48      inference('demod', [status(thm)], ['25', '26'])).
% 0.20/0.48  thf('28', plain, ((v1_funct_1 @ k1_xboole_0)),
% 0.20/0.48      inference('sup+', [status(thm)], ['24', '27'])).
% 0.20/0.48  thf('29', plain,
% 0.20/0.48      ((~ (v1_yellow_1 @ k1_xboole_0)
% 0.20/0.48        | ((k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0)
% 0.20/0.48            = (g1_orders_2 @ (k1_tarski @ k1_xboole_0) @ 
% 0.20/0.48               (k6_partfun1 @ (k1_tarski @ k1_xboole_0)))))),
% 0.20/0.48      inference('demod', [status(thm)], ['13', '18', '23', '28'])).
% 0.20/0.48  thf('30', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(fc2_funcop_1, axiom,
% 0.20/0.48    (![A:$i]: ( v1_xboole_0 @ ( k2_funcop_1 @ k1_xboole_0 @ A ) ))).
% 0.20/0.48  thf('31', plain,
% 0.20/0.48      (![X19 : $i]: (v1_xboole_0 @ (k2_funcop_1 @ k1_xboole_0 @ X19))),
% 0.20/0.48      inference('cnf', [status(esa)], [fc2_funcop_1])).
% 0.20/0.48  thf(redefinition_k7_funcop_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]: ( ( k7_funcop_1 @ A @ B ) = ( k2_funcop_1 @ A @ B ) ))).
% 0.20/0.48  thf('32', plain,
% 0.20/0.48      (![X20 : $i, X21 : $i]:
% 0.20/0.48         ((k7_funcop_1 @ X20 @ X21) = (k2_funcop_1 @ X20 @ X21))),
% 0.20/0.48      inference('cnf', [status(esa)], [redefinition_k7_funcop_1])).
% 0.20/0.48  thf('33', plain,
% 0.20/0.48      (![X19 : $i]: (v1_xboole_0 @ (k7_funcop_1 @ k1_xboole_0 @ X19))),
% 0.20/0.48      inference('demod', [status(thm)], ['31', '32'])).
% 0.20/0.48  thf('34', plain,
% 0.20/0.48      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.48  thf('35', plain,
% 0.20/0.48      (![X0 : $i]: ((k7_funcop_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['33', '34'])).
% 0.20/0.48  thf(fc10_yellow_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( l1_orders_2 @ B ) => ( v1_yellow_1 @ ( k2_funcop_1 @ A @ B ) ) ))).
% 0.20/0.48  thf('36', plain,
% 0.20/0.48      (![X17 : $i, X18 : $i]:
% 0.20/0.48         ((v1_yellow_1 @ (k2_funcop_1 @ X17 @ X18)) | ~ (l1_orders_2 @ X18))),
% 0.20/0.48      inference('cnf', [status(esa)], [fc10_yellow_1])).
% 0.20/0.48  thf('37', plain,
% 0.20/0.48      (![X20 : $i, X21 : $i]:
% 0.20/0.48         ((k7_funcop_1 @ X20 @ X21) = (k2_funcop_1 @ X20 @ X21))),
% 0.20/0.48      inference('cnf', [status(esa)], [redefinition_k7_funcop_1])).
% 0.20/0.48  thf('38', plain,
% 0.20/0.48      (![X17 : $i, X18 : $i]:
% 0.20/0.48         ((v1_yellow_1 @ (k7_funcop_1 @ X17 @ X18)) | ~ (l1_orders_2 @ X18))),
% 0.20/0.48      inference('demod', [status(thm)], ['36', '37'])).
% 0.20/0.48  thf('39', plain,
% 0.20/0.48      (![X0 : $i]: ((v1_yellow_1 @ k1_xboole_0) | ~ (l1_orders_2 @ X0))),
% 0.20/0.48      inference('sup+', [status(thm)], ['35', '38'])).
% 0.20/0.48  thf('40', plain, ((v1_yellow_1 @ k1_xboole_0)),
% 0.20/0.48      inference('sup-', [status(thm)], ['30', '39'])).
% 0.20/0.48  thf('41', plain,
% 0.20/0.48      (((k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0)
% 0.20/0.48         = (g1_orders_2 @ (k1_tarski @ k1_xboole_0) @ 
% 0.20/0.48            (k6_partfun1 @ (k1_tarski @ k1_xboole_0))))),
% 0.20/0.48      inference('demod', [status(thm)], ['29', '40'])).
% 0.20/0.48  thf('42', plain,
% 0.20/0.48      (((k6_yellow_1 @ k1_xboole_0 @ sk_A)
% 0.20/0.48         != (k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0))),
% 0.20/0.48      inference('demod', [status(thm)], ['4', '41'])).
% 0.20/0.48  thf('43', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (((k6_yellow_1 @ k1_xboole_0 @ sk_A)
% 0.20/0.48            != (k5_yellow_1 @ k1_xboole_0 @ X0))
% 0.20/0.48          | ~ (v1_xboole_0 @ X0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['3', '42'])).
% 0.20/0.48  thf('44', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (((k6_yellow_1 @ k1_xboole_0 @ sk_A)
% 0.20/0.48            != (k6_yellow_1 @ k1_xboole_0 @ X0))
% 0.20/0.48          | ~ (l1_orders_2 @ X0)
% 0.20/0.48          | ~ (v1_xboole_0 @ (k7_funcop_1 @ k1_xboole_0 @ X0)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['0', '43'])).
% 0.20/0.48  thf('45', plain,
% 0.20/0.48      (![X0 : $i]: ((k7_funcop_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['33', '34'])).
% 0.20/0.48  thf('46', plain,
% 0.20/0.48      (![X19 : $i]: (v1_xboole_0 @ (k7_funcop_1 @ k1_xboole_0 @ X19))),
% 0.20/0.48      inference('demod', [status(thm)], ['31', '32'])).
% 0.20/0.48  thf('47', plain,
% 0.20/0.48      (![X0 : $i]: ((k7_funcop_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['33', '34'])).
% 0.20/0.48  thf('48', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.48      inference('demod', [status(thm)], ['46', '47'])).
% 0.20/0.48  thf('49', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (((k6_yellow_1 @ k1_xboole_0 @ sk_A)
% 0.20/0.48            != (k6_yellow_1 @ k1_xboole_0 @ X0))
% 0.20/0.48          | ~ (l1_orders_2 @ X0))),
% 0.20/0.48      inference('demod', [status(thm)], ['44', '45', '48'])).
% 0.20/0.48  thf('50', plain, (~ (l1_orders_2 @ sk_A)),
% 0.20/0.48      inference('eq_res', [status(thm)], ['49'])).
% 0.20/0.48  thf('51', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('52', plain, ($false), inference('demod', [status(thm)], ['50', '51'])).
% 0.20/0.48  
% 0.20/0.48  % SZS output end Refutation
% 0.20/0.48  
% 0.20/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
