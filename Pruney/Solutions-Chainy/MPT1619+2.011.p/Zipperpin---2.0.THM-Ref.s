%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5UU1zrKmqO

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:25 EST 2020

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 151 expanded)
%              Number of leaves         :   35 (  65 expanded)
%              Depth                    :   15
%              Number of atoms          :  434 ( 758 expanded)
%              Number of equality atoms :   37 (  81 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k7_funcop_1_type,type,(
    k7_funcop_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k6_yellow_1_type,type,(
    k6_yellow_1: $i > $i > $i )).

thf(k5_yellow_1_type,type,(
    k5_yellow_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_yellow_1_type,type,(
    v1_yellow_1: $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_funcop_1_type,type,(
    k2_funcop_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(g1_orders_2_type,type,(
    g1_orders_2: $i > $i > $i )).

thf(d5_yellow_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( l1_orders_2 @ B )
     => ( ( k6_yellow_1 @ A @ B )
        = ( k5_yellow_1 @ A @ ( k7_funcop_1 @ A @ B ) ) ) ) )).

thf('0',plain,(
    ! [X31: $i,X32: $i] :
      ( ( ( k6_yellow_1 @ X31 @ X32 )
        = ( k5_yellow_1 @ X31 @ ( k7_funcop_1 @ X31 @ X32 ) ) )
      | ~ ( l1_orders_2 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d5_yellow_1])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('1',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

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

thf('2',plain,(
    ( k6_yellow_1 @ k1_xboole_0 @ sk_A )
 != ( g1_orders_2 @ ( k1_tarski @ k1_xboole_0 ) @ ( k6_partfun1 @ ( k1_tarski @ k1_xboole_0 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('4',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('5',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X24 ) @ X25 )
      | ( v4_relat_1 @ X24 @ X25 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( v4_relat_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('7',plain,(
    ! [X1: $i] :
      ( r1_tarski @ k1_xboole_0 @ X1 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t81_relat_1,axiom,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('8',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('9',plain,(
    ! [X30: $i] :
      ( ( k6_partfun1 @ X30 )
      = ( k6_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('10',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['8','9'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('11',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('12',plain,(
    ! [X30: $i] :
      ( ( k6_partfun1 @ X30 )
      = ( k6_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('13',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X26 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['10','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( v4_relat_1 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['6','7','14'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('16',plain,(
    ! [X28: $i,X29: $i] :
      ( ( ( k1_relat_1 @ X29 )
       != X28 )
      | ( v1_partfun1 @ X29 @ X28 )
      | ~ ( v4_relat_1 @ X29 @ X28 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('17',plain,(
    ! [X29: $i] :
      ( ~ ( v1_relat_1 @ X29 )
      | ~ ( v4_relat_1 @ X29 @ ( k1_relat_1 @ X29 ) )
      | ( v1_partfun1 @ X29 @ ( k1_relat_1 @ X29 ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,
    ( ( v1_partfun1 @ k1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['15','17'])).

thf('19',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('20',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['10','13'])).

thf('21',plain,(
    v1_partfun1 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( v1_partfun1 @ k1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','21'])).

thf(t26_yellow_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v4_relat_1 @ A @ k1_xboole_0 )
        & ( v1_funct_1 @ A )
        & ( v1_partfun1 @ A @ k1_xboole_0 )
        & ( v1_yellow_1 @ A ) )
     => ( ( k5_yellow_1 @ k1_xboole_0 @ A )
        = ( g1_orders_2 @ ( k1_tarski @ k1_xboole_0 ) @ ( k6_partfun1 @ ( k1_tarski @ k1_xboole_0 ) ) ) ) ) )).

thf('23',plain,(
    ! [X38: $i] :
      ( ( ( k5_yellow_1 @ k1_xboole_0 @ X38 )
        = ( g1_orders_2 @ ( k1_tarski @ k1_xboole_0 ) @ ( k6_partfun1 @ ( k1_tarski @ k1_xboole_0 ) ) ) )
      | ~ ( v1_yellow_1 @ X38 )
      | ~ ( v1_partfun1 @ X38 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( v4_relat_1 @ X38 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t26_yellow_1])).

thf('24',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 )
    | ~ ( v4_relat_1 @ k1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_funct_1 @ k1_xboole_0 )
    | ~ ( v1_yellow_1 @ k1_xboole_0 )
    | ( ( k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0 )
      = ( g1_orders_2 @ ( k1_tarski @ k1_xboole_0 ) @ ( k6_partfun1 @ ( k1_tarski @ k1_xboole_0 ) ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('25',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('26',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['10','13'])).

thf('27',plain,(
    ! [X0: $i] :
      ( v4_relat_1 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['6','7','14'])).

thf('28',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['8','9'])).

thf('29',plain,(
    ! [X27: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('30',plain,(
    ! [X30: $i] :
      ( ( k6_partfun1 @ X30 )
      = ( k6_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('31',plain,(
    ! [X27: $i] :
      ( v1_funct_1 @ ( k6_partfun1 @ X27 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['28','31'])).

thf('33',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc2_funcop_1,axiom,(
    ! [A: $i] :
      ( v1_xboole_0 @ ( k2_funcop_1 @ k1_xboole_0 @ A ) ) )).

thf('34',plain,(
    ! [X35: $i] :
      ( v1_xboole_0 @ ( k2_funcop_1 @ k1_xboole_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[fc2_funcop_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k2_funcop_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf(redefinition_k7_funcop_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k7_funcop_1 @ A @ B )
      = ( k2_funcop_1 @ A @ B ) ) )).

thf('37',plain,(
    ! [X36: $i,X37: $i] :
      ( ( k7_funcop_1 @ X36 @ X37 )
      = ( k2_funcop_1 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_funcop_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k7_funcop_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['36','37'])).

thf(fc10_yellow_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( l1_orders_2 @ B )
     => ( v1_yellow_1 @ ( k2_funcop_1 @ A @ B ) ) ) )).

thf('39',plain,(
    ! [X33: $i,X34: $i] :
      ( ( v1_yellow_1 @ ( k2_funcop_1 @ X33 @ X34 ) )
      | ~ ( l1_orders_2 @ X34 ) ) ),
    inference(cnf,[status(esa)],[fc10_yellow_1])).

thf('40',plain,(
    ! [X36: $i,X37: $i] :
      ( ( k7_funcop_1 @ X36 @ X37 )
      = ( k2_funcop_1 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_funcop_1])).

thf('41',plain,(
    ! [X33: $i,X34: $i] :
      ( ( v1_yellow_1 @ ( k7_funcop_1 @ X33 @ X34 ) )
      | ~ ( l1_orders_2 @ X34 ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( v1_yellow_1 @ k1_xboole_0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['38','41'])).

thf('43',plain,(
    v1_yellow_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['33','42'])).

thf('44',plain,
    ( ( k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0 )
    = ( g1_orders_2 @ ( k1_tarski @ k1_xboole_0 ) @ ( k6_partfun1 @ ( k1_tarski @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['24','25','26','27','32','43'])).

thf('45',plain,(
    ( k6_yellow_1 @ k1_xboole_0 @ sk_A )
 != ( k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['2','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( ( k6_yellow_1 @ k1_xboole_0 @ sk_A )
       != ( k5_yellow_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( ( k6_yellow_1 @ k1_xboole_0 @ sk_A )
       != ( k6_yellow_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v1_xboole_0 @ ( k7_funcop_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['0','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k7_funcop_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('49',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( ( k6_yellow_1 @ k1_xboole_0 @ sk_A )
       != ( k6_yellow_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('51',plain,(
    ~ ( l1_orders_2 @ sk_A ) ),
    inference(eq_res,[status(thm)],['50'])).

thf('52',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    $false ),
    inference(demod,[status(thm)],['51','52'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5UU1zrKmqO
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:01:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.47/0.69  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.47/0.69  % Solved by: fo/fo7.sh
% 0.47/0.69  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.47/0.69  % done 229 iterations in 0.228s
% 0.47/0.69  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.47/0.69  % SZS output start Refutation
% 0.47/0.69  thf(sk_A_type, type, sk_A: $i).
% 0.47/0.69  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.47/0.69  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.47/0.69  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.47/0.69  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.47/0.69  thf(k7_funcop_1_type, type, k7_funcop_1: $i > $i > $i).
% 0.47/0.69  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.47/0.69  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.47/0.69  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.47/0.69  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.47/0.69  thf(k6_yellow_1_type, type, k6_yellow_1: $i > $i > $i).
% 0.47/0.69  thf(k5_yellow_1_type, type, k5_yellow_1: $i > $i > $i).
% 0.47/0.69  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.47/0.69  thf(v1_yellow_1_type, type, v1_yellow_1: $i > $o).
% 0.47/0.69  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.47/0.69  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.47/0.69  thf(k2_funcop_1_type, type, k2_funcop_1: $i > $i > $i).
% 0.47/0.69  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.47/0.69  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.47/0.69  thf(g1_orders_2_type, type, g1_orders_2: $i > $i > $i).
% 0.47/0.69  thf(d5_yellow_1, axiom,
% 0.47/0.69    (![A:$i,B:$i]:
% 0.47/0.69     ( ( l1_orders_2 @ B ) =>
% 0.47/0.69       ( ( k6_yellow_1 @ A @ B ) =
% 0.47/0.69         ( k5_yellow_1 @ A @ ( k7_funcop_1 @ A @ B ) ) ) ))).
% 0.47/0.69  thf('0', plain,
% 0.47/0.69      (![X31 : $i, X32 : $i]:
% 0.47/0.69         (((k6_yellow_1 @ X31 @ X32)
% 0.47/0.69            = (k5_yellow_1 @ X31 @ (k7_funcop_1 @ X31 @ X32)))
% 0.47/0.69          | ~ (l1_orders_2 @ X32))),
% 0.47/0.69      inference('cnf', [status(esa)], [d5_yellow_1])).
% 0.47/0.69  thf(l13_xboole_0, axiom,
% 0.47/0.69    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.47/0.69  thf('1', plain,
% 0.47/0.69      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.47/0.69      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.47/0.69  thf(t27_yellow_1, conjecture,
% 0.47/0.69    (![A:$i]:
% 0.47/0.69     ( ( l1_orders_2 @ A ) =>
% 0.47/0.69       ( ( k6_yellow_1 @ k1_xboole_0 @ A ) =
% 0.47/0.69         ( g1_orders_2 @
% 0.47/0.69           ( k1_tarski @ k1_xboole_0 ) @ 
% 0.47/0.69           ( k6_partfun1 @ ( k1_tarski @ k1_xboole_0 ) ) ) ) ))).
% 0.47/0.69  thf(zf_stmt_0, negated_conjecture,
% 0.47/0.69    (~( ![A:$i]:
% 0.47/0.69        ( ( l1_orders_2 @ A ) =>
% 0.47/0.69          ( ( k6_yellow_1 @ k1_xboole_0 @ A ) =
% 0.47/0.69            ( g1_orders_2 @
% 0.47/0.69              ( k1_tarski @ k1_xboole_0 ) @ 
% 0.47/0.69              ( k6_partfun1 @ ( k1_tarski @ k1_xboole_0 ) ) ) ) ) )),
% 0.47/0.69    inference('cnf.neg', [status(esa)], [t27_yellow_1])).
% 0.47/0.69  thf('2', plain,
% 0.47/0.69      (((k6_yellow_1 @ k1_xboole_0 @ sk_A)
% 0.47/0.69         != (g1_orders_2 @ (k1_tarski @ k1_xboole_0) @ 
% 0.47/0.69             (k6_partfun1 @ (k1_tarski @ k1_xboole_0))))),
% 0.47/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.69  thf('3', plain,
% 0.47/0.69      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.47/0.69      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.47/0.69  thf(t60_relat_1, axiom,
% 0.47/0.69    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.47/0.69     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.47/0.69  thf('4', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.47/0.69      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.47/0.69  thf(d18_relat_1, axiom,
% 0.47/0.69    (![A:$i,B:$i]:
% 0.47/0.69     ( ( v1_relat_1 @ B ) =>
% 0.47/0.69       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.47/0.69  thf('5', plain,
% 0.47/0.69      (![X24 : $i, X25 : $i]:
% 0.47/0.69         (~ (r1_tarski @ (k1_relat_1 @ X24) @ X25)
% 0.47/0.69          | (v4_relat_1 @ X24 @ X25)
% 0.47/0.69          | ~ (v1_relat_1 @ X24))),
% 0.47/0.69      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.47/0.69  thf('6', plain,
% 0.47/0.69      (![X0 : $i]:
% 0.47/0.69         (~ (r1_tarski @ k1_xboole_0 @ X0)
% 0.47/0.69          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.47/0.69          | (v4_relat_1 @ k1_xboole_0 @ X0))),
% 0.47/0.69      inference('sup-', [status(thm)], ['4', '5'])).
% 0.47/0.69  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.47/0.69  thf('7', plain, (![X1 : $i]: (r1_tarski @ k1_xboole_0 @ X1)),
% 0.47/0.69      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.47/0.69  thf(t81_relat_1, axiom, (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.47/0.69  thf('8', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.47/0.69      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.47/0.69  thf(redefinition_k6_partfun1, axiom,
% 0.47/0.69    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.47/0.69  thf('9', plain, (![X30 : $i]: ((k6_partfun1 @ X30) = (k6_relat_1 @ X30))),
% 0.47/0.69      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.47/0.69  thf('10', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.47/0.69      inference('demod', [status(thm)], ['8', '9'])).
% 0.47/0.69  thf(fc3_funct_1, axiom,
% 0.47/0.69    (![A:$i]:
% 0.47/0.69     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.47/0.69       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.47/0.69  thf('11', plain, (![X26 : $i]: (v1_relat_1 @ (k6_relat_1 @ X26))),
% 0.47/0.69      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.47/0.69  thf('12', plain, (![X30 : $i]: ((k6_partfun1 @ X30) = (k6_relat_1 @ X30))),
% 0.47/0.69      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.47/0.69  thf('13', plain, (![X26 : $i]: (v1_relat_1 @ (k6_partfun1 @ X26))),
% 0.47/0.69      inference('demod', [status(thm)], ['11', '12'])).
% 0.47/0.69  thf('14', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.47/0.69      inference('sup+', [status(thm)], ['10', '13'])).
% 0.47/0.69  thf('15', plain, (![X0 : $i]: (v4_relat_1 @ k1_xboole_0 @ X0)),
% 0.47/0.69      inference('demod', [status(thm)], ['6', '7', '14'])).
% 0.47/0.69  thf(d4_partfun1, axiom,
% 0.47/0.69    (![A:$i,B:$i]:
% 0.47/0.69     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.47/0.69       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 0.47/0.69  thf('16', plain,
% 0.47/0.69      (![X28 : $i, X29 : $i]:
% 0.47/0.69         (((k1_relat_1 @ X29) != (X28))
% 0.47/0.69          | (v1_partfun1 @ X29 @ X28)
% 0.47/0.69          | ~ (v4_relat_1 @ X29 @ X28)
% 0.47/0.69          | ~ (v1_relat_1 @ X29))),
% 0.47/0.69      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.47/0.69  thf('17', plain,
% 0.47/0.69      (![X29 : $i]:
% 0.47/0.69         (~ (v1_relat_1 @ X29)
% 0.47/0.69          | ~ (v4_relat_1 @ X29 @ (k1_relat_1 @ X29))
% 0.47/0.69          | (v1_partfun1 @ X29 @ (k1_relat_1 @ X29)))),
% 0.47/0.69      inference('simplify', [status(thm)], ['16'])).
% 0.47/0.69  thf('18', plain,
% 0.47/0.69      (((v1_partfun1 @ k1_xboole_0 @ (k1_relat_1 @ k1_xboole_0))
% 0.47/0.69        | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.47/0.69      inference('sup-', [status(thm)], ['15', '17'])).
% 0.47/0.69  thf('19', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.47/0.69      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.47/0.69  thf('20', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.47/0.69      inference('sup+', [status(thm)], ['10', '13'])).
% 0.47/0.69  thf('21', plain, ((v1_partfun1 @ k1_xboole_0 @ k1_xboole_0)),
% 0.47/0.69      inference('demod', [status(thm)], ['18', '19', '20'])).
% 0.47/0.69  thf('22', plain,
% 0.47/0.69      (![X0 : $i]: ((v1_partfun1 @ k1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X0))),
% 0.47/0.69      inference('sup+', [status(thm)], ['3', '21'])).
% 0.47/0.69  thf(t26_yellow_1, axiom,
% 0.47/0.69    (![A:$i]:
% 0.47/0.69     ( ( ( v1_relat_1 @ A ) & ( v4_relat_1 @ A @ k1_xboole_0 ) & 
% 0.47/0.69         ( v1_funct_1 @ A ) & ( v1_partfun1 @ A @ k1_xboole_0 ) & 
% 0.47/0.69         ( v1_yellow_1 @ A ) ) =>
% 0.47/0.69       ( ( k5_yellow_1 @ k1_xboole_0 @ A ) =
% 0.47/0.69         ( g1_orders_2 @
% 0.47/0.69           ( k1_tarski @ k1_xboole_0 ) @ 
% 0.47/0.69           ( k6_partfun1 @ ( k1_tarski @ k1_xboole_0 ) ) ) ) ))).
% 0.47/0.69  thf('23', plain,
% 0.47/0.69      (![X38 : $i]:
% 0.47/0.69         (((k5_yellow_1 @ k1_xboole_0 @ X38)
% 0.47/0.69            = (g1_orders_2 @ (k1_tarski @ k1_xboole_0) @ 
% 0.47/0.69               (k6_partfun1 @ (k1_tarski @ k1_xboole_0))))
% 0.47/0.69          | ~ (v1_yellow_1 @ X38)
% 0.47/0.69          | ~ (v1_partfun1 @ X38 @ k1_xboole_0)
% 0.47/0.69          | ~ (v1_funct_1 @ X38)
% 0.47/0.69          | ~ (v4_relat_1 @ X38 @ k1_xboole_0)
% 0.47/0.69          | ~ (v1_relat_1 @ X38))),
% 0.47/0.69      inference('cnf', [status(esa)], [t26_yellow_1])).
% 0.47/0.69  thf('24', plain,
% 0.47/0.69      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.47/0.69        | ~ (v1_relat_1 @ k1_xboole_0)
% 0.47/0.69        | ~ (v4_relat_1 @ k1_xboole_0 @ k1_xboole_0)
% 0.47/0.69        | ~ (v1_funct_1 @ k1_xboole_0)
% 0.47/0.69        | ~ (v1_yellow_1 @ k1_xboole_0)
% 0.47/0.69        | ((k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0)
% 0.47/0.69            = (g1_orders_2 @ (k1_tarski @ k1_xboole_0) @ 
% 0.47/0.69               (k6_partfun1 @ (k1_tarski @ k1_xboole_0)))))),
% 0.47/0.69      inference('sup-', [status(thm)], ['22', '23'])).
% 0.47/0.69  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.47/0.69  thf('25', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.47/0.69      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.47/0.69  thf('26', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.47/0.69      inference('sup+', [status(thm)], ['10', '13'])).
% 0.47/0.69  thf('27', plain, (![X0 : $i]: (v4_relat_1 @ k1_xboole_0 @ X0)),
% 0.47/0.69      inference('demod', [status(thm)], ['6', '7', '14'])).
% 0.47/0.69  thf('28', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.47/0.69      inference('demod', [status(thm)], ['8', '9'])).
% 0.47/0.69  thf('29', plain, (![X27 : $i]: (v1_funct_1 @ (k6_relat_1 @ X27))),
% 0.47/0.69      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.47/0.69  thf('30', plain, (![X30 : $i]: ((k6_partfun1 @ X30) = (k6_relat_1 @ X30))),
% 0.47/0.69      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.47/0.69  thf('31', plain, (![X27 : $i]: (v1_funct_1 @ (k6_partfun1 @ X27))),
% 0.47/0.69      inference('demod', [status(thm)], ['29', '30'])).
% 0.47/0.69  thf('32', plain, ((v1_funct_1 @ k1_xboole_0)),
% 0.47/0.69      inference('sup+', [status(thm)], ['28', '31'])).
% 0.47/0.69  thf('33', plain, ((l1_orders_2 @ sk_A)),
% 0.47/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.69  thf(fc2_funcop_1, axiom,
% 0.47/0.69    (![A:$i]: ( v1_xboole_0 @ ( k2_funcop_1 @ k1_xboole_0 @ A ) ))).
% 0.47/0.69  thf('34', plain,
% 0.47/0.69      (![X35 : $i]: (v1_xboole_0 @ (k2_funcop_1 @ k1_xboole_0 @ X35))),
% 0.47/0.69      inference('cnf', [status(esa)], [fc2_funcop_1])).
% 0.47/0.69  thf('35', plain,
% 0.47/0.69      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.47/0.69      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.47/0.69  thf('36', plain,
% 0.47/0.69      (![X0 : $i]: ((k2_funcop_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.47/0.69      inference('sup-', [status(thm)], ['34', '35'])).
% 0.47/0.69  thf(redefinition_k7_funcop_1, axiom,
% 0.47/0.69    (![A:$i,B:$i]: ( ( k7_funcop_1 @ A @ B ) = ( k2_funcop_1 @ A @ B ) ))).
% 0.47/0.69  thf('37', plain,
% 0.47/0.69      (![X36 : $i, X37 : $i]:
% 0.47/0.69         ((k7_funcop_1 @ X36 @ X37) = (k2_funcop_1 @ X36 @ X37))),
% 0.47/0.69      inference('cnf', [status(esa)], [redefinition_k7_funcop_1])).
% 0.47/0.69  thf('38', plain,
% 0.47/0.69      (![X0 : $i]: ((k7_funcop_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.47/0.69      inference('demod', [status(thm)], ['36', '37'])).
% 0.47/0.69  thf(fc10_yellow_1, axiom,
% 0.47/0.69    (![A:$i,B:$i]:
% 0.47/0.69     ( ( l1_orders_2 @ B ) => ( v1_yellow_1 @ ( k2_funcop_1 @ A @ B ) ) ))).
% 0.47/0.69  thf('39', plain,
% 0.47/0.69      (![X33 : $i, X34 : $i]:
% 0.47/0.69         ((v1_yellow_1 @ (k2_funcop_1 @ X33 @ X34)) | ~ (l1_orders_2 @ X34))),
% 0.47/0.69      inference('cnf', [status(esa)], [fc10_yellow_1])).
% 0.47/0.69  thf('40', plain,
% 0.47/0.69      (![X36 : $i, X37 : $i]:
% 0.47/0.69         ((k7_funcop_1 @ X36 @ X37) = (k2_funcop_1 @ X36 @ X37))),
% 0.47/0.69      inference('cnf', [status(esa)], [redefinition_k7_funcop_1])).
% 0.47/0.69  thf('41', plain,
% 0.47/0.69      (![X33 : $i, X34 : $i]:
% 0.47/0.69         ((v1_yellow_1 @ (k7_funcop_1 @ X33 @ X34)) | ~ (l1_orders_2 @ X34))),
% 0.47/0.69      inference('demod', [status(thm)], ['39', '40'])).
% 0.47/0.69  thf('42', plain,
% 0.47/0.69      (![X0 : $i]: ((v1_yellow_1 @ k1_xboole_0) | ~ (l1_orders_2 @ X0))),
% 0.47/0.69      inference('sup+', [status(thm)], ['38', '41'])).
% 0.47/0.69  thf('43', plain, ((v1_yellow_1 @ k1_xboole_0)),
% 0.47/0.69      inference('sup-', [status(thm)], ['33', '42'])).
% 0.47/0.69  thf('44', plain,
% 0.47/0.69      (((k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0)
% 0.47/0.69         = (g1_orders_2 @ (k1_tarski @ k1_xboole_0) @ 
% 0.47/0.69            (k6_partfun1 @ (k1_tarski @ k1_xboole_0))))),
% 0.47/0.69      inference('demod', [status(thm)], ['24', '25', '26', '27', '32', '43'])).
% 0.47/0.69  thf('45', plain,
% 0.47/0.69      (((k6_yellow_1 @ k1_xboole_0 @ sk_A)
% 0.47/0.69         != (k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0))),
% 0.47/0.69      inference('demod', [status(thm)], ['2', '44'])).
% 0.47/0.69  thf('46', plain,
% 0.47/0.69      (![X0 : $i]:
% 0.47/0.69         (((k6_yellow_1 @ k1_xboole_0 @ sk_A)
% 0.47/0.69            != (k5_yellow_1 @ k1_xboole_0 @ X0))
% 0.47/0.69          | ~ (v1_xboole_0 @ X0))),
% 0.47/0.69      inference('sup-', [status(thm)], ['1', '45'])).
% 0.47/0.69  thf('47', plain,
% 0.47/0.69      (![X0 : $i]:
% 0.47/0.69         (((k6_yellow_1 @ k1_xboole_0 @ sk_A)
% 0.47/0.69            != (k6_yellow_1 @ k1_xboole_0 @ X0))
% 0.47/0.69          | ~ (l1_orders_2 @ X0)
% 0.47/0.69          | ~ (v1_xboole_0 @ (k7_funcop_1 @ k1_xboole_0 @ X0)))),
% 0.47/0.69      inference('sup-', [status(thm)], ['0', '46'])).
% 0.47/0.69  thf('48', plain,
% 0.47/0.69      (![X0 : $i]: ((k7_funcop_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.47/0.69      inference('demod', [status(thm)], ['36', '37'])).
% 0.47/0.69  thf('49', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.47/0.69      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.47/0.69  thf('50', plain,
% 0.47/0.69      (![X0 : $i]:
% 0.47/0.69         (((k6_yellow_1 @ k1_xboole_0 @ sk_A)
% 0.47/0.69            != (k6_yellow_1 @ k1_xboole_0 @ X0))
% 0.47/0.69          | ~ (l1_orders_2 @ X0))),
% 0.47/0.69      inference('demod', [status(thm)], ['47', '48', '49'])).
% 0.47/0.69  thf('51', plain, (~ (l1_orders_2 @ sk_A)),
% 0.47/0.69      inference('eq_res', [status(thm)], ['50'])).
% 0.47/0.69  thf('52', plain, ((l1_orders_2 @ sk_A)),
% 0.47/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.69  thf('53', plain, ($false), inference('demod', [status(thm)], ['51', '52'])).
% 0.47/0.69  
% 0.47/0.69  % SZS output end Refutation
% 0.47/0.69  
% 0.47/0.70  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
