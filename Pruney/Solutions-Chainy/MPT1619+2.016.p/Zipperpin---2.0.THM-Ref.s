%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.x5MLjKluuO

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:26 EST 2020

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 118 expanded)
%              Number of leaves         :   43 (  59 expanded)
%              Depth                    :   10
%              Number of atoms          :  430 ( 566 expanded)
%              Number of equality atoms :   36 (  53 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k7_funcop_1_type,type,(
    k7_funcop_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k2_funcop_1_type,type,(
    k2_funcop_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(g1_orders_2_type,type,(
    g1_orders_2: $i > $i > $i )).

thf(v1_orders_2_type,type,(
    v1_orders_2: $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k5_yellow_1_type,type,(
    k5_yellow_1: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_1_type,type,(
    sk_A_1: $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k6_yellow_1_type,type,(
    k6_yellow_1: $i > $i > $i )).

thf(v1_yellow_1_type,type,(
    v1_yellow_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v7_struct_0_type,type,(
    v7_struct_0: $i > $o )).

thf(fc2_funcop_1,axiom,(
    ! [A: $i] :
      ( v1_xboole_0 @ ( k2_funcop_1 @ k1_xboole_0 @ A ) ) )).

thf('0',plain,(
    ! [X41: $i] :
      ( v1_xboole_0 @ ( k2_funcop_1 @ k1_xboole_0 @ X41 ) ) ),
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
    ! [X42: $i,X43: $i] :
      ( ( k7_funcop_1 @ X42 @ X43 )
      = ( k2_funcop_1 @ X42 @ X43 ) ) ),
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
    ! [X37: $i,X38: $i] :
      ( ( ( k6_yellow_1 @ X37 @ X38 )
        = ( k5_yellow_1 @ X37 @ ( k7_funcop_1 @ X37 @ X38 ) ) )
      | ~ ( l1_orders_2 @ X38 ) ) ),
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
    ( k6_yellow_1 @ k1_xboole_0 @ sk_A_1 )
 != ( g1_orders_2 @ ( k1_tarski @ k1_xboole_0 ) @ ( k6_partfun1 @ ( k1_tarski @ k1_xboole_0 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('8',plain,(
    ! [X36: $i] :
      ( ( k6_partfun1 @ X36 )
      = ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('9',plain,(
    ( k6_yellow_1 @ k1_xboole_0 @ sk_A_1 )
 != ( g1_orders_2 @ ( k1_tarski @ k1_xboole_0 ) @ ( k6_relat_1 @ ( k1_tarski @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t81_relat_1,axiom,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('11',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( ( k6_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('13',plain,(
    ! [X34: $i] :
      ( v1_partfun1 @ ( k6_partfun1 @ X34 ) @ X34 ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('14',plain,(
    ! [X36: $i] :
      ( ( k6_partfun1 @ X36 )
      = ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('15',plain,(
    ! [X34: $i] :
      ( v1_partfun1 @ ( k6_relat_1 @ X34 ) @ X34 ) ),
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
    ! [X44: $i] :
      ( ( ( k5_yellow_1 @ k1_xboole_0 @ X44 )
        = ( g1_orders_2 @ ( k1_tarski @ k1_xboole_0 ) @ ( k6_partfun1 @ ( k1_tarski @ k1_xboole_0 ) ) ) )
      | ~ ( v1_yellow_1 @ X44 )
      | ~ ( v1_partfun1 @ X44 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ X44 )
      | ~ ( v4_relat_1 @ X44 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t26_yellow_1])).

thf('18',plain,(
    ! [X36: $i] :
      ( ( k6_partfun1 @ X36 )
      = ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('19',plain,(
    ! [X44: $i] :
      ( ( ( k5_yellow_1 @ k1_xboole_0 @ X44 )
        = ( g1_orders_2 @ ( k1_tarski @ k1_xboole_0 ) @ ( k6_relat_1 @ ( k1_tarski @ k1_xboole_0 ) ) ) )
      | ~ ( v1_yellow_1 @ X44 )
      | ~ ( v1_partfun1 @ X44 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ X44 )
      | ~ ( v4_relat_1 @ X44 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X44 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 )
    | ~ ( v4_relat_1 @ k1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_funct_1 @ k1_xboole_0 )
    | ~ ( v1_yellow_1 @ k1_xboole_0 )
    | ( ( k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0 )
      = ( g1_orders_2 @ ( k1_tarski @ k1_xboole_0 ) @ ( k6_relat_1 @ ( k1_tarski @ k1_xboole_0 ) ) ) ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('21',plain,(
    ! [X41: $i] :
      ( v1_xboole_0 @ ( k2_funcop_1 @ k1_xboole_0 @ X41 ) ) ),
    inference(cnf,[status(esa)],[fc2_funcop_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k2_funcop_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('23',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('25',plain,(
    ! [X32: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('26',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['24','25'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('27',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('28',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X30 ) @ X31 )
      | ( v4_relat_1 @ X30 @ X31 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( v4_relat_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('30',plain,(
    ! [X1: $i] :
      ( r1_tarski @ k1_xboole_0 @ X1 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('31',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['24','25'])).

thf('32',plain,(
    ! [X0: $i] :
      ( v4_relat_1 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('33',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf('34',plain,(
    ! [X33: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('35',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['33','34'])).

thf(rc1_yellow_0,axiom,(
    ? [A: $i] :
      ( ( v3_orders_2 @ A )
      & ( v1_orders_2 @ A )
      & ( v7_struct_0 @ A )
      & ~ ( v2_struct_0 @ A )
      & ( l1_orders_2 @ A ) ) )).

thf('36',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[rc1_yellow_0])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k7_funcop_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(fc10_yellow_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( l1_orders_2 @ B )
     => ( v1_yellow_1 @ ( k2_funcop_1 @ A @ B ) ) ) )).

thf('38',plain,(
    ! [X39: $i,X40: $i] :
      ( ( v1_yellow_1 @ ( k2_funcop_1 @ X39 @ X40 ) )
      | ~ ( l1_orders_2 @ X40 ) ) ),
    inference(cnf,[status(esa)],[fc10_yellow_1])).

thf('39',plain,(
    ! [X42: $i,X43: $i] :
      ( ( k7_funcop_1 @ X42 @ X43 )
      = ( k2_funcop_1 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_funcop_1])).

thf('40',plain,(
    ! [X39: $i,X40: $i] :
      ( ( v1_yellow_1 @ ( k7_funcop_1 @ X39 @ X40 ) )
      | ~ ( l1_orders_2 @ X40 ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( v1_yellow_1 @ k1_xboole_0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['37','40'])).

thf('42',plain,(
    v1_yellow_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['36','41'])).

thf('43',plain,
    ( ( k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0 )
    = ( g1_orders_2 @ ( k1_tarski @ k1_xboole_0 ) @ ( k6_relat_1 @ ( k1_tarski @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['20','23','26','32','35','42'])).

thf('44',plain,(
    ( k6_yellow_1 @ k1_xboole_0 @ sk_A_1 )
 != ( k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['9','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( ( k6_yellow_1 @ k1_xboole_0 @ sk_A_1 )
       != ( k6_yellow_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','44'])).

thf('46',plain,(
    ~ ( l1_orders_2 @ sk_A_1 ) ),
    inference(eq_res,[status(thm)],['45'])).

thf('47',plain,(
    l1_orders_2 @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    $false ),
    inference(demod,[status(thm)],['46','47'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.x5MLjKluuO
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:51:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.20/0.34  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.47/0.68  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.47/0.68  % Solved by: fo/fo7.sh
% 0.47/0.68  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.47/0.68  % done 211 iterations in 0.228s
% 0.47/0.68  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.47/0.68  % SZS output start Refutation
% 0.47/0.68  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.47/0.68  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.47/0.68  thf(k7_funcop_1_type, type, k7_funcop_1: $i > $i > $i).
% 0.47/0.68  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.47/0.68  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.47/0.68  thf(sk_A_type, type, sk_A: $i).
% 0.47/0.68  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.47/0.68  thf(k2_funcop_1_type, type, k2_funcop_1: $i > $i > $i).
% 0.47/0.68  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.47/0.68  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.47/0.68  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.47/0.68  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.47/0.68  thf(g1_orders_2_type, type, g1_orders_2: $i > $i > $i).
% 0.47/0.68  thf(v1_orders_2_type, type, v1_orders_2: $i > $o).
% 0.47/0.68  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.47/0.68  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.47/0.68  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.47/0.68  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.47/0.68  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.47/0.68  thf(k5_yellow_1_type, type, k5_yellow_1: $i > $i > $i).
% 0.47/0.68  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.47/0.68  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.47/0.68  thf(sk_A_1_type, type, sk_A_1: $i).
% 0.47/0.68  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.47/0.68  thf(k6_yellow_1_type, type, k6_yellow_1: $i > $i > $i).
% 0.47/0.68  thf(v1_yellow_1_type, type, v1_yellow_1: $i > $o).
% 0.47/0.68  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.47/0.68  thf(v7_struct_0_type, type, v7_struct_0: $i > $o).
% 0.47/0.68  thf(fc2_funcop_1, axiom,
% 0.47/0.68    (![A:$i]: ( v1_xboole_0 @ ( k2_funcop_1 @ k1_xboole_0 @ A ) ))).
% 0.47/0.68  thf('0', plain,
% 0.47/0.68      (![X41 : $i]: (v1_xboole_0 @ (k2_funcop_1 @ k1_xboole_0 @ X41))),
% 0.47/0.68      inference('cnf', [status(esa)], [fc2_funcop_1])).
% 0.47/0.68  thf(l13_xboole_0, axiom,
% 0.47/0.68    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.47/0.68  thf('1', plain,
% 0.47/0.68      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.47/0.68      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.47/0.68  thf('2', plain,
% 0.47/0.68      (![X0 : $i]: ((k2_funcop_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.47/0.68      inference('sup-', [status(thm)], ['0', '1'])).
% 0.47/0.68  thf(redefinition_k7_funcop_1, axiom,
% 0.47/0.68    (![A:$i,B:$i]: ( ( k7_funcop_1 @ A @ B ) = ( k2_funcop_1 @ A @ B ) ))).
% 0.47/0.68  thf('3', plain,
% 0.47/0.68      (![X42 : $i, X43 : $i]:
% 0.47/0.68         ((k7_funcop_1 @ X42 @ X43) = (k2_funcop_1 @ X42 @ X43))),
% 0.47/0.68      inference('cnf', [status(esa)], [redefinition_k7_funcop_1])).
% 0.47/0.68  thf('4', plain,
% 0.47/0.68      (![X0 : $i]: ((k7_funcop_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.47/0.68      inference('demod', [status(thm)], ['2', '3'])).
% 0.47/0.68  thf(d5_yellow_1, axiom,
% 0.47/0.68    (![A:$i,B:$i]:
% 0.47/0.68     ( ( l1_orders_2 @ B ) =>
% 0.47/0.68       ( ( k6_yellow_1 @ A @ B ) =
% 0.47/0.68         ( k5_yellow_1 @ A @ ( k7_funcop_1 @ A @ B ) ) ) ))).
% 0.47/0.68  thf('5', plain,
% 0.47/0.68      (![X37 : $i, X38 : $i]:
% 0.47/0.68         (((k6_yellow_1 @ X37 @ X38)
% 0.47/0.68            = (k5_yellow_1 @ X37 @ (k7_funcop_1 @ X37 @ X38)))
% 0.47/0.68          | ~ (l1_orders_2 @ X38))),
% 0.47/0.68      inference('cnf', [status(esa)], [d5_yellow_1])).
% 0.47/0.68  thf('6', plain,
% 0.47/0.68      (![X0 : $i]:
% 0.47/0.68         (((k6_yellow_1 @ k1_xboole_0 @ X0)
% 0.47/0.68            = (k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0))
% 0.47/0.68          | ~ (l1_orders_2 @ X0))),
% 0.47/0.68      inference('sup+', [status(thm)], ['4', '5'])).
% 0.47/0.68  thf(t27_yellow_1, conjecture,
% 0.47/0.68    (![A:$i]:
% 0.47/0.68     ( ( l1_orders_2 @ A ) =>
% 0.47/0.68       ( ( k6_yellow_1 @ k1_xboole_0 @ A ) =
% 0.47/0.68         ( g1_orders_2 @
% 0.47/0.68           ( k1_tarski @ k1_xboole_0 ) @ 
% 0.47/0.68           ( k6_partfun1 @ ( k1_tarski @ k1_xboole_0 ) ) ) ) ))).
% 0.47/0.68  thf(zf_stmt_0, negated_conjecture,
% 0.47/0.68    (~( ![A:$i]:
% 0.47/0.68        ( ( l1_orders_2 @ A ) =>
% 0.47/0.68          ( ( k6_yellow_1 @ k1_xboole_0 @ A ) =
% 0.47/0.68            ( g1_orders_2 @
% 0.47/0.68              ( k1_tarski @ k1_xboole_0 ) @ 
% 0.47/0.68              ( k6_partfun1 @ ( k1_tarski @ k1_xboole_0 ) ) ) ) ) )),
% 0.47/0.68    inference('cnf.neg', [status(esa)], [t27_yellow_1])).
% 0.47/0.68  thf('7', plain,
% 0.47/0.68      (((k6_yellow_1 @ k1_xboole_0 @ sk_A_1)
% 0.47/0.68         != (g1_orders_2 @ (k1_tarski @ k1_xboole_0) @ 
% 0.47/0.68             (k6_partfun1 @ (k1_tarski @ k1_xboole_0))))),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf(redefinition_k6_partfun1, axiom,
% 0.47/0.68    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.47/0.68  thf('8', plain, (![X36 : $i]: ((k6_partfun1 @ X36) = (k6_relat_1 @ X36))),
% 0.47/0.68      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.47/0.68  thf('9', plain,
% 0.47/0.68      (((k6_yellow_1 @ k1_xboole_0 @ sk_A_1)
% 0.47/0.68         != (g1_orders_2 @ (k1_tarski @ k1_xboole_0) @ 
% 0.47/0.68             (k6_relat_1 @ (k1_tarski @ k1_xboole_0))))),
% 0.47/0.68      inference('demod', [status(thm)], ['7', '8'])).
% 0.47/0.68  thf('10', plain,
% 0.47/0.68      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.47/0.68      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.47/0.68  thf(t81_relat_1, axiom, (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.47/0.68  thf('11', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.47/0.68      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.47/0.68  thf('12', plain,
% 0.47/0.68      (![X0 : $i]: (((k6_relat_1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.47/0.68      inference('sup+', [status(thm)], ['10', '11'])).
% 0.47/0.68  thf(dt_k6_partfun1, axiom,
% 0.47/0.68    (![A:$i]:
% 0.47/0.68     ( ( m1_subset_1 @
% 0.47/0.68         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 0.47/0.68       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 0.47/0.68  thf('13', plain, (![X34 : $i]: (v1_partfun1 @ (k6_partfun1 @ X34) @ X34)),
% 0.47/0.68      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.47/0.68  thf('14', plain, (![X36 : $i]: ((k6_partfun1 @ X36) = (k6_relat_1 @ X36))),
% 0.47/0.68      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.47/0.68  thf('15', plain, (![X34 : $i]: (v1_partfun1 @ (k6_relat_1 @ X34) @ X34)),
% 0.47/0.68      inference('demod', [status(thm)], ['13', '14'])).
% 0.47/0.68  thf('16', plain,
% 0.47/0.68      (![X0 : $i]: ((v1_partfun1 @ k1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X0))),
% 0.47/0.68      inference('sup+', [status(thm)], ['12', '15'])).
% 0.47/0.68  thf(t26_yellow_1, axiom,
% 0.47/0.68    (![A:$i]:
% 0.47/0.68     ( ( ( v1_relat_1 @ A ) & ( v4_relat_1 @ A @ k1_xboole_0 ) & 
% 0.47/0.68         ( v1_funct_1 @ A ) & ( v1_partfun1 @ A @ k1_xboole_0 ) & 
% 0.47/0.68         ( v1_yellow_1 @ A ) ) =>
% 0.47/0.68       ( ( k5_yellow_1 @ k1_xboole_0 @ A ) =
% 0.47/0.68         ( g1_orders_2 @
% 0.47/0.68           ( k1_tarski @ k1_xboole_0 ) @ 
% 0.47/0.68           ( k6_partfun1 @ ( k1_tarski @ k1_xboole_0 ) ) ) ) ))).
% 0.47/0.68  thf('17', plain,
% 0.47/0.68      (![X44 : $i]:
% 0.47/0.68         (((k5_yellow_1 @ k1_xboole_0 @ X44)
% 0.47/0.68            = (g1_orders_2 @ (k1_tarski @ k1_xboole_0) @ 
% 0.47/0.68               (k6_partfun1 @ (k1_tarski @ k1_xboole_0))))
% 0.47/0.68          | ~ (v1_yellow_1 @ X44)
% 0.47/0.68          | ~ (v1_partfun1 @ X44 @ k1_xboole_0)
% 0.47/0.68          | ~ (v1_funct_1 @ X44)
% 0.47/0.68          | ~ (v4_relat_1 @ X44 @ k1_xboole_0)
% 0.47/0.68          | ~ (v1_relat_1 @ X44))),
% 0.47/0.68      inference('cnf', [status(esa)], [t26_yellow_1])).
% 0.47/0.68  thf('18', plain, (![X36 : $i]: ((k6_partfun1 @ X36) = (k6_relat_1 @ X36))),
% 0.47/0.68      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.47/0.68  thf('19', plain,
% 0.47/0.68      (![X44 : $i]:
% 0.47/0.68         (((k5_yellow_1 @ k1_xboole_0 @ X44)
% 0.47/0.68            = (g1_orders_2 @ (k1_tarski @ k1_xboole_0) @ 
% 0.47/0.68               (k6_relat_1 @ (k1_tarski @ k1_xboole_0))))
% 0.47/0.68          | ~ (v1_yellow_1 @ X44)
% 0.47/0.68          | ~ (v1_partfun1 @ X44 @ k1_xboole_0)
% 0.47/0.68          | ~ (v1_funct_1 @ X44)
% 0.47/0.68          | ~ (v4_relat_1 @ X44 @ k1_xboole_0)
% 0.47/0.68          | ~ (v1_relat_1 @ X44))),
% 0.47/0.68      inference('demod', [status(thm)], ['17', '18'])).
% 0.47/0.68  thf('20', plain,
% 0.47/0.68      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.47/0.68        | ~ (v1_relat_1 @ k1_xboole_0)
% 0.47/0.68        | ~ (v4_relat_1 @ k1_xboole_0 @ k1_xboole_0)
% 0.47/0.68        | ~ (v1_funct_1 @ k1_xboole_0)
% 0.47/0.68        | ~ (v1_yellow_1 @ k1_xboole_0)
% 0.47/0.68        | ((k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0)
% 0.47/0.68            = (g1_orders_2 @ (k1_tarski @ k1_xboole_0) @ 
% 0.47/0.68               (k6_relat_1 @ (k1_tarski @ k1_xboole_0)))))),
% 0.47/0.68      inference('sup-', [status(thm)], ['16', '19'])).
% 0.47/0.68  thf('21', plain,
% 0.47/0.68      (![X41 : $i]: (v1_xboole_0 @ (k2_funcop_1 @ k1_xboole_0 @ X41))),
% 0.47/0.68      inference('cnf', [status(esa)], [fc2_funcop_1])).
% 0.47/0.68  thf('22', plain,
% 0.47/0.68      (![X0 : $i]: ((k2_funcop_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.47/0.68      inference('sup-', [status(thm)], ['0', '1'])).
% 0.47/0.68  thf('23', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.47/0.68      inference('demod', [status(thm)], ['21', '22'])).
% 0.47/0.68  thf('24', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.47/0.68      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.47/0.68  thf(fc3_funct_1, axiom,
% 0.47/0.68    (![A:$i]:
% 0.47/0.68     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.47/0.68       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.47/0.68  thf('25', plain, (![X32 : $i]: (v1_relat_1 @ (k6_relat_1 @ X32))),
% 0.47/0.68      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.47/0.68  thf('26', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.47/0.68      inference('sup+', [status(thm)], ['24', '25'])).
% 0.47/0.68  thf(t60_relat_1, axiom,
% 0.47/0.68    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.47/0.68     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.47/0.68  thf('27', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.47/0.68      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.47/0.68  thf(d18_relat_1, axiom,
% 0.47/0.68    (![A:$i,B:$i]:
% 0.47/0.68     ( ( v1_relat_1 @ B ) =>
% 0.47/0.68       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.47/0.68  thf('28', plain,
% 0.47/0.68      (![X30 : $i, X31 : $i]:
% 0.47/0.68         (~ (r1_tarski @ (k1_relat_1 @ X30) @ X31)
% 0.47/0.68          | (v4_relat_1 @ X30 @ X31)
% 0.47/0.68          | ~ (v1_relat_1 @ X30))),
% 0.47/0.68      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.47/0.68  thf('29', plain,
% 0.47/0.68      (![X0 : $i]:
% 0.47/0.68         (~ (r1_tarski @ k1_xboole_0 @ X0)
% 0.47/0.68          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.47/0.68          | (v4_relat_1 @ k1_xboole_0 @ X0))),
% 0.47/0.68      inference('sup-', [status(thm)], ['27', '28'])).
% 0.47/0.68  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.47/0.68  thf('30', plain, (![X1 : $i]: (r1_tarski @ k1_xboole_0 @ X1)),
% 0.47/0.68      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.47/0.68  thf('31', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.47/0.68      inference('sup+', [status(thm)], ['24', '25'])).
% 0.47/0.68  thf('32', plain, (![X0 : $i]: (v4_relat_1 @ k1_xboole_0 @ X0)),
% 0.47/0.68      inference('demod', [status(thm)], ['29', '30', '31'])).
% 0.47/0.68  thf('33', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.47/0.68      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.47/0.68  thf('34', plain, (![X33 : $i]: (v1_funct_1 @ (k6_relat_1 @ X33))),
% 0.47/0.68      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.47/0.68  thf('35', plain, ((v1_funct_1 @ k1_xboole_0)),
% 0.47/0.68      inference('sup+', [status(thm)], ['33', '34'])).
% 0.47/0.68  thf(rc1_yellow_0, axiom,
% 0.47/0.68    (?[A:$i]:
% 0.47/0.68     ( ( v3_orders_2 @ A ) & ( v1_orders_2 @ A ) & ( v7_struct_0 @ A ) & 
% 0.47/0.68       ( ~( v2_struct_0 @ A ) ) & ( l1_orders_2 @ A ) ))).
% 0.47/0.68  thf('36', plain, ((l1_orders_2 @ sk_A)),
% 0.47/0.68      inference('cnf', [status(esa)], [rc1_yellow_0])).
% 0.47/0.68  thf('37', plain,
% 0.47/0.68      (![X0 : $i]: ((k7_funcop_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.47/0.68      inference('demod', [status(thm)], ['2', '3'])).
% 0.47/0.68  thf(fc10_yellow_1, axiom,
% 0.47/0.68    (![A:$i,B:$i]:
% 0.47/0.68     ( ( l1_orders_2 @ B ) => ( v1_yellow_1 @ ( k2_funcop_1 @ A @ B ) ) ))).
% 0.47/0.68  thf('38', plain,
% 0.47/0.68      (![X39 : $i, X40 : $i]:
% 0.47/0.68         ((v1_yellow_1 @ (k2_funcop_1 @ X39 @ X40)) | ~ (l1_orders_2 @ X40))),
% 0.47/0.68      inference('cnf', [status(esa)], [fc10_yellow_1])).
% 0.47/0.68  thf('39', plain,
% 0.47/0.68      (![X42 : $i, X43 : $i]:
% 0.47/0.68         ((k7_funcop_1 @ X42 @ X43) = (k2_funcop_1 @ X42 @ X43))),
% 0.47/0.68      inference('cnf', [status(esa)], [redefinition_k7_funcop_1])).
% 0.47/0.68  thf('40', plain,
% 0.47/0.68      (![X39 : $i, X40 : $i]:
% 0.47/0.68         ((v1_yellow_1 @ (k7_funcop_1 @ X39 @ X40)) | ~ (l1_orders_2 @ X40))),
% 0.47/0.68      inference('demod', [status(thm)], ['38', '39'])).
% 0.47/0.68  thf('41', plain,
% 0.47/0.68      (![X0 : $i]: ((v1_yellow_1 @ k1_xboole_0) | ~ (l1_orders_2 @ X0))),
% 0.47/0.68      inference('sup+', [status(thm)], ['37', '40'])).
% 0.47/0.68  thf('42', plain, ((v1_yellow_1 @ k1_xboole_0)),
% 0.47/0.68      inference('sup-', [status(thm)], ['36', '41'])).
% 0.47/0.68  thf('43', plain,
% 0.47/0.68      (((k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0)
% 0.47/0.68         = (g1_orders_2 @ (k1_tarski @ k1_xboole_0) @ 
% 0.47/0.68            (k6_relat_1 @ (k1_tarski @ k1_xboole_0))))),
% 0.47/0.68      inference('demod', [status(thm)], ['20', '23', '26', '32', '35', '42'])).
% 0.47/0.68  thf('44', plain,
% 0.47/0.68      (((k6_yellow_1 @ k1_xboole_0 @ sk_A_1)
% 0.47/0.68         != (k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0))),
% 0.47/0.68      inference('demod', [status(thm)], ['9', '43'])).
% 0.47/0.68  thf('45', plain,
% 0.47/0.68      (![X0 : $i]:
% 0.47/0.68         (((k6_yellow_1 @ k1_xboole_0 @ sk_A_1)
% 0.47/0.68            != (k6_yellow_1 @ k1_xboole_0 @ X0))
% 0.47/0.68          | ~ (l1_orders_2 @ X0))),
% 0.47/0.68      inference('sup-', [status(thm)], ['6', '44'])).
% 0.47/0.68  thf('46', plain, (~ (l1_orders_2 @ sk_A_1)),
% 0.47/0.68      inference('eq_res', [status(thm)], ['45'])).
% 0.47/0.68  thf('47', plain, ((l1_orders_2 @ sk_A_1)),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('48', plain, ($false), inference('demod', [status(thm)], ['46', '47'])).
% 0.47/0.68  
% 0.47/0.68  % SZS output end Refutation
% 0.47/0.68  
% 0.47/0.69  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
