%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.sql5O7EamZ

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:27 EST 2020

% Result     : Theorem 0.14s
% Output     : Refutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 121 expanded)
%              Number of leaves         :   34 (  55 expanded)
%              Depth                    :   12
%              Number of atoms          :  407 ( 652 expanded)
%              Number of equality atoms :   33 (  59 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k7_funcop_1_type,type,(
    k7_funcop_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k5_yellow_1_type,type,(
    k5_yellow_1: $i > $i > $i )).

thf(v5_ordinal1_type,type,(
    v5_ordinal1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(g1_orders_2_type,type,(
    g1_orders_2: $i > $i > $i )).

thf(v1_yellow_1_type,type,(
    v1_yellow_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k6_yellow_1_type,type,(
    k6_yellow_1: $i > $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k2_funcop_1_type,type,(
    k2_funcop_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(fc2_funcop_1,axiom,(
    ! [A: $i] :
      ( v1_xboole_0 @ ( k2_funcop_1 @ k1_xboole_0 @ A ) ) )).

thf('0',plain,(
    ! [X39: $i] :
      ( v1_xboole_0 @ ( k2_funcop_1 @ k1_xboole_0 @ X39 ) ) ),
    inference(cnf,[status(esa)],[fc2_funcop_1])).

thf(redefinition_k7_funcop_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k7_funcop_1 @ A @ B )
      = ( k2_funcop_1 @ A @ B ) ) )).

thf('1',plain,(
    ! [X40: $i,X41: $i] :
      ( ( k7_funcop_1 @ X40 @ X41 )
      = ( k2_funcop_1 @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_funcop_1])).

thf('2',plain,(
    ! [X39: $i] :
      ( v1_xboole_0 @ ( k7_funcop_1 @ k1_xboole_0 @ X39 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('3',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k7_funcop_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(d5_yellow_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( l1_orders_2 @ B )
     => ( ( k6_yellow_1 @ A @ B )
        = ( k5_yellow_1 @ A @ ( k7_funcop_1 @ A @ B ) ) ) ) )).

thf('5',plain,(
    ! [X35: $i,X36: $i] :
      ( ( ( k6_yellow_1 @ X35 @ X36 )
        = ( k5_yellow_1 @ X35 @ ( k7_funcop_1 @ X35 @ X36 ) ) )
      | ~ ( l1_orders_2 @ X36 ) ) ),
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

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('8',plain,(
    ! [X34: $i] :
      ( ( k6_partfun1 @ X34 )
      = ( k6_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('9',plain,(
    ( k6_yellow_1 @ k1_xboole_0 @ sk_A )
 != ( g1_orders_2 @ ( k1_tarski @ k1_xboole_0 ) @ ( k6_relat_1 @ ( k1_tarski @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k7_funcop_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(fc10_yellow_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( l1_orders_2 @ B )
     => ( v1_yellow_1 @ ( k2_funcop_1 @ A @ B ) ) ) )).

thf('13',plain,(
    ! [X37: $i,X38: $i] :
      ( ( v1_yellow_1 @ ( k2_funcop_1 @ X37 @ X38 ) )
      | ~ ( l1_orders_2 @ X38 ) ) ),
    inference(cnf,[status(esa)],[fc10_yellow_1])).

thf('14',plain,(
    ! [X40: $i,X41: $i] :
      ( ( k7_funcop_1 @ X40 @ X41 )
      = ( k2_funcop_1 @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_funcop_1])).

thf('15',plain,(
    ! [X37: $i,X38: $i] :
      ( ( v1_yellow_1 @ ( k7_funcop_1 @ X37 @ X38 ) )
      | ~ ( l1_orders_2 @ X38 ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( v1_yellow_1 @ k1_xboole_0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_yellow_1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( l1_orders_2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['11','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_yellow_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t81_relat_1,axiom,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('20',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( ( k6_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('22',plain,(
    ! [X32: $i] :
      ( v1_partfun1 @ ( k6_partfun1 @ X32 ) @ X32 ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('23',plain,(
    ! [X34: $i] :
      ( ( k6_partfun1 @ X34 )
      = ( k6_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('24',plain,(
    ! [X32: $i] :
      ( v1_partfun1 @ ( k6_relat_1 @ X32 ) @ X32 ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( v1_partfun1 @ k1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['21','24'])).

thf(t26_yellow_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v4_relat_1 @ A @ k1_xboole_0 )
        & ( v1_funct_1 @ A )
        & ( v1_partfun1 @ A @ k1_xboole_0 )
        & ( v1_yellow_1 @ A ) )
     => ( ( k5_yellow_1 @ k1_xboole_0 @ A )
        = ( g1_orders_2 @ ( k1_tarski @ k1_xboole_0 ) @ ( k6_partfun1 @ ( k1_tarski @ k1_xboole_0 ) ) ) ) ) )).

thf('26',plain,(
    ! [X42: $i] :
      ( ( ( k5_yellow_1 @ k1_xboole_0 @ X42 )
        = ( g1_orders_2 @ ( k1_tarski @ k1_xboole_0 ) @ ( k6_partfun1 @ ( k1_tarski @ k1_xboole_0 ) ) ) )
      | ~ ( v1_yellow_1 @ X42 )
      | ~ ( v1_partfun1 @ X42 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ X42 )
      | ~ ( v4_relat_1 @ X42 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t26_yellow_1])).

thf('27',plain,(
    ! [X34: $i] :
      ( ( k6_partfun1 @ X34 )
      = ( k6_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('28',plain,(
    ! [X42: $i] :
      ( ( ( k5_yellow_1 @ k1_xboole_0 @ X42 )
        = ( g1_orders_2 @ ( k1_tarski @ k1_xboole_0 ) @ ( k6_relat_1 @ ( k1_tarski @ k1_xboole_0 ) ) ) )
      | ~ ( v1_yellow_1 @ X42 )
      | ~ ( v1_partfun1 @ X42 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ X42 )
      | ~ ( v4_relat_1 @ X42 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X42 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 )
    | ~ ( v4_relat_1 @ k1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_funct_1 @ k1_xboole_0 )
    | ~ ( v1_yellow_1 @ k1_xboole_0 )
    | ( ( k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0 )
      = ( g1_orders_2 @ ( k1_tarski @ k1_xboole_0 ) @ ( k6_relat_1 @ ( k1_tarski @ k1_xboole_0 ) ) ) ) ),
    inference('sup-',[status(thm)],['25','28'])).

thf('30',plain,(
    ! [X39: $i] :
      ( v1_xboole_0 @ ( k7_funcop_1 @ k1_xboole_0 @ X39 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k7_funcop_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('32',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['30','31'])).

thf(t45_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v5_ordinal1 @ k1_xboole_0 )
      & ( v1_funct_1 @ k1_xboole_0 )
      & ( v5_relat_1 @ k1_xboole_0 @ A )
      & ( v1_relat_1 @ k1_xboole_0 ) ) )).

thf('33',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[t45_ordinal1])).

thf(l222_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v5_relat_1 @ k1_xboole_0 @ B )
      & ( v4_relat_1 @ k1_xboole_0 @ A ) ) )).

thf('34',plain,(
    ! [X30: $i] :
      ( v4_relat_1 @ k1_xboole_0 @ X30 ) ),
    inference(cnf,[status(esa)],[l222_relat_1])).

thf('35',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[t45_ordinal1])).

thf('36',plain,
    ( ~ ( v1_yellow_1 @ k1_xboole_0 )
    | ( ( k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0 )
      = ( g1_orders_2 @ ( k1_tarski @ k1_xboole_0 ) @ ( k6_relat_1 @ ( k1_tarski @ k1_xboole_0 ) ) ) ) ),
    inference(demod,[status(thm)],['29','32','33','34','35'])).

thf('37',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( ( k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0 )
      = ( g1_orders_2 @ ( k1_tarski @ k1_xboole_0 ) @ ( k6_relat_1 @ ( k1_tarski @ k1_xboole_0 ) ) ) ) ),
    inference('sup-',[status(thm)],['18','36'])).

thf('38',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['30','31'])).

thf('39',plain,
    ( ( k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0 )
    = ( g1_orders_2 @ ( k1_tarski @ k1_xboole_0 ) @ ( k6_relat_1 @ ( k1_tarski @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ( k6_yellow_1 @ k1_xboole_0 @ sk_A )
 != ( k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['9','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( ( k6_yellow_1 @ k1_xboole_0 @ sk_A )
       != ( k6_yellow_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','40'])).

thf('42',plain,(
    ~ ( l1_orders_2 @ sk_A ) ),
    inference(eq_res,[status(thm)],['41'])).

thf('43',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    $false ),
    inference(demod,[status(thm)],['42','43'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.09  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.10  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.sql5O7EamZ
% 0.09/0.29  % Computer   : n019.cluster.edu
% 0.09/0.29  % Model      : x86_64 x86_64
% 0.09/0.29  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.09/0.29  % Memory     : 8042.1875MB
% 0.09/0.29  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.09/0.29  % CPULimit   : 60
% 0.09/0.29  % DateTime   : Tue Dec  1 14:29:52 EST 2020
% 0.09/0.29  % CPUTime    : 
% 0.09/0.29  % Running portfolio for 600 s
% 0.09/0.29  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.09/0.29  % Number of cores: 8
% 0.09/0.29  % Python version: Python 3.6.8
% 0.09/0.29  % Running in FO mode
% 0.14/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.14/0.49  % Solved by: fo/fo7.sh
% 0.14/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.14/0.49  % done 173 iterations in 0.131s
% 0.14/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.14/0.49  % SZS output start Refutation
% 0.14/0.49  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.14/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.14/0.49  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.14/0.49  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.14/0.49  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.14/0.49  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.14/0.49  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.14/0.49  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.14/0.49  thf(k7_funcop_1_type, type, k7_funcop_1: $i > $i > $i).
% 0.14/0.49  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.14/0.49  thf(k5_yellow_1_type, type, k5_yellow_1: $i > $i > $i).
% 0.14/0.49  thf(v5_ordinal1_type, type, v5_ordinal1: $i > $o).
% 0.14/0.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.14/0.49  thf(g1_orders_2_type, type, g1_orders_2: $i > $i > $i).
% 0.14/0.49  thf(v1_yellow_1_type, type, v1_yellow_1: $i > $o).
% 0.14/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.14/0.49  thf(k6_yellow_1_type, type, k6_yellow_1: $i > $i > $i).
% 0.14/0.49  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.14/0.49  thf(k2_funcop_1_type, type, k2_funcop_1: $i > $i > $i).
% 0.14/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.14/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.14/0.49  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.14/0.49  thf(fc2_funcop_1, axiom,
% 0.14/0.49    (![A:$i]: ( v1_xboole_0 @ ( k2_funcop_1 @ k1_xboole_0 @ A ) ))).
% 0.14/0.49  thf('0', plain,
% 0.14/0.49      (![X39 : $i]: (v1_xboole_0 @ (k2_funcop_1 @ k1_xboole_0 @ X39))),
% 0.14/0.49      inference('cnf', [status(esa)], [fc2_funcop_1])).
% 0.14/0.49  thf(redefinition_k7_funcop_1, axiom,
% 0.14/0.49    (![A:$i,B:$i]: ( ( k7_funcop_1 @ A @ B ) = ( k2_funcop_1 @ A @ B ) ))).
% 0.14/0.49  thf('1', plain,
% 0.14/0.49      (![X40 : $i, X41 : $i]:
% 0.14/0.49         ((k7_funcop_1 @ X40 @ X41) = (k2_funcop_1 @ X40 @ X41))),
% 0.14/0.49      inference('cnf', [status(esa)], [redefinition_k7_funcop_1])).
% 0.14/0.49  thf('2', plain,
% 0.14/0.49      (![X39 : $i]: (v1_xboole_0 @ (k7_funcop_1 @ k1_xboole_0 @ X39))),
% 0.14/0.49      inference('demod', [status(thm)], ['0', '1'])).
% 0.14/0.49  thf(l13_xboole_0, axiom,
% 0.14/0.49    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.14/0.49  thf('3', plain,
% 0.14/0.49      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.14/0.49      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.14/0.49  thf('4', plain,
% 0.14/0.49      (![X0 : $i]: ((k7_funcop_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.14/0.49      inference('sup-', [status(thm)], ['2', '3'])).
% 0.14/0.49  thf(d5_yellow_1, axiom,
% 0.14/0.49    (![A:$i,B:$i]:
% 0.14/0.49     ( ( l1_orders_2 @ B ) =>
% 0.14/0.49       ( ( k6_yellow_1 @ A @ B ) =
% 0.14/0.49         ( k5_yellow_1 @ A @ ( k7_funcop_1 @ A @ B ) ) ) ))).
% 0.14/0.49  thf('5', plain,
% 0.14/0.49      (![X35 : $i, X36 : $i]:
% 0.14/0.49         (((k6_yellow_1 @ X35 @ X36)
% 0.14/0.49            = (k5_yellow_1 @ X35 @ (k7_funcop_1 @ X35 @ X36)))
% 0.14/0.49          | ~ (l1_orders_2 @ X36))),
% 0.14/0.49      inference('cnf', [status(esa)], [d5_yellow_1])).
% 0.14/0.49  thf('6', plain,
% 0.14/0.49      (![X0 : $i]:
% 0.14/0.49         (((k6_yellow_1 @ k1_xboole_0 @ X0)
% 0.14/0.49            = (k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0))
% 0.14/0.49          | ~ (l1_orders_2 @ X0))),
% 0.14/0.49      inference('sup+', [status(thm)], ['4', '5'])).
% 0.14/0.49  thf(t27_yellow_1, conjecture,
% 0.14/0.49    (![A:$i]:
% 0.14/0.49     ( ( l1_orders_2 @ A ) =>
% 0.14/0.49       ( ( k6_yellow_1 @ k1_xboole_0 @ A ) =
% 0.14/0.49         ( g1_orders_2 @
% 0.14/0.49           ( k1_tarski @ k1_xboole_0 ) @ 
% 0.14/0.49           ( k6_partfun1 @ ( k1_tarski @ k1_xboole_0 ) ) ) ) ))).
% 0.14/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.14/0.49    (~( ![A:$i]:
% 0.14/0.49        ( ( l1_orders_2 @ A ) =>
% 0.14/0.49          ( ( k6_yellow_1 @ k1_xboole_0 @ A ) =
% 0.14/0.49            ( g1_orders_2 @
% 0.14/0.49              ( k1_tarski @ k1_xboole_0 ) @ 
% 0.14/0.49              ( k6_partfun1 @ ( k1_tarski @ k1_xboole_0 ) ) ) ) ) )),
% 0.14/0.49    inference('cnf.neg', [status(esa)], [t27_yellow_1])).
% 0.14/0.49  thf('7', plain,
% 0.14/0.49      (((k6_yellow_1 @ k1_xboole_0 @ sk_A)
% 0.14/0.49         != (g1_orders_2 @ (k1_tarski @ k1_xboole_0) @ 
% 0.14/0.49             (k6_partfun1 @ (k1_tarski @ k1_xboole_0))))),
% 0.14/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.14/0.49  thf(redefinition_k6_partfun1, axiom,
% 0.14/0.49    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.14/0.49  thf('8', plain, (![X34 : $i]: ((k6_partfun1 @ X34) = (k6_relat_1 @ X34))),
% 0.14/0.49      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.14/0.49  thf('9', plain,
% 0.14/0.49      (((k6_yellow_1 @ k1_xboole_0 @ sk_A)
% 0.14/0.49         != (g1_orders_2 @ (k1_tarski @ k1_xboole_0) @ 
% 0.14/0.49             (k6_relat_1 @ (k1_tarski @ k1_xboole_0))))),
% 0.14/0.49      inference('demod', [status(thm)], ['7', '8'])).
% 0.14/0.49  thf('10', plain, ((l1_orders_2 @ sk_A)),
% 0.14/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.14/0.49  thf('11', plain,
% 0.14/0.49      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.14/0.49      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.14/0.49  thf('12', plain,
% 0.14/0.49      (![X0 : $i]: ((k7_funcop_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.14/0.49      inference('sup-', [status(thm)], ['2', '3'])).
% 0.14/0.49  thf(fc10_yellow_1, axiom,
% 0.14/0.49    (![A:$i,B:$i]:
% 0.14/0.49     ( ( l1_orders_2 @ B ) => ( v1_yellow_1 @ ( k2_funcop_1 @ A @ B ) ) ))).
% 0.14/0.49  thf('13', plain,
% 0.14/0.49      (![X37 : $i, X38 : $i]:
% 0.14/0.49         ((v1_yellow_1 @ (k2_funcop_1 @ X37 @ X38)) | ~ (l1_orders_2 @ X38))),
% 0.14/0.49      inference('cnf', [status(esa)], [fc10_yellow_1])).
% 0.14/0.49  thf('14', plain,
% 0.14/0.49      (![X40 : $i, X41 : $i]:
% 0.14/0.49         ((k7_funcop_1 @ X40 @ X41) = (k2_funcop_1 @ X40 @ X41))),
% 0.14/0.49      inference('cnf', [status(esa)], [redefinition_k7_funcop_1])).
% 0.14/0.49  thf('15', plain,
% 0.14/0.49      (![X37 : $i, X38 : $i]:
% 0.14/0.49         ((v1_yellow_1 @ (k7_funcop_1 @ X37 @ X38)) | ~ (l1_orders_2 @ X38))),
% 0.14/0.49      inference('demod', [status(thm)], ['13', '14'])).
% 0.14/0.49  thf('16', plain,
% 0.14/0.49      (![X0 : $i]: ((v1_yellow_1 @ k1_xboole_0) | ~ (l1_orders_2 @ X0))),
% 0.14/0.49      inference('sup+', [status(thm)], ['12', '15'])).
% 0.14/0.49  thf('17', plain,
% 0.14/0.49      (![X0 : $i, X1 : $i]:
% 0.14/0.49         ((v1_yellow_1 @ X0) | ~ (v1_xboole_0 @ X0) | ~ (l1_orders_2 @ X1))),
% 0.14/0.49      inference('sup+', [status(thm)], ['11', '16'])).
% 0.14/0.49  thf('18', plain, (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (v1_yellow_1 @ X0))),
% 0.14/0.49      inference('sup-', [status(thm)], ['10', '17'])).
% 0.14/0.49  thf('19', plain,
% 0.14/0.49      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.14/0.49      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.14/0.49  thf(t81_relat_1, axiom, (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.14/0.49  thf('20', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.14/0.49      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.14/0.49  thf('21', plain,
% 0.14/0.49      (![X0 : $i]: (((k6_relat_1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.14/0.49      inference('sup+', [status(thm)], ['19', '20'])).
% 0.14/0.49  thf(dt_k6_partfun1, axiom,
% 0.14/0.49    (![A:$i]:
% 0.14/0.49     ( ( m1_subset_1 @
% 0.14/0.49         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 0.14/0.49       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 0.14/0.49  thf('22', plain, (![X32 : $i]: (v1_partfun1 @ (k6_partfun1 @ X32) @ X32)),
% 0.14/0.49      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.14/0.49  thf('23', plain, (![X34 : $i]: ((k6_partfun1 @ X34) = (k6_relat_1 @ X34))),
% 0.14/0.49      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.14/0.49  thf('24', plain, (![X32 : $i]: (v1_partfun1 @ (k6_relat_1 @ X32) @ X32)),
% 0.14/0.49      inference('demod', [status(thm)], ['22', '23'])).
% 0.14/0.49  thf('25', plain,
% 0.14/0.49      (![X0 : $i]: ((v1_partfun1 @ k1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X0))),
% 0.14/0.49      inference('sup+', [status(thm)], ['21', '24'])).
% 0.14/0.49  thf(t26_yellow_1, axiom,
% 0.14/0.49    (![A:$i]:
% 0.14/0.49     ( ( ( v1_relat_1 @ A ) & ( v4_relat_1 @ A @ k1_xboole_0 ) & 
% 0.14/0.49         ( v1_funct_1 @ A ) & ( v1_partfun1 @ A @ k1_xboole_0 ) & 
% 0.14/0.49         ( v1_yellow_1 @ A ) ) =>
% 0.14/0.49       ( ( k5_yellow_1 @ k1_xboole_0 @ A ) =
% 0.14/0.49         ( g1_orders_2 @
% 0.14/0.49           ( k1_tarski @ k1_xboole_0 ) @ 
% 0.14/0.49           ( k6_partfun1 @ ( k1_tarski @ k1_xboole_0 ) ) ) ) ))).
% 0.14/0.49  thf('26', plain,
% 0.14/0.49      (![X42 : $i]:
% 0.14/0.49         (((k5_yellow_1 @ k1_xboole_0 @ X42)
% 0.14/0.49            = (g1_orders_2 @ (k1_tarski @ k1_xboole_0) @ 
% 0.14/0.49               (k6_partfun1 @ (k1_tarski @ k1_xboole_0))))
% 0.14/0.49          | ~ (v1_yellow_1 @ X42)
% 0.14/0.49          | ~ (v1_partfun1 @ X42 @ k1_xboole_0)
% 0.14/0.49          | ~ (v1_funct_1 @ X42)
% 0.14/0.49          | ~ (v4_relat_1 @ X42 @ k1_xboole_0)
% 0.14/0.49          | ~ (v1_relat_1 @ X42))),
% 0.14/0.49      inference('cnf', [status(esa)], [t26_yellow_1])).
% 0.14/0.49  thf('27', plain, (![X34 : $i]: ((k6_partfun1 @ X34) = (k6_relat_1 @ X34))),
% 0.14/0.49      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.14/0.49  thf('28', plain,
% 0.14/0.49      (![X42 : $i]:
% 0.14/0.49         (((k5_yellow_1 @ k1_xboole_0 @ X42)
% 0.14/0.49            = (g1_orders_2 @ (k1_tarski @ k1_xboole_0) @ 
% 0.14/0.49               (k6_relat_1 @ (k1_tarski @ k1_xboole_0))))
% 0.14/0.49          | ~ (v1_yellow_1 @ X42)
% 0.14/0.49          | ~ (v1_partfun1 @ X42 @ k1_xboole_0)
% 0.14/0.49          | ~ (v1_funct_1 @ X42)
% 0.14/0.49          | ~ (v4_relat_1 @ X42 @ k1_xboole_0)
% 0.14/0.49          | ~ (v1_relat_1 @ X42))),
% 0.14/0.49      inference('demod', [status(thm)], ['26', '27'])).
% 0.14/0.49  thf('29', plain,
% 0.14/0.49      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.14/0.49        | ~ (v1_relat_1 @ k1_xboole_0)
% 0.14/0.49        | ~ (v4_relat_1 @ k1_xboole_0 @ k1_xboole_0)
% 0.14/0.49        | ~ (v1_funct_1 @ k1_xboole_0)
% 0.14/0.49        | ~ (v1_yellow_1 @ k1_xboole_0)
% 0.14/0.49        | ((k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0)
% 0.14/0.49            = (g1_orders_2 @ (k1_tarski @ k1_xboole_0) @ 
% 0.14/0.49               (k6_relat_1 @ (k1_tarski @ k1_xboole_0)))))),
% 0.14/0.49      inference('sup-', [status(thm)], ['25', '28'])).
% 0.14/0.49  thf('30', plain,
% 0.14/0.49      (![X39 : $i]: (v1_xboole_0 @ (k7_funcop_1 @ k1_xboole_0 @ X39))),
% 0.14/0.49      inference('demod', [status(thm)], ['0', '1'])).
% 0.14/0.49  thf('31', plain,
% 0.14/0.49      (![X0 : $i]: ((k7_funcop_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.14/0.49      inference('sup-', [status(thm)], ['2', '3'])).
% 0.14/0.49  thf('32', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.14/0.49      inference('demod', [status(thm)], ['30', '31'])).
% 0.14/0.49  thf(t45_ordinal1, axiom,
% 0.14/0.49    (![A:$i]:
% 0.14/0.49     ( ( v5_ordinal1 @ k1_xboole_0 ) & ( v1_funct_1 @ k1_xboole_0 ) & 
% 0.14/0.49       ( v5_relat_1 @ k1_xboole_0 @ A ) & ( v1_relat_1 @ k1_xboole_0 ) ))).
% 0.14/0.49  thf('33', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.14/0.49      inference('cnf', [status(esa)], [t45_ordinal1])).
% 0.14/0.49  thf(l222_relat_1, axiom,
% 0.14/0.49    (![A:$i,B:$i]:
% 0.14/0.49     ( ( v5_relat_1 @ k1_xboole_0 @ B ) & ( v4_relat_1 @ k1_xboole_0 @ A ) ))).
% 0.14/0.49  thf('34', plain, (![X30 : $i]: (v4_relat_1 @ k1_xboole_0 @ X30)),
% 0.14/0.49      inference('cnf', [status(esa)], [l222_relat_1])).
% 0.14/0.49  thf('35', plain, ((v1_funct_1 @ k1_xboole_0)),
% 0.14/0.49      inference('cnf', [status(esa)], [t45_ordinal1])).
% 0.14/0.49  thf('36', plain,
% 0.14/0.49      ((~ (v1_yellow_1 @ k1_xboole_0)
% 0.14/0.49        | ((k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0)
% 0.14/0.49            = (g1_orders_2 @ (k1_tarski @ k1_xboole_0) @ 
% 0.14/0.49               (k6_relat_1 @ (k1_tarski @ k1_xboole_0)))))),
% 0.14/0.49      inference('demod', [status(thm)], ['29', '32', '33', '34', '35'])).
% 0.14/0.49  thf('37', plain,
% 0.14/0.49      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.14/0.49        | ((k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0)
% 0.14/0.49            = (g1_orders_2 @ (k1_tarski @ k1_xboole_0) @ 
% 0.14/0.49               (k6_relat_1 @ (k1_tarski @ k1_xboole_0)))))),
% 0.14/0.49      inference('sup-', [status(thm)], ['18', '36'])).
% 0.14/0.49  thf('38', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.14/0.49      inference('demod', [status(thm)], ['30', '31'])).
% 0.14/0.49  thf('39', plain,
% 0.14/0.49      (((k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0)
% 0.14/0.49         = (g1_orders_2 @ (k1_tarski @ k1_xboole_0) @ 
% 0.14/0.49            (k6_relat_1 @ (k1_tarski @ k1_xboole_0))))),
% 0.14/0.49      inference('demod', [status(thm)], ['37', '38'])).
% 0.14/0.49  thf('40', plain,
% 0.14/0.49      (((k6_yellow_1 @ k1_xboole_0 @ sk_A)
% 0.14/0.49         != (k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0))),
% 0.14/0.49      inference('demod', [status(thm)], ['9', '39'])).
% 0.14/0.49  thf('41', plain,
% 0.14/0.49      (![X0 : $i]:
% 0.14/0.49         (((k6_yellow_1 @ k1_xboole_0 @ sk_A)
% 0.14/0.49            != (k6_yellow_1 @ k1_xboole_0 @ X0))
% 0.14/0.49          | ~ (l1_orders_2 @ X0))),
% 0.14/0.49      inference('sup-', [status(thm)], ['6', '40'])).
% 0.14/0.49  thf('42', plain, (~ (l1_orders_2 @ sk_A)),
% 0.14/0.49      inference('eq_res', [status(thm)], ['41'])).
% 0.14/0.49  thf('43', plain, ((l1_orders_2 @ sk_A)),
% 0.14/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.14/0.49  thf('44', plain, ($false), inference('demod', [status(thm)], ['42', '43'])).
% 0.14/0.49  
% 0.14/0.49  % SZS output end Refutation
% 0.14/0.49  
% 0.14/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
