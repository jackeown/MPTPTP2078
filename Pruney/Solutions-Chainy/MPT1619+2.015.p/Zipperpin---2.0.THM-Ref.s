%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.osSSEXxgn5

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:26 EST 2020

% Result     : Theorem 0.60s
% Output     : Refutation 0.60s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 112 expanded)
%              Number of leaves         :   37 (  54 expanded)
%              Depth                    :   10
%              Number of atoms          :  430 ( 569 expanded)
%              Number of equality atoms :   35 (  52 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_A_1_type,type,(
    sk_A_1: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(g1_orders_2_type,type,(
    g1_orders_2: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_orders_2_type,type,(
    v1_orders_2: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k5_yellow_1_type,type,(
    k5_yellow_1: $i > $i > $i )).

thf(k2_funcop_1_type,type,(
    k2_funcop_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_yellow_1_type,type,(
    v1_yellow_1: $i > $o )).

thf(k6_yellow_1_type,type,(
    k6_yellow_1: $i > $i > $i )).

thf(k7_funcop_1_type,type,(
    k7_funcop_1: $i > $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

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
    ! [X29: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('26',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf('28',plain,(
    ! [X35: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X35 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('29',plain,(
    ! [X36: $i] :
      ( ( k6_partfun1 @ X36 )
      = ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('30',plain,(
    ! [X35: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X35 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X35 ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['27','30'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('32',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( v4_relat_1 @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('33',plain,(
    v4_relat_1 @ k1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf('35',plain,(
    ! [X30: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('36',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['34','35'])).

thf(rc4_orders_2,axiom,(
    ? [A: $i] :
      ( ( v1_orders_2 @ A )
      & ( v2_struct_0 @ A )
      & ( l1_orders_2 @ A ) ) )).

thf('37',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[rc4_orders_2])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k7_funcop_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(fc10_yellow_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( l1_orders_2 @ B )
     => ( v1_yellow_1 @ ( k2_funcop_1 @ A @ B ) ) ) )).

thf('39',plain,(
    ! [X39: $i,X40: $i] :
      ( ( v1_yellow_1 @ ( k2_funcop_1 @ X39 @ X40 ) )
      | ~ ( l1_orders_2 @ X40 ) ) ),
    inference(cnf,[status(esa)],[fc10_yellow_1])).

thf('40',plain,(
    ! [X42: $i,X43: $i] :
      ( ( k7_funcop_1 @ X42 @ X43 )
      = ( k2_funcop_1 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_funcop_1])).

thf('41',plain,(
    ! [X39: $i,X40: $i] :
      ( ( v1_yellow_1 @ ( k7_funcop_1 @ X39 @ X40 ) )
      | ~ ( l1_orders_2 @ X40 ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( v1_yellow_1 @ k1_xboole_0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['38','41'])).

thf('43',plain,(
    v1_yellow_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['37','42'])).

thf('44',plain,
    ( ( k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0 )
    = ( g1_orders_2 @ ( k1_tarski @ k1_xboole_0 ) @ ( k6_relat_1 @ ( k1_tarski @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['20','23','26','33','36','43'])).

thf('45',plain,(
    ( k6_yellow_1 @ k1_xboole_0 @ sk_A_1 )
 != ( k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['9','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( ( k6_yellow_1 @ k1_xboole_0 @ sk_A_1 )
       != ( k6_yellow_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','45'])).

thf('47',plain,(
    ~ ( l1_orders_2 @ sk_A_1 ) ),
    inference(eq_res,[status(thm)],['46'])).

thf('48',plain,(
    l1_orders_2 @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    $false ),
    inference(demod,[status(thm)],['47','48'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.osSSEXxgn5
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:21:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.60/0.78  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.60/0.78  % Solved by: fo/fo7.sh
% 0.60/0.78  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.60/0.78  % done 193 iterations in 0.276s
% 0.60/0.78  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.60/0.78  % SZS output start Refutation
% 0.60/0.78  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.60/0.78  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.60/0.78  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.60/0.78  thf(sk_A_1_type, type, sk_A_1: $i).
% 0.60/0.78  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.60/0.78  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.60/0.78  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.60/0.78  thf(sk_A_type, type, sk_A: $i).
% 0.60/0.78  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.60/0.78  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.60/0.78  thf(g1_orders_2_type, type, g1_orders_2: $i > $i > $i).
% 0.60/0.78  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.60/0.78  thf(v1_orders_2_type, type, v1_orders_2: $i > $o).
% 0.60/0.78  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.60/0.78  thf(k5_yellow_1_type, type, k5_yellow_1: $i > $i > $i).
% 0.60/0.78  thf(k2_funcop_1_type, type, k2_funcop_1: $i > $i > $i).
% 0.60/0.78  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.60/0.78  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.60/0.78  thf(v1_yellow_1_type, type, v1_yellow_1: $i > $o).
% 0.60/0.78  thf(k6_yellow_1_type, type, k6_yellow_1: $i > $i > $i).
% 0.60/0.78  thf(k7_funcop_1_type, type, k7_funcop_1: $i > $i > $i).
% 0.60/0.78  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.60/0.78  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.60/0.78  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.60/0.78  thf(fc2_funcop_1, axiom,
% 0.60/0.78    (![A:$i]: ( v1_xboole_0 @ ( k2_funcop_1 @ k1_xboole_0 @ A ) ))).
% 0.60/0.78  thf('0', plain,
% 0.60/0.78      (![X41 : $i]: (v1_xboole_0 @ (k2_funcop_1 @ k1_xboole_0 @ X41))),
% 0.60/0.78      inference('cnf', [status(esa)], [fc2_funcop_1])).
% 0.60/0.78  thf(l13_xboole_0, axiom,
% 0.60/0.78    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.60/0.78  thf('1', plain,
% 0.60/0.78      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.60/0.78      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.60/0.78  thf('2', plain,
% 0.60/0.78      (![X0 : $i]: ((k2_funcop_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.60/0.78      inference('sup-', [status(thm)], ['0', '1'])).
% 0.60/0.78  thf(redefinition_k7_funcop_1, axiom,
% 0.60/0.78    (![A:$i,B:$i]: ( ( k7_funcop_1 @ A @ B ) = ( k2_funcop_1 @ A @ B ) ))).
% 0.60/0.78  thf('3', plain,
% 0.60/0.78      (![X42 : $i, X43 : $i]:
% 0.60/0.78         ((k7_funcop_1 @ X42 @ X43) = (k2_funcop_1 @ X42 @ X43))),
% 0.60/0.78      inference('cnf', [status(esa)], [redefinition_k7_funcop_1])).
% 0.60/0.78  thf('4', plain,
% 0.60/0.78      (![X0 : $i]: ((k7_funcop_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.60/0.78      inference('demod', [status(thm)], ['2', '3'])).
% 0.60/0.78  thf(d5_yellow_1, axiom,
% 0.60/0.78    (![A:$i,B:$i]:
% 0.60/0.78     ( ( l1_orders_2 @ B ) =>
% 0.60/0.78       ( ( k6_yellow_1 @ A @ B ) =
% 0.60/0.78         ( k5_yellow_1 @ A @ ( k7_funcop_1 @ A @ B ) ) ) ))).
% 0.60/0.78  thf('5', plain,
% 0.60/0.78      (![X37 : $i, X38 : $i]:
% 0.60/0.78         (((k6_yellow_1 @ X37 @ X38)
% 0.60/0.78            = (k5_yellow_1 @ X37 @ (k7_funcop_1 @ X37 @ X38)))
% 0.60/0.78          | ~ (l1_orders_2 @ X38))),
% 0.60/0.78      inference('cnf', [status(esa)], [d5_yellow_1])).
% 0.60/0.78  thf('6', plain,
% 0.60/0.78      (![X0 : $i]:
% 0.60/0.78         (((k6_yellow_1 @ k1_xboole_0 @ X0)
% 0.60/0.78            = (k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0))
% 0.60/0.78          | ~ (l1_orders_2 @ X0))),
% 0.60/0.78      inference('sup+', [status(thm)], ['4', '5'])).
% 0.60/0.78  thf(t27_yellow_1, conjecture,
% 0.60/0.78    (![A:$i]:
% 0.60/0.78     ( ( l1_orders_2 @ A ) =>
% 0.60/0.78       ( ( k6_yellow_1 @ k1_xboole_0 @ A ) =
% 0.60/0.78         ( g1_orders_2 @
% 0.60/0.78           ( k1_tarski @ k1_xboole_0 ) @ 
% 0.60/0.78           ( k6_partfun1 @ ( k1_tarski @ k1_xboole_0 ) ) ) ) ))).
% 0.60/0.78  thf(zf_stmt_0, negated_conjecture,
% 0.60/0.78    (~( ![A:$i]:
% 0.60/0.78        ( ( l1_orders_2 @ A ) =>
% 0.60/0.78          ( ( k6_yellow_1 @ k1_xboole_0 @ A ) =
% 0.60/0.78            ( g1_orders_2 @
% 0.60/0.78              ( k1_tarski @ k1_xboole_0 ) @ 
% 0.60/0.78              ( k6_partfun1 @ ( k1_tarski @ k1_xboole_0 ) ) ) ) ) )),
% 0.60/0.78    inference('cnf.neg', [status(esa)], [t27_yellow_1])).
% 0.60/0.78  thf('7', plain,
% 0.60/0.78      (((k6_yellow_1 @ k1_xboole_0 @ sk_A_1)
% 0.60/0.78         != (g1_orders_2 @ (k1_tarski @ k1_xboole_0) @ 
% 0.60/0.78             (k6_partfun1 @ (k1_tarski @ k1_xboole_0))))),
% 0.60/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.78  thf(redefinition_k6_partfun1, axiom,
% 0.60/0.78    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.60/0.78  thf('8', plain, (![X36 : $i]: ((k6_partfun1 @ X36) = (k6_relat_1 @ X36))),
% 0.60/0.78      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.60/0.78  thf('9', plain,
% 0.60/0.78      (((k6_yellow_1 @ k1_xboole_0 @ sk_A_1)
% 0.60/0.78         != (g1_orders_2 @ (k1_tarski @ k1_xboole_0) @ 
% 0.60/0.78             (k6_relat_1 @ (k1_tarski @ k1_xboole_0))))),
% 0.60/0.78      inference('demod', [status(thm)], ['7', '8'])).
% 0.60/0.78  thf('10', plain,
% 0.60/0.78      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.60/0.78      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.60/0.78  thf(t81_relat_1, axiom, (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.60/0.78  thf('11', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.60/0.78      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.60/0.78  thf('12', plain,
% 0.60/0.78      (![X0 : $i]: (((k6_relat_1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.60/0.78      inference('sup+', [status(thm)], ['10', '11'])).
% 0.60/0.78  thf(dt_k6_partfun1, axiom,
% 0.60/0.78    (![A:$i]:
% 0.60/0.78     ( ( m1_subset_1 @
% 0.60/0.78         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 0.60/0.78       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 0.60/0.78  thf('13', plain, (![X34 : $i]: (v1_partfun1 @ (k6_partfun1 @ X34) @ X34)),
% 0.60/0.78      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.60/0.78  thf('14', plain, (![X36 : $i]: ((k6_partfun1 @ X36) = (k6_relat_1 @ X36))),
% 0.60/0.78      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.60/0.78  thf('15', plain, (![X34 : $i]: (v1_partfun1 @ (k6_relat_1 @ X34) @ X34)),
% 0.60/0.78      inference('demod', [status(thm)], ['13', '14'])).
% 0.60/0.78  thf('16', plain,
% 0.60/0.78      (![X0 : $i]: ((v1_partfun1 @ k1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X0))),
% 0.60/0.78      inference('sup+', [status(thm)], ['12', '15'])).
% 0.60/0.78  thf(t26_yellow_1, axiom,
% 0.60/0.78    (![A:$i]:
% 0.60/0.78     ( ( ( v1_relat_1 @ A ) & ( v4_relat_1 @ A @ k1_xboole_0 ) & 
% 0.60/0.78         ( v1_funct_1 @ A ) & ( v1_partfun1 @ A @ k1_xboole_0 ) & 
% 0.60/0.78         ( v1_yellow_1 @ A ) ) =>
% 0.60/0.78       ( ( k5_yellow_1 @ k1_xboole_0 @ A ) =
% 0.60/0.78         ( g1_orders_2 @
% 0.60/0.78           ( k1_tarski @ k1_xboole_0 ) @ 
% 0.60/0.78           ( k6_partfun1 @ ( k1_tarski @ k1_xboole_0 ) ) ) ) ))).
% 0.60/0.78  thf('17', plain,
% 0.60/0.78      (![X44 : $i]:
% 0.60/0.78         (((k5_yellow_1 @ k1_xboole_0 @ X44)
% 0.60/0.78            = (g1_orders_2 @ (k1_tarski @ k1_xboole_0) @ 
% 0.60/0.78               (k6_partfun1 @ (k1_tarski @ k1_xboole_0))))
% 0.60/0.78          | ~ (v1_yellow_1 @ X44)
% 0.60/0.78          | ~ (v1_partfun1 @ X44 @ k1_xboole_0)
% 0.60/0.78          | ~ (v1_funct_1 @ X44)
% 0.60/0.78          | ~ (v4_relat_1 @ X44 @ k1_xboole_0)
% 0.60/0.78          | ~ (v1_relat_1 @ X44))),
% 0.60/0.78      inference('cnf', [status(esa)], [t26_yellow_1])).
% 0.60/0.78  thf('18', plain, (![X36 : $i]: ((k6_partfun1 @ X36) = (k6_relat_1 @ X36))),
% 0.60/0.78      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.60/0.78  thf('19', plain,
% 0.60/0.78      (![X44 : $i]:
% 0.60/0.78         (((k5_yellow_1 @ k1_xboole_0 @ X44)
% 0.60/0.78            = (g1_orders_2 @ (k1_tarski @ k1_xboole_0) @ 
% 0.60/0.78               (k6_relat_1 @ (k1_tarski @ k1_xboole_0))))
% 0.60/0.78          | ~ (v1_yellow_1 @ X44)
% 0.60/0.78          | ~ (v1_partfun1 @ X44 @ k1_xboole_0)
% 0.60/0.78          | ~ (v1_funct_1 @ X44)
% 0.60/0.78          | ~ (v4_relat_1 @ X44 @ k1_xboole_0)
% 0.60/0.78          | ~ (v1_relat_1 @ X44))),
% 0.60/0.78      inference('demod', [status(thm)], ['17', '18'])).
% 0.60/0.78  thf('20', plain,
% 0.60/0.78      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.60/0.78        | ~ (v1_relat_1 @ k1_xboole_0)
% 0.60/0.78        | ~ (v4_relat_1 @ k1_xboole_0 @ k1_xboole_0)
% 0.60/0.78        | ~ (v1_funct_1 @ k1_xboole_0)
% 0.60/0.78        | ~ (v1_yellow_1 @ k1_xboole_0)
% 0.60/0.78        | ((k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0)
% 0.60/0.78            = (g1_orders_2 @ (k1_tarski @ k1_xboole_0) @ 
% 0.60/0.78               (k6_relat_1 @ (k1_tarski @ k1_xboole_0)))))),
% 0.60/0.78      inference('sup-', [status(thm)], ['16', '19'])).
% 0.60/0.78  thf('21', plain,
% 0.60/0.78      (![X41 : $i]: (v1_xboole_0 @ (k2_funcop_1 @ k1_xboole_0 @ X41))),
% 0.60/0.78      inference('cnf', [status(esa)], [fc2_funcop_1])).
% 0.60/0.78  thf('22', plain,
% 0.60/0.78      (![X0 : $i]: ((k2_funcop_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.60/0.78      inference('sup-', [status(thm)], ['0', '1'])).
% 0.60/0.78  thf('23', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.60/0.78      inference('demod', [status(thm)], ['21', '22'])).
% 0.60/0.78  thf('24', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.60/0.78      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.60/0.78  thf(fc3_funct_1, axiom,
% 0.60/0.78    (![A:$i]:
% 0.60/0.78     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.60/0.78       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.60/0.78  thf('25', plain, (![X29 : $i]: (v1_relat_1 @ (k6_relat_1 @ X29))),
% 0.60/0.78      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.60/0.78  thf('26', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.60/0.78      inference('sup+', [status(thm)], ['24', '25'])).
% 0.60/0.78  thf('27', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.60/0.78      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.60/0.78  thf('28', plain,
% 0.60/0.78      (![X35 : $i]:
% 0.60/0.78         (m1_subset_1 @ (k6_partfun1 @ X35) @ 
% 0.60/0.78          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X35)))),
% 0.60/0.78      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.60/0.78  thf('29', plain, (![X36 : $i]: ((k6_partfun1 @ X36) = (k6_relat_1 @ X36))),
% 0.60/0.78      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.60/0.78  thf('30', plain,
% 0.60/0.78      (![X35 : $i]:
% 0.60/0.78         (m1_subset_1 @ (k6_relat_1 @ X35) @ 
% 0.60/0.78          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X35)))),
% 0.60/0.78      inference('demod', [status(thm)], ['28', '29'])).
% 0.60/0.78  thf('31', plain,
% 0.60/0.78      ((m1_subset_1 @ k1_xboole_0 @ 
% 0.60/0.78        (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0)))),
% 0.60/0.78      inference('sup+', [status(thm)], ['27', '30'])).
% 0.60/0.78  thf(cc2_relset_1, axiom,
% 0.60/0.78    (![A:$i,B:$i,C:$i]:
% 0.60/0.78     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.60/0.78       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.60/0.78  thf('32', plain,
% 0.60/0.78      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.60/0.78         ((v4_relat_1 @ X31 @ X32)
% 0.60/0.78          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 0.60/0.78      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.60/0.78  thf('33', plain, ((v4_relat_1 @ k1_xboole_0 @ k1_xboole_0)),
% 0.60/0.78      inference('sup-', [status(thm)], ['31', '32'])).
% 0.60/0.78  thf('34', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.60/0.78      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.60/0.78  thf('35', plain, (![X30 : $i]: (v1_funct_1 @ (k6_relat_1 @ X30))),
% 0.60/0.78      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.60/0.78  thf('36', plain, ((v1_funct_1 @ k1_xboole_0)),
% 0.60/0.78      inference('sup+', [status(thm)], ['34', '35'])).
% 0.60/0.78  thf(rc4_orders_2, axiom,
% 0.60/0.78    (?[A:$i]:
% 0.60/0.78     ( ( v1_orders_2 @ A ) & ( v2_struct_0 @ A ) & ( l1_orders_2 @ A ) ))).
% 0.60/0.78  thf('37', plain, ((l1_orders_2 @ sk_A)),
% 0.60/0.78      inference('cnf', [status(esa)], [rc4_orders_2])).
% 0.60/0.78  thf('38', plain,
% 0.60/0.78      (![X0 : $i]: ((k7_funcop_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.60/0.78      inference('demod', [status(thm)], ['2', '3'])).
% 0.60/0.78  thf(fc10_yellow_1, axiom,
% 0.60/0.78    (![A:$i,B:$i]:
% 0.60/0.78     ( ( l1_orders_2 @ B ) => ( v1_yellow_1 @ ( k2_funcop_1 @ A @ B ) ) ))).
% 0.60/0.78  thf('39', plain,
% 0.60/0.78      (![X39 : $i, X40 : $i]:
% 0.60/0.78         ((v1_yellow_1 @ (k2_funcop_1 @ X39 @ X40)) | ~ (l1_orders_2 @ X40))),
% 0.60/0.78      inference('cnf', [status(esa)], [fc10_yellow_1])).
% 0.60/0.78  thf('40', plain,
% 0.60/0.78      (![X42 : $i, X43 : $i]:
% 0.60/0.78         ((k7_funcop_1 @ X42 @ X43) = (k2_funcop_1 @ X42 @ X43))),
% 0.60/0.78      inference('cnf', [status(esa)], [redefinition_k7_funcop_1])).
% 0.60/0.78  thf('41', plain,
% 0.60/0.78      (![X39 : $i, X40 : $i]:
% 0.60/0.78         ((v1_yellow_1 @ (k7_funcop_1 @ X39 @ X40)) | ~ (l1_orders_2 @ X40))),
% 0.60/0.78      inference('demod', [status(thm)], ['39', '40'])).
% 0.60/0.78  thf('42', plain,
% 0.60/0.78      (![X0 : $i]: ((v1_yellow_1 @ k1_xboole_0) | ~ (l1_orders_2 @ X0))),
% 0.60/0.78      inference('sup+', [status(thm)], ['38', '41'])).
% 0.60/0.78  thf('43', plain, ((v1_yellow_1 @ k1_xboole_0)),
% 0.60/0.78      inference('sup-', [status(thm)], ['37', '42'])).
% 0.60/0.78  thf('44', plain,
% 0.60/0.78      (((k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0)
% 0.60/0.78         = (g1_orders_2 @ (k1_tarski @ k1_xboole_0) @ 
% 0.60/0.78            (k6_relat_1 @ (k1_tarski @ k1_xboole_0))))),
% 0.60/0.78      inference('demod', [status(thm)], ['20', '23', '26', '33', '36', '43'])).
% 0.60/0.78  thf('45', plain,
% 0.60/0.78      (((k6_yellow_1 @ k1_xboole_0 @ sk_A_1)
% 0.60/0.78         != (k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0))),
% 0.60/0.78      inference('demod', [status(thm)], ['9', '44'])).
% 0.60/0.78  thf('46', plain,
% 0.60/0.78      (![X0 : $i]:
% 0.60/0.78         (((k6_yellow_1 @ k1_xboole_0 @ sk_A_1)
% 0.60/0.78            != (k6_yellow_1 @ k1_xboole_0 @ X0))
% 0.60/0.78          | ~ (l1_orders_2 @ X0))),
% 0.60/0.78      inference('sup-', [status(thm)], ['6', '45'])).
% 0.60/0.78  thf('47', plain, (~ (l1_orders_2 @ sk_A_1)),
% 0.60/0.78      inference('eq_res', [status(thm)], ['46'])).
% 0.60/0.78  thf('48', plain, ((l1_orders_2 @ sk_A_1)),
% 0.60/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.78  thf('49', plain, ($false), inference('demod', [status(thm)], ['47', '48'])).
% 0.60/0.78  
% 0.60/0.78  % SZS output end Refutation
% 0.60/0.78  
% 0.60/0.79  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
