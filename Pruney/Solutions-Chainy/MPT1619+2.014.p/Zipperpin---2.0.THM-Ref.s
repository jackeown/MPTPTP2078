%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.NUYEt2LfbB

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:26 EST 2020

% Result     : Theorem 0.44s
% Output     : Refutation 0.44s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 116 expanded)
%              Number of leaves         :   40 (  58 expanded)
%              Depth                    :    9
%              Number of atoms          :  446 ( 574 expanded)
%              Number of equality atoms :   39 (  55 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k6_yellow_1_type,type,(
    k6_yellow_1: $i > $i > $i )).

thf(v1_orders_2_type,type,(
    v1_orders_2: $i > $o )).

thf(v7_struct_0_type,type,(
    v7_struct_0: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k7_funcop_1_type,type,(
    k7_funcop_1: $i > $i > $i )).

thf(k5_yellow_1_type,type,(
    k5_yellow_1: $i > $i > $i )).

thf(v1_yellow_1_type,type,(
    v1_yellow_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(g1_orders_2_type,type,(
    g1_orders_2: $i > $i > $i )).

thf(k2_funcop_1_type,type,(
    k2_funcop_1: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(sk_A_1_type,type,(
    sk_A_1: $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

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

thf(t1_zfmisc_1,axiom,
    ( ( k1_zfmisc_1 @ k1_xboole_0 )
    = ( k1_tarski @ k1_xboole_0 ) )).

thf('8',plain,
    ( ( k1_zfmisc_1 @ k1_xboole_0 )
    = ( k1_tarski @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t1_zfmisc_1])).

thf('9',plain,
    ( ( k1_zfmisc_1 @ k1_xboole_0 )
    = ( k1_tarski @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t1_zfmisc_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('10',plain,(
    ! [X36: $i] :
      ( ( k6_partfun1 @ X36 )
      = ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('11',plain,(
    ( k6_yellow_1 @ k1_xboole_0 @ sk_A_1 )
 != ( g1_orders_2 @ ( k1_zfmisc_1 @ k1_xboole_0 ) @ ( k6_relat_1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['7','8','9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t81_relat_1,axiom,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('13',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( ( k6_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('15',plain,(
    ! [X34: $i] :
      ( v1_partfun1 @ ( k6_partfun1 @ X34 ) @ X34 ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('16',plain,(
    ! [X36: $i] :
      ( ( k6_partfun1 @ X36 )
      = ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('17',plain,(
    ! [X34: $i] :
      ( v1_partfun1 @ ( k6_relat_1 @ X34 ) @ X34 ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( v1_partfun1 @ k1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','17'])).

thf(t26_yellow_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v4_relat_1 @ A @ k1_xboole_0 )
        & ( v1_funct_1 @ A )
        & ( v1_partfun1 @ A @ k1_xboole_0 )
        & ( v1_yellow_1 @ A ) )
     => ( ( k5_yellow_1 @ k1_xboole_0 @ A )
        = ( g1_orders_2 @ ( k1_tarski @ k1_xboole_0 ) @ ( k6_partfun1 @ ( k1_tarski @ k1_xboole_0 ) ) ) ) ) )).

thf('19',plain,(
    ! [X44: $i] :
      ( ( ( k5_yellow_1 @ k1_xboole_0 @ X44 )
        = ( g1_orders_2 @ ( k1_tarski @ k1_xboole_0 ) @ ( k6_partfun1 @ ( k1_tarski @ k1_xboole_0 ) ) ) )
      | ~ ( v1_yellow_1 @ X44 )
      | ~ ( v1_partfun1 @ X44 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ X44 )
      | ~ ( v4_relat_1 @ X44 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t26_yellow_1])).

thf('20',plain,
    ( ( k1_zfmisc_1 @ k1_xboole_0 )
    = ( k1_tarski @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t1_zfmisc_1])).

thf('21',plain,
    ( ( k1_zfmisc_1 @ k1_xboole_0 )
    = ( k1_tarski @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t1_zfmisc_1])).

thf('22',plain,(
    ! [X36: $i] :
      ( ( k6_partfun1 @ X36 )
      = ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('23',plain,(
    ! [X44: $i] :
      ( ( ( k5_yellow_1 @ k1_xboole_0 @ X44 )
        = ( g1_orders_2 @ ( k1_zfmisc_1 @ k1_xboole_0 ) @ ( k6_relat_1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ) )
      | ~ ( v1_yellow_1 @ X44 )
      | ~ ( v1_partfun1 @ X44 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ X44 )
      | ~ ( v4_relat_1 @ X44 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X44 ) ) ),
    inference(demod,[status(thm)],['19','20','21','22'])).

thf('24',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 )
    | ~ ( v4_relat_1 @ k1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_funct_1 @ k1_xboole_0 )
    | ~ ( v1_yellow_1 @ k1_xboole_0 )
    | ( ( k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0 )
      = ( g1_orders_2 @ ( k1_zfmisc_1 @ k1_xboole_0 ) @ ( k6_relat_1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ) ) ),
    inference('sup-',[status(thm)],['18','23'])).

thf('25',plain,(
    ! [X41: $i] :
      ( v1_xboole_0 @ ( k2_funcop_1 @ k1_xboole_0 @ X41 ) ) ),
    inference(cnf,[status(esa)],[fc2_funcop_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k2_funcop_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('27',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('29',plain,(
    ! [X29: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('30',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf('32',plain,(
    ! [X35: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X35 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('33',plain,(
    ! [X36: $i] :
      ( ( k6_partfun1 @ X36 )
      = ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('34',plain,(
    ! [X35: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X35 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X35 ) ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['31','34'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('36',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( v4_relat_1 @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('37',plain,(
    v4_relat_1 @ k1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf('39',plain,(
    ! [X30: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('40',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['38','39'])).

thf(rc1_yellow_0,axiom,(
    ? [A: $i] :
      ( ( v3_orders_2 @ A )
      & ( v1_orders_2 @ A )
      & ( v7_struct_0 @ A )
      & ~ ( v2_struct_0 @ A )
      & ( l1_orders_2 @ A ) ) )).

thf('41',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[rc1_yellow_0])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k2_funcop_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(fc10_yellow_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( l1_orders_2 @ B )
     => ( v1_yellow_1 @ ( k2_funcop_1 @ A @ B ) ) ) )).

thf('43',plain,(
    ! [X39: $i,X40: $i] :
      ( ( v1_yellow_1 @ ( k2_funcop_1 @ X39 @ X40 ) )
      | ~ ( l1_orders_2 @ X40 ) ) ),
    inference(cnf,[status(esa)],[fc10_yellow_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( v1_yellow_1 @ k1_xboole_0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    v1_yellow_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['41','44'])).

thf('46',plain,
    ( ( k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0 )
    = ( g1_orders_2 @ ( k1_zfmisc_1 @ k1_xboole_0 ) @ ( k6_relat_1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['24','27','30','37','40','45'])).

thf('47',plain,(
    ( k6_yellow_1 @ k1_xboole_0 @ sk_A_1 )
 != ( k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['11','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( ( k6_yellow_1 @ k1_xboole_0 @ sk_A_1 )
       != ( k6_yellow_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','47'])).

thf('49',plain,(
    ~ ( l1_orders_2 @ sk_A_1 ) ),
    inference(eq_res,[status(thm)],['48'])).

thf('50',plain,(
    l1_orders_2 @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    $false ),
    inference(demod,[status(thm)],['49','50'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.NUYEt2LfbB
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:05:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.44/0.65  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.44/0.65  % Solved by: fo/fo7.sh
% 0.44/0.65  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.44/0.65  % done 211 iterations in 0.194s
% 0.44/0.65  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.44/0.65  % SZS output start Refutation
% 0.44/0.65  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.44/0.65  thf(sk_A_type, type, sk_A: $i).
% 0.44/0.65  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.44/0.65  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.44/0.65  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.44/0.65  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.44/0.65  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.44/0.65  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.44/0.65  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.44/0.65  thf(k6_yellow_1_type, type, k6_yellow_1: $i > $i > $i).
% 0.44/0.65  thf(v1_orders_2_type, type, v1_orders_2: $i > $o).
% 0.44/0.65  thf(v7_struct_0_type, type, v7_struct_0: $i > $o).
% 0.44/0.65  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.44/0.65  thf(k7_funcop_1_type, type, k7_funcop_1: $i > $i > $i).
% 0.44/0.65  thf(k5_yellow_1_type, type, k5_yellow_1: $i > $i > $i).
% 0.44/0.65  thf(v1_yellow_1_type, type, v1_yellow_1: $i > $o).
% 0.44/0.65  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.44/0.65  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.44/0.65  thf(g1_orders_2_type, type, g1_orders_2: $i > $i > $i).
% 0.44/0.65  thf(k2_funcop_1_type, type, k2_funcop_1: $i > $i > $i).
% 0.44/0.65  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.44/0.65  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.44/0.65  thf(sk_A_1_type, type, sk_A_1: $i).
% 0.44/0.65  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.44/0.65  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.44/0.65  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.44/0.65  thf(fc2_funcop_1, axiom,
% 0.44/0.65    (![A:$i]: ( v1_xboole_0 @ ( k2_funcop_1 @ k1_xboole_0 @ A ) ))).
% 0.44/0.65  thf('0', plain,
% 0.44/0.65      (![X41 : $i]: (v1_xboole_0 @ (k2_funcop_1 @ k1_xboole_0 @ X41))),
% 0.44/0.65      inference('cnf', [status(esa)], [fc2_funcop_1])).
% 0.44/0.65  thf(l13_xboole_0, axiom,
% 0.44/0.65    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.44/0.65  thf('1', plain,
% 0.44/0.65      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.44/0.65      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.44/0.65  thf('2', plain,
% 0.44/0.65      (![X0 : $i]: ((k2_funcop_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.44/0.65      inference('sup-', [status(thm)], ['0', '1'])).
% 0.44/0.65  thf(redefinition_k7_funcop_1, axiom,
% 0.44/0.65    (![A:$i,B:$i]: ( ( k7_funcop_1 @ A @ B ) = ( k2_funcop_1 @ A @ B ) ))).
% 0.44/0.65  thf('3', plain,
% 0.44/0.65      (![X42 : $i, X43 : $i]:
% 0.44/0.65         ((k7_funcop_1 @ X42 @ X43) = (k2_funcop_1 @ X42 @ X43))),
% 0.44/0.65      inference('cnf', [status(esa)], [redefinition_k7_funcop_1])).
% 0.44/0.65  thf('4', plain,
% 0.44/0.65      (![X0 : $i]: ((k7_funcop_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.44/0.65      inference('demod', [status(thm)], ['2', '3'])).
% 0.44/0.65  thf(d5_yellow_1, axiom,
% 0.44/0.65    (![A:$i,B:$i]:
% 0.44/0.65     ( ( l1_orders_2 @ B ) =>
% 0.44/0.65       ( ( k6_yellow_1 @ A @ B ) =
% 0.44/0.65         ( k5_yellow_1 @ A @ ( k7_funcop_1 @ A @ B ) ) ) ))).
% 0.44/0.65  thf('5', plain,
% 0.44/0.65      (![X37 : $i, X38 : $i]:
% 0.44/0.65         (((k6_yellow_1 @ X37 @ X38)
% 0.44/0.65            = (k5_yellow_1 @ X37 @ (k7_funcop_1 @ X37 @ X38)))
% 0.44/0.65          | ~ (l1_orders_2 @ X38))),
% 0.44/0.65      inference('cnf', [status(esa)], [d5_yellow_1])).
% 0.44/0.65  thf('6', plain,
% 0.44/0.65      (![X0 : $i]:
% 0.44/0.65         (((k6_yellow_1 @ k1_xboole_0 @ X0)
% 0.44/0.65            = (k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0))
% 0.44/0.65          | ~ (l1_orders_2 @ X0))),
% 0.44/0.65      inference('sup+', [status(thm)], ['4', '5'])).
% 0.44/0.65  thf(t27_yellow_1, conjecture,
% 0.44/0.65    (![A:$i]:
% 0.44/0.65     ( ( l1_orders_2 @ A ) =>
% 0.44/0.65       ( ( k6_yellow_1 @ k1_xboole_0 @ A ) =
% 0.44/0.65         ( g1_orders_2 @
% 0.44/0.65           ( k1_tarski @ k1_xboole_0 ) @ 
% 0.44/0.65           ( k6_partfun1 @ ( k1_tarski @ k1_xboole_0 ) ) ) ) ))).
% 0.44/0.65  thf(zf_stmt_0, negated_conjecture,
% 0.44/0.65    (~( ![A:$i]:
% 0.44/0.65        ( ( l1_orders_2 @ A ) =>
% 0.44/0.65          ( ( k6_yellow_1 @ k1_xboole_0 @ A ) =
% 0.44/0.65            ( g1_orders_2 @
% 0.44/0.65              ( k1_tarski @ k1_xboole_0 ) @ 
% 0.44/0.65              ( k6_partfun1 @ ( k1_tarski @ k1_xboole_0 ) ) ) ) ) )),
% 0.44/0.65    inference('cnf.neg', [status(esa)], [t27_yellow_1])).
% 0.44/0.65  thf('7', plain,
% 0.44/0.65      (((k6_yellow_1 @ k1_xboole_0 @ sk_A_1)
% 0.44/0.65         != (g1_orders_2 @ (k1_tarski @ k1_xboole_0) @ 
% 0.44/0.65             (k6_partfun1 @ (k1_tarski @ k1_xboole_0))))),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf(t1_zfmisc_1, axiom,
% 0.44/0.65    (( k1_zfmisc_1 @ k1_xboole_0 ) = ( k1_tarski @ k1_xboole_0 ))).
% 0.44/0.65  thf('8', plain, (((k1_zfmisc_1 @ k1_xboole_0) = (k1_tarski @ k1_xboole_0))),
% 0.44/0.65      inference('cnf', [status(esa)], [t1_zfmisc_1])).
% 0.44/0.65  thf('9', plain, (((k1_zfmisc_1 @ k1_xboole_0) = (k1_tarski @ k1_xboole_0))),
% 0.44/0.65      inference('cnf', [status(esa)], [t1_zfmisc_1])).
% 0.44/0.65  thf(redefinition_k6_partfun1, axiom,
% 0.44/0.65    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.44/0.65  thf('10', plain, (![X36 : $i]: ((k6_partfun1 @ X36) = (k6_relat_1 @ X36))),
% 0.44/0.65      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.44/0.65  thf('11', plain,
% 0.44/0.65      (((k6_yellow_1 @ k1_xboole_0 @ sk_A_1)
% 0.44/0.65         != (g1_orders_2 @ (k1_zfmisc_1 @ k1_xboole_0) @ 
% 0.44/0.65             (k6_relat_1 @ (k1_zfmisc_1 @ k1_xboole_0))))),
% 0.44/0.65      inference('demod', [status(thm)], ['7', '8', '9', '10'])).
% 0.44/0.65  thf('12', plain,
% 0.44/0.65      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.44/0.65      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.44/0.65  thf(t81_relat_1, axiom, (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.44/0.65  thf('13', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.44/0.65      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.44/0.65  thf('14', plain,
% 0.44/0.65      (![X0 : $i]: (((k6_relat_1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.44/0.65      inference('sup+', [status(thm)], ['12', '13'])).
% 0.44/0.65  thf(dt_k6_partfun1, axiom,
% 0.44/0.65    (![A:$i]:
% 0.44/0.65     ( ( m1_subset_1 @
% 0.44/0.65         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 0.44/0.65       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 0.44/0.65  thf('15', plain, (![X34 : $i]: (v1_partfun1 @ (k6_partfun1 @ X34) @ X34)),
% 0.44/0.65      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.44/0.65  thf('16', plain, (![X36 : $i]: ((k6_partfun1 @ X36) = (k6_relat_1 @ X36))),
% 0.44/0.65      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.44/0.65  thf('17', plain, (![X34 : $i]: (v1_partfun1 @ (k6_relat_1 @ X34) @ X34)),
% 0.44/0.65      inference('demod', [status(thm)], ['15', '16'])).
% 0.44/0.65  thf('18', plain,
% 0.44/0.65      (![X0 : $i]: ((v1_partfun1 @ k1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X0))),
% 0.44/0.65      inference('sup+', [status(thm)], ['14', '17'])).
% 0.44/0.65  thf(t26_yellow_1, axiom,
% 0.44/0.65    (![A:$i]:
% 0.44/0.65     ( ( ( v1_relat_1 @ A ) & ( v4_relat_1 @ A @ k1_xboole_0 ) & 
% 0.44/0.65         ( v1_funct_1 @ A ) & ( v1_partfun1 @ A @ k1_xboole_0 ) & 
% 0.44/0.65         ( v1_yellow_1 @ A ) ) =>
% 0.44/0.65       ( ( k5_yellow_1 @ k1_xboole_0 @ A ) =
% 0.44/0.65         ( g1_orders_2 @
% 0.44/0.65           ( k1_tarski @ k1_xboole_0 ) @ 
% 0.44/0.65           ( k6_partfun1 @ ( k1_tarski @ k1_xboole_0 ) ) ) ) ))).
% 0.44/0.65  thf('19', plain,
% 0.44/0.65      (![X44 : $i]:
% 0.44/0.65         (((k5_yellow_1 @ k1_xboole_0 @ X44)
% 0.44/0.65            = (g1_orders_2 @ (k1_tarski @ k1_xboole_0) @ 
% 0.44/0.65               (k6_partfun1 @ (k1_tarski @ k1_xboole_0))))
% 0.44/0.65          | ~ (v1_yellow_1 @ X44)
% 0.44/0.65          | ~ (v1_partfun1 @ X44 @ k1_xboole_0)
% 0.44/0.65          | ~ (v1_funct_1 @ X44)
% 0.44/0.65          | ~ (v4_relat_1 @ X44 @ k1_xboole_0)
% 0.44/0.65          | ~ (v1_relat_1 @ X44))),
% 0.44/0.65      inference('cnf', [status(esa)], [t26_yellow_1])).
% 0.44/0.65  thf('20', plain, (((k1_zfmisc_1 @ k1_xboole_0) = (k1_tarski @ k1_xboole_0))),
% 0.44/0.65      inference('cnf', [status(esa)], [t1_zfmisc_1])).
% 0.44/0.65  thf('21', plain, (((k1_zfmisc_1 @ k1_xboole_0) = (k1_tarski @ k1_xboole_0))),
% 0.44/0.65      inference('cnf', [status(esa)], [t1_zfmisc_1])).
% 0.44/0.65  thf('22', plain, (![X36 : $i]: ((k6_partfun1 @ X36) = (k6_relat_1 @ X36))),
% 0.44/0.65      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.44/0.65  thf('23', plain,
% 0.44/0.65      (![X44 : $i]:
% 0.44/0.65         (((k5_yellow_1 @ k1_xboole_0 @ X44)
% 0.44/0.65            = (g1_orders_2 @ (k1_zfmisc_1 @ k1_xboole_0) @ 
% 0.44/0.65               (k6_relat_1 @ (k1_zfmisc_1 @ k1_xboole_0))))
% 0.44/0.65          | ~ (v1_yellow_1 @ X44)
% 0.44/0.65          | ~ (v1_partfun1 @ X44 @ k1_xboole_0)
% 0.44/0.65          | ~ (v1_funct_1 @ X44)
% 0.44/0.65          | ~ (v4_relat_1 @ X44 @ k1_xboole_0)
% 0.44/0.65          | ~ (v1_relat_1 @ X44))),
% 0.44/0.65      inference('demod', [status(thm)], ['19', '20', '21', '22'])).
% 0.44/0.65  thf('24', plain,
% 0.44/0.65      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.44/0.65        | ~ (v1_relat_1 @ k1_xboole_0)
% 0.44/0.65        | ~ (v4_relat_1 @ k1_xboole_0 @ k1_xboole_0)
% 0.44/0.65        | ~ (v1_funct_1 @ k1_xboole_0)
% 0.44/0.65        | ~ (v1_yellow_1 @ k1_xboole_0)
% 0.44/0.65        | ((k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0)
% 0.44/0.65            = (g1_orders_2 @ (k1_zfmisc_1 @ k1_xboole_0) @ 
% 0.44/0.65               (k6_relat_1 @ (k1_zfmisc_1 @ k1_xboole_0)))))),
% 0.44/0.65      inference('sup-', [status(thm)], ['18', '23'])).
% 0.44/0.65  thf('25', plain,
% 0.44/0.65      (![X41 : $i]: (v1_xboole_0 @ (k2_funcop_1 @ k1_xboole_0 @ X41))),
% 0.44/0.65      inference('cnf', [status(esa)], [fc2_funcop_1])).
% 0.44/0.65  thf('26', plain,
% 0.44/0.65      (![X0 : $i]: ((k2_funcop_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.44/0.65      inference('sup-', [status(thm)], ['0', '1'])).
% 0.44/0.65  thf('27', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.44/0.65      inference('demod', [status(thm)], ['25', '26'])).
% 0.44/0.65  thf('28', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.44/0.65      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.44/0.65  thf(fc3_funct_1, axiom,
% 0.44/0.65    (![A:$i]:
% 0.44/0.65     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.44/0.65       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.44/0.65  thf('29', plain, (![X29 : $i]: (v1_relat_1 @ (k6_relat_1 @ X29))),
% 0.44/0.65      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.44/0.65  thf('30', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.44/0.65      inference('sup+', [status(thm)], ['28', '29'])).
% 0.44/0.65  thf('31', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.44/0.65      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.44/0.65  thf('32', plain,
% 0.44/0.65      (![X35 : $i]:
% 0.44/0.65         (m1_subset_1 @ (k6_partfun1 @ X35) @ 
% 0.44/0.65          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X35)))),
% 0.44/0.65      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.44/0.65  thf('33', plain, (![X36 : $i]: ((k6_partfun1 @ X36) = (k6_relat_1 @ X36))),
% 0.44/0.65      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.44/0.65  thf('34', plain,
% 0.44/0.65      (![X35 : $i]:
% 0.44/0.65         (m1_subset_1 @ (k6_relat_1 @ X35) @ 
% 0.44/0.65          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X35)))),
% 0.44/0.65      inference('demod', [status(thm)], ['32', '33'])).
% 0.44/0.65  thf('35', plain,
% 0.44/0.65      ((m1_subset_1 @ k1_xboole_0 @ 
% 0.44/0.65        (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0)))),
% 0.44/0.65      inference('sup+', [status(thm)], ['31', '34'])).
% 0.44/0.65  thf(cc2_relset_1, axiom,
% 0.44/0.65    (![A:$i,B:$i,C:$i]:
% 0.44/0.65     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.44/0.65       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.44/0.65  thf('36', plain,
% 0.44/0.65      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.44/0.65         ((v4_relat_1 @ X31 @ X32)
% 0.44/0.65          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 0.44/0.65      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.44/0.65  thf('37', plain, ((v4_relat_1 @ k1_xboole_0 @ k1_xboole_0)),
% 0.44/0.65      inference('sup-', [status(thm)], ['35', '36'])).
% 0.44/0.65  thf('38', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.44/0.65      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.44/0.65  thf('39', plain, (![X30 : $i]: (v1_funct_1 @ (k6_relat_1 @ X30))),
% 0.44/0.65      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.44/0.65  thf('40', plain, ((v1_funct_1 @ k1_xboole_0)),
% 0.44/0.65      inference('sup+', [status(thm)], ['38', '39'])).
% 0.44/0.65  thf(rc1_yellow_0, axiom,
% 0.44/0.65    (?[A:$i]:
% 0.44/0.65     ( ( v3_orders_2 @ A ) & ( v1_orders_2 @ A ) & ( v7_struct_0 @ A ) & 
% 0.44/0.65       ( ~( v2_struct_0 @ A ) ) & ( l1_orders_2 @ A ) ))).
% 0.44/0.65  thf('41', plain, ((l1_orders_2 @ sk_A)),
% 0.44/0.65      inference('cnf', [status(esa)], [rc1_yellow_0])).
% 0.44/0.65  thf('42', plain,
% 0.44/0.65      (![X0 : $i]: ((k2_funcop_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.44/0.65      inference('sup-', [status(thm)], ['0', '1'])).
% 0.44/0.65  thf(fc10_yellow_1, axiom,
% 0.44/0.65    (![A:$i,B:$i]:
% 0.44/0.65     ( ( l1_orders_2 @ B ) => ( v1_yellow_1 @ ( k2_funcop_1 @ A @ B ) ) ))).
% 0.44/0.65  thf('43', plain,
% 0.44/0.65      (![X39 : $i, X40 : $i]:
% 0.44/0.65         ((v1_yellow_1 @ (k2_funcop_1 @ X39 @ X40)) | ~ (l1_orders_2 @ X40))),
% 0.44/0.65      inference('cnf', [status(esa)], [fc10_yellow_1])).
% 0.44/0.65  thf('44', plain,
% 0.44/0.65      (![X0 : $i]: ((v1_yellow_1 @ k1_xboole_0) | ~ (l1_orders_2 @ X0))),
% 0.44/0.65      inference('sup+', [status(thm)], ['42', '43'])).
% 0.44/0.65  thf('45', plain, ((v1_yellow_1 @ k1_xboole_0)),
% 0.44/0.65      inference('sup-', [status(thm)], ['41', '44'])).
% 0.44/0.65  thf('46', plain,
% 0.44/0.65      (((k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0)
% 0.44/0.65         = (g1_orders_2 @ (k1_zfmisc_1 @ k1_xboole_0) @ 
% 0.44/0.65            (k6_relat_1 @ (k1_zfmisc_1 @ k1_xboole_0))))),
% 0.44/0.65      inference('demod', [status(thm)], ['24', '27', '30', '37', '40', '45'])).
% 0.44/0.65  thf('47', plain,
% 0.44/0.65      (((k6_yellow_1 @ k1_xboole_0 @ sk_A_1)
% 0.44/0.65         != (k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0))),
% 0.44/0.65      inference('demod', [status(thm)], ['11', '46'])).
% 0.44/0.65  thf('48', plain,
% 0.44/0.65      (![X0 : $i]:
% 0.44/0.65         (((k6_yellow_1 @ k1_xboole_0 @ sk_A_1)
% 0.44/0.65            != (k6_yellow_1 @ k1_xboole_0 @ X0))
% 0.44/0.65          | ~ (l1_orders_2 @ X0))),
% 0.44/0.65      inference('sup-', [status(thm)], ['6', '47'])).
% 0.44/0.65  thf('49', plain, (~ (l1_orders_2 @ sk_A_1)),
% 0.44/0.65      inference('eq_res', [status(thm)], ['48'])).
% 0.44/0.65  thf('50', plain, ((l1_orders_2 @ sk_A_1)),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('51', plain, ($false), inference('demod', [status(thm)], ['49', '50'])).
% 0.44/0.65  
% 0.44/0.65  % SZS output end Refutation
% 0.44/0.65  
% 0.44/0.66  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
