%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.feEgvTJ4yW

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:24 EST 2020

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 115 expanded)
%              Number of leaves         :   43 (  57 expanded)
%              Depth                    :   12
%              Number of atoms          :  435 ( 540 expanded)
%              Number of equality atoms :   33 (  44 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_1_type,type,(
    sk_A_1: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_yellow_1_type,type,(
    v1_yellow_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_orders_2_type,type,(
    v1_orders_2: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k7_funcop_1_type,type,(
    k7_funcop_1: $i > $i > $i )).

thf(k6_yellow_1_type,type,(
    k6_yellow_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(g1_orders_2_type,type,(
    g1_orders_2: $i > $i > $i )).

thf(k5_yellow_1_type,type,(
    k5_yellow_1: $i > $i > $i )).

thf(k2_funcop_1_type,type,(
    k2_funcop_1: $i > $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(d5_yellow_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( l1_orders_2 @ B )
     => ( ( k6_yellow_1 @ A @ B )
        = ( k5_yellow_1 @ A @ ( k7_funcop_1 @ A @ B ) ) ) ) )).

thf('0',plain,(
    ! [X37: $i,X38: $i] :
      ( ( ( k6_yellow_1 @ X37 @ X38 )
        = ( k5_yellow_1 @ X37 @ ( k7_funcop_1 @ X37 @ X38 ) ) )
      | ~ ( l1_orders_2 @ X38 ) ) ),
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
    ( k6_yellow_1 @ k1_xboole_0 @ sk_A_1 )
 != ( g1_orders_2 @ ( k1_tarski @ k1_xboole_0 ) @ ( k6_partfun1 @ ( k1_tarski @ k1_xboole_0 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('3',plain,(
    ! [X36: $i] :
      ( ( k6_partfun1 @ X36 )
      = ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('4',plain,(
    ( k6_yellow_1 @ k1_xboole_0 @ sk_A_1 )
 != ( g1_orders_2 @ ( k1_tarski @ k1_xboole_0 ) @ ( k6_relat_1 @ ( k1_tarski @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t81_relat_1,axiom,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('6',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('7',plain,(
    ! [X34: $i] :
      ( v1_partfun1 @ ( k6_partfun1 @ X34 ) @ X34 ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('8',plain,(
    ! [X36: $i] :
      ( ( k6_partfun1 @ X36 )
      = ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('9',plain,(
    ! [X34: $i] :
      ( v1_partfun1 @ ( k6_relat_1 @ X34 ) @ X34 ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    v1_partfun1 @ k1_xboole_0 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['6','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( v1_partfun1 @ k1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','10'])).

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
    ! [X44: $i] :
      ( ( ( k5_yellow_1 @ k1_xboole_0 @ X44 )
        = ( g1_orders_2 @ ( k1_tarski @ k1_xboole_0 ) @ ( k6_partfun1 @ ( k1_tarski @ k1_xboole_0 ) ) ) )
      | ~ ( v1_yellow_1 @ X44 )
      | ~ ( v1_partfun1 @ X44 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ X44 )
      | ~ ( v4_relat_1 @ X44 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t26_yellow_1])).

thf('13',plain,(
    ! [X36: $i] :
      ( ( k6_partfun1 @ X36 )
      = ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('14',plain,(
    ! [X44: $i] :
      ( ( ( k5_yellow_1 @ k1_xboole_0 @ X44 )
        = ( g1_orders_2 @ ( k1_tarski @ k1_xboole_0 ) @ ( k6_relat_1 @ ( k1_tarski @ k1_xboole_0 ) ) ) )
      | ~ ( v1_yellow_1 @ X44 )
      | ~ ( v1_partfun1 @ X44 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ X44 )
      | ~ ( v4_relat_1 @ X44 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X44 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 )
    | ~ ( v4_relat_1 @ k1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_funct_1 @ k1_xboole_0 )
    | ~ ( v1_yellow_1 @ k1_xboole_0 )
    | ( ( k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0 )
      = ( g1_orders_2 @ ( k1_tarski @ k1_xboole_0 ) @ ( k6_relat_1 @ ( k1_tarski @ k1_xboole_0 ) ) ) ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('16',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('17',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(cc1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_relat_1 @ A ) ) )).

thf('18',plain,(
    ! [X30: $i] :
      ( ( v1_relat_1 @ X30 )
      | ~ ( v1_xboole_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('19',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['17','18'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('20',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('21',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X31 ) @ X32 )
      | ( v4_relat_1 @ X31 @ X32 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( v4_relat_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('23',plain,(
    ! [X1: $i] :
      ( r1_tarski @ k1_xboole_0 @ X1 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('24',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['17','18'])).

thf('25',plain,(
    ! [X0: $i] :
      ( v4_relat_1 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('26',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(cc1_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_funct_1 @ A ) ) )).

thf('27',plain,(
    ! [X33: $i] :
      ( ( v1_funct_1 @ X33 )
      | ~ ( v1_xboole_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[cc1_funct_1])).

thf('28',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['26','27'])).

thf(rc4_orders_2,axiom,(
    ? [A: $i] :
      ( ( v1_orders_2 @ A )
      & ( v2_struct_0 @ A )
      & ( l1_orders_2 @ A ) ) )).

thf('29',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[rc4_orders_2])).

thf(fc2_funcop_1,axiom,(
    ! [A: $i] :
      ( v1_xboole_0 @ ( k2_funcop_1 @ k1_xboole_0 @ A ) ) )).

thf('30',plain,(
    ! [X41: $i] :
      ( v1_xboole_0 @ ( k2_funcop_1 @ k1_xboole_0 @ X41 ) ) ),
    inference(cnf,[status(esa)],[fc2_funcop_1])).

thf(redefinition_k7_funcop_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k7_funcop_1 @ A @ B )
      = ( k2_funcop_1 @ A @ B ) ) )).

thf('31',plain,(
    ! [X42: $i,X43: $i] :
      ( ( k7_funcop_1 @ X42 @ X43 )
      = ( k2_funcop_1 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_funcop_1])).

thf('32',plain,(
    ! [X41: $i] :
      ( v1_xboole_0 @ ( k7_funcop_1 @ k1_xboole_0 @ X41 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k7_funcop_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf(fc10_yellow_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( l1_orders_2 @ B )
     => ( v1_yellow_1 @ ( k2_funcop_1 @ A @ B ) ) ) )).

thf('35',plain,(
    ! [X39: $i,X40: $i] :
      ( ( v1_yellow_1 @ ( k2_funcop_1 @ X39 @ X40 ) )
      | ~ ( l1_orders_2 @ X40 ) ) ),
    inference(cnf,[status(esa)],[fc10_yellow_1])).

thf('36',plain,(
    ! [X42: $i,X43: $i] :
      ( ( k7_funcop_1 @ X42 @ X43 )
      = ( k2_funcop_1 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_funcop_1])).

thf('37',plain,(
    ! [X39: $i,X40: $i] :
      ( ( v1_yellow_1 @ ( k7_funcop_1 @ X39 @ X40 ) )
      | ~ ( l1_orders_2 @ X40 ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( v1_yellow_1 @ k1_xboole_0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['34','37'])).

thf('39',plain,(
    v1_yellow_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['29','38'])).

thf('40',plain,
    ( ( k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0 )
    = ( g1_orders_2 @ ( k1_tarski @ k1_xboole_0 ) @ ( k6_relat_1 @ ( k1_tarski @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['15','16','19','25','28','39'])).

thf('41',plain,(
    ( k6_yellow_1 @ k1_xboole_0 @ sk_A_1 )
 != ( k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['4','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( ( k6_yellow_1 @ k1_xboole_0 @ sk_A_1 )
       != ( k5_yellow_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( ( k6_yellow_1 @ k1_xboole_0 @ sk_A_1 )
       != ( k6_yellow_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v1_xboole_0 @ ( k7_funcop_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['0','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k7_funcop_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('45',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( ( k6_yellow_1 @ k1_xboole_0 @ sk_A_1 )
       != ( k6_yellow_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(demod,[status(thm)],['43','44','45'])).

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
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.feEgvTJ4yW
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:24:59 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.47/0.63  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.47/0.63  % Solved by: fo/fo7.sh
% 0.47/0.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.47/0.63  % done 195 iterations in 0.184s
% 0.47/0.63  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.47/0.63  % SZS output start Refutation
% 0.47/0.63  thf(sk_A_1_type, type, sk_A_1: $i).
% 0.47/0.63  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.47/0.63  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.47/0.63  thf(v1_yellow_1_type, type, v1_yellow_1: $i > $o).
% 0.47/0.63  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.47/0.63  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.47/0.63  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.47/0.63  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.47/0.63  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.47/0.63  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.47/0.63  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.47/0.63  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.47/0.63  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.47/0.63  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.47/0.63  thf(v1_orders_2_type, type, v1_orders_2: $i > $o).
% 0.47/0.63  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.47/0.63  thf(k7_funcop_1_type, type, k7_funcop_1: $i > $i > $i).
% 0.47/0.63  thf(k6_yellow_1_type, type, k6_yellow_1: $i > $i > $i).
% 0.47/0.63  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.47/0.63  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.47/0.63  thf(g1_orders_2_type, type, g1_orders_2: $i > $i > $i).
% 0.47/0.63  thf(k5_yellow_1_type, type, k5_yellow_1: $i > $i > $i).
% 0.47/0.63  thf(k2_funcop_1_type, type, k2_funcop_1: $i > $i > $i).
% 0.47/0.63  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.47/0.63  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.47/0.63  thf(sk_A_type, type, sk_A: $i).
% 0.47/0.63  thf(d5_yellow_1, axiom,
% 0.47/0.63    (![A:$i,B:$i]:
% 0.47/0.63     ( ( l1_orders_2 @ B ) =>
% 0.47/0.63       ( ( k6_yellow_1 @ A @ B ) =
% 0.47/0.63         ( k5_yellow_1 @ A @ ( k7_funcop_1 @ A @ B ) ) ) ))).
% 0.47/0.63  thf('0', plain,
% 0.47/0.63      (![X37 : $i, X38 : $i]:
% 0.47/0.63         (((k6_yellow_1 @ X37 @ X38)
% 0.47/0.63            = (k5_yellow_1 @ X37 @ (k7_funcop_1 @ X37 @ X38)))
% 0.47/0.63          | ~ (l1_orders_2 @ X38))),
% 0.47/0.63      inference('cnf', [status(esa)], [d5_yellow_1])).
% 0.47/0.63  thf(l13_xboole_0, axiom,
% 0.47/0.63    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.47/0.63  thf('1', plain,
% 0.47/0.63      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.47/0.63      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.47/0.63  thf(t27_yellow_1, conjecture,
% 0.47/0.63    (![A:$i]:
% 0.47/0.63     ( ( l1_orders_2 @ A ) =>
% 0.47/0.63       ( ( k6_yellow_1 @ k1_xboole_0 @ A ) =
% 0.47/0.63         ( g1_orders_2 @
% 0.47/0.63           ( k1_tarski @ k1_xboole_0 ) @ 
% 0.47/0.63           ( k6_partfun1 @ ( k1_tarski @ k1_xboole_0 ) ) ) ) ))).
% 0.47/0.63  thf(zf_stmt_0, negated_conjecture,
% 0.47/0.63    (~( ![A:$i]:
% 0.47/0.63        ( ( l1_orders_2 @ A ) =>
% 0.47/0.63          ( ( k6_yellow_1 @ k1_xboole_0 @ A ) =
% 0.47/0.63            ( g1_orders_2 @
% 0.47/0.63              ( k1_tarski @ k1_xboole_0 ) @ 
% 0.47/0.63              ( k6_partfun1 @ ( k1_tarski @ k1_xboole_0 ) ) ) ) ) )),
% 0.47/0.63    inference('cnf.neg', [status(esa)], [t27_yellow_1])).
% 0.47/0.63  thf('2', plain,
% 0.47/0.63      (((k6_yellow_1 @ k1_xboole_0 @ sk_A_1)
% 0.47/0.63         != (g1_orders_2 @ (k1_tarski @ k1_xboole_0) @ 
% 0.47/0.63             (k6_partfun1 @ (k1_tarski @ k1_xboole_0))))),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf(redefinition_k6_partfun1, axiom,
% 0.47/0.63    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.47/0.63  thf('3', plain, (![X36 : $i]: ((k6_partfun1 @ X36) = (k6_relat_1 @ X36))),
% 0.47/0.63      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.47/0.63  thf('4', plain,
% 0.47/0.63      (((k6_yellow_1 @ k1_xboole_0 @ sk_A_1)
% 0.47/0.63         != (g1_orders_2 @ (k1_tarski @ k1_xboole_0) @ 
% 0.47/0.63             (k6_relat_1 @ (k1_tarski @ k1_xboole_0))))),
% 0.47/0.63      inference('demod', [status(thm)], ['2', '3'])).
% 0.47/0.63  thf('5', plain,
% 0.47/0.63      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.47/0.63      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.47/0.63  thf(t81_relat_1, axiom, (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.47/0.63  thf('6', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.47/0.63      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.47/0.63  thf(dt_k6_partfun1, axiom,
% 0.47/0.63    (![A:$i]:
% 0.47/0.63     ( ( m1_subset_1 @
% 0.47/0.63         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 0.47/0.63       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 0.47/0.63  thf('7', plain, (![X34 : $i]: (v1_partfun1 @ (k6_partfun1 @ X34) @ X34)),
% 0.47/0.63      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.47/0.63  thf('8', plain, (![X36 : $i]: ((k6_partfun1 @ X36) = (k6_relat_1 @ X36))),
% 0.47/0.63      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.47/0.63  thf('9', plain, (![X34 : $i]: (v1_partfun1 @ (k6_relat_1 @ X34) @ X34)),
% 0.47/0.63      inference('demod', [status(thm)], ['7', '8'])).
% 0.47/0.63  thf('10', plain, ((v1_partfun1 @ k1_xboole_0 @ k1_xboole_0)),
% 0.47/0.63      inference('sup+', [status(thm)], ['6', '9'])).
% 0.47/0.63  thf('11', plain,
% 0.47/0.63      (![X0 : $i]: ((v1_partfun1 @ k1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X0))),
% 0.47/0.63      inference('sup+', [status(thm)], ['5', '10'])).
% 0.47/0.63  thf(t26_yellow_1, axiom,
% 0.47/0.63    (![A:$i]:
% 0.47/0.63     ( ( ( v1_relat_1 @ A ) & ( v4_relat_1 @ A @ k1_xboole_0 ) & 
% 0.47/0.63         ( v1_funct_1 @ A ) & ( v1_partfun1 @ A @ k1_xboole_0 ) & 
% 0.47/0.63         ( v1_yellow_1 @ A ) ) =>
% 0.47/0.63       ( ( k5_yellow_1 @ k1_xboole_0 @ A ) =
% 0.47/0.63         ( g1_orders_2 @
% 0.47/0.63           ( k1_tarski @ k1_xboole_0 ) @ 
% 0.47/0.63           ( k6_partfun1 @ ( k1_tarski @ k1_xboole_0 ) ) ) ) ))).
% 0.47/0.63  thf('12', plain,
% 0.47/0.63      (![X44 : $i]:
% 0.47/0.63         (((k5_yellow_1 @ k1_xboole_0 @ X44)
% 0.47/0.63            = (g1_orders_2 @ (k1_tarski @ k1_xboole_0) @ 
% 0.47/0.63               (k6_partfun1 @ (k1_tarski @ k1_xboole_0))))
% 0.47/0.63          | ~ (v1_yellow_1 @ X44)
% 0.47/0.63          | ~ (v1_partfun1 @ X44 @ k1_xboole_0)
% 0.47/0.63          | ~ (v1_funct_1 @ X44)
% 0.47/0.63          | ~ (v4_relat_1 @ X44 @ k1_xboole_0)
% 0.47/0.63          | ~ (v1_relat_1 @ X44))),
% 0.47/0.63      inference('cnf', [status(esa)], [t26_yellow_1])).
% 0.47/0.63  thf('13', plain, (![X36 : $i]: ((k6_partfun1 @ X36) = (k6_relat_1 @ X36))),
% 0.47/0.63      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.47/0.63  thf('14', plain,
% 0.47/0.63      (![X44 : $i]:
% 0.47/0.63         (((k5_yellow_1 @ k1_xboole_0 @ X44)
% 0.47/0.63            = (g1_orders_2 @ (k1_tarski @ k1_xboole_0) @ 
% 0.47/0.63               (k6_relat_1 @ (k1_tarski @ k1_xboole_0))))
% 0.47/0.63          | ~ (v1_yellow_1 @ X44)
% 0.47/0.63          | ~ (v1_partfun1 @ X44 @ k1_xboole_0)
% 0.47/0.63          | ~ (v1_funct_1 @ X44)
% 0.47/0.63          | ~ (v4_relat_1 @ X44 @ k1_xboole_0)
% 0.47/0.63          | ~ (v1_relat_1 @ X44))),
% 0.47/0.63      inference('demod', [status(thm)], ['12', '13'])).
% 0.47/0.63  thf('15', plain,
% 0.47/0.63      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.47/0.63        | ~ (v1_relat_1 @ k1_xboole_0)
% 0.47/0.63        | ~ (v4_relat_1 @ k1_xboole_0 @ k1_xboole_0)
% 0.47/0.63        | ~ (v1_funct_1 @ k1_xboole_0)
% 0.47/0.63        | ~ (v1_yellow_1 @ k1_xboole_0)
% 0.47/0.63        | ((k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0)
% 0.47/0.63            = (g1_orders_2 @ (k1_tarski @ k1_xboole_0) @ 
% 0.47/0.63               (k6_relat_1 @ (k1_tarski @ k1_xboole_0)))))),
% 0.47/0.63      inference('sup-', [status(thm)], ['11', '14'])).
% 0.47/0.63  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.47/0.63  thf('16', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.47/0.63      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.47/0.63  thf('17', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.47/0.63      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.47/0.63  thf(cc1_relat_1, axiom,
% 0.47/0.63    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 0.47/0.63  thf('18', plain, (![X30 : $i]: ((v1_relat_1 @ X30) | ~ (v1_xboole_0 @ X30))),
% 0.47/0.63      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.47/0.63  thf('19', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.47/0.63      inference('sup-', [status(thm)], ['17', '18'])).
% 0.47/0.63  thf(t60_relat_1, axiom,
% 0.47/0.63    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.47/0.63     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.47/0.63  thf('20', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.47/0.63      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.47/0.63  thf(d18_relat_1, axiom,
% 0.47/0.63    (![A:$i,B:$i]:
% 0.47/0.63     ( ( v1_relat_1 @ B ) =>
% 0.47/0.63       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.47/0.63  thf('21', plain,
% 0.47/0.63      (![X31 : $i, X32 : $i]:
% 0.47/0.63         (~ (r1_tarski @ (k1_relat_1 @ X31) @ X32)
% 0.47/0.63          | (v4_relat_1 @ X31 @ X32)
% 0.47/0.63          | ~ (v1_relat_1 @ X31))),
% 0.47/0.63      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.47/0.63  thf('22', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         (~ (r1_tarski @ k1_xboole_0 @ X0)
% 0.47/0.63          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.47/0.63          | (v4_relat_1 @ k1_xboole_0 @ X0))),
% 0.47/0.63      inference('sup-', [status(thm)], ['20', '21'])).
% 0.47/0.63  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.47/0.63  thf('23', plain, (![X1 : $i]: (r1_tarski @ k1_xboole_0 @ X1)),
% 0.47/0.63      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.47/0.63  thf('24', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.47/0.63      inference('sup-', [status(thm)], ['17', '18'])).
% 0.47/0.63  thf('25', plain, (![X0 : $i]: (v4_relat_1 @ k1_xboole_0 @ X0)),
% 0.47/0.63      inference('demod', [status(thm)], ['22', '23', '24'])).
% 0.47/0.63  thf('26', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.47/0.63      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.47/0.63  thf(cc1_funct_1, axiom,
% 0.47/0.63    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_funct_1 @ A ) ))).
% 0.47/0.63  thf('27', plain, (![X33 : $i]: ((v1_funct_1 @ X33) | ~ (v1_xboole_0 @ X33))),
% 0.47/0.63      inference('cnf', [status(esa)], [cc1_funct_1])).
% 0.47/0.63  thf('28', plain, ((v1_funct_1 @ k1_xboole_0)),
% 0.47/0.63      inference('sup-', [status(thm)], ['26', '27'])).
% 0.47/0.63  thf(rc4_orders_2, axiom,
% 0.47/0.63    (?[A:$i]:
% 0.47/0.63     ( ( v1_orders_2 @ A ) & ( v2_struct_0 @ A ) & ( l1_orders_2 @ A ) ))).
% 0.47/0.63  thf('29', plain, ((l1_orders_2 @ sk_A)),
% 0.47/0.63      inference('cnf', [status(esa)], [rc4_orders_2])).
% 0.47/0.63  thf(fc2_funcop_1, axiom,
% 0.47/0.63    (![A:$i]: ( v1_xboole_0 @ ( k2_funcop_1 @ k1_xboole_0 @ A ) ))).
% 0.47/0.63  thf('30', plain,
% 0.47/0.63      (![X41 : $i]: (v1_xboole_0 @ (k2_funcop_1 @ k1_xboole_0 @ X41))),
% 0.47/0.63      inference('cnf', [status(esa)], [fc2_funcop_1])).
% 0.47/0.63  thf(redefinition_k7_funcop_1, axiom,
% 0.47/0.63    (![A:$i,B:$i]: ( ( k7_funcop_1 @ A @ B ) = ( k2_funcop_1 @ A @ B ) ))).
% 0.47/0.63  thf('31', plain,
% 0.47/0.63      (![X42 : $i, X43 : $i]:
% 0.47/0.63         ((k7_funcop_1 @ X42 @ X43) = (k2_funcop_1 @ X42 @ X43))),
% 0.47/0.63      inference('cnf', [status(esa)], [redefinition_k7_funcop_1])).
% 0.47/0.63  thf('32', plain,
% 0.47/0.63      (![X41 : $i]: (v1_xboole_0 @ (k7_funcop_1 @ k1_xboole_0 @ X41))),
% 0.47/0.63      inference('demod', [status(thm)], ['30', '31'])).
% 0.47/0.63  thf('33', plain,
% 0.47/0.63      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.47/0.63      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.47/0.63  thf('34', plain,
% 0.47/0.63      (![X0 : $i]: ((k7_funcop_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.47/0.63      inference('sup-', [status(thm)], ['32', '33'])).
% 0.47/0.63  thf(fc10_yellow_1, axiom,
% 0.47/0.63    (![A:$i,B:$i]:
% 0.47/0.63     ( ( l1_orders_2 @ B ) => ( v1_yellow_1 @ ( k2_funcop_1 @ A @ B ) ) ))).
% 0.47/0.63  thf('35', plain,
% 0.47/0.63      (![X39 : $i, X40 : $i]:
% 0.47/0.63         ((v1_yellow_1 @ (k2_funcop_1 @ X39 @ X40)) | ~ (l1_orders_2 @ X40))),
% 0.47/0.63      inference('cnf', [status(esa)], [fc10_yellow_1])).
% 0.47/0.63  thf('36', plain,
% 0.47/0.63      (![X42 : $i, X43 : $i]:
% 0.47/0.63         ((k7_funcop_1 @ X42 @ X43) = (k2_funcop_1 @ X42 @ X43))),
% 0.47/0.63      inference('cnf', [status(esa)], [redefinition_k7_funcop_1])).
% 0.47/0.63  thf('37', plain,
% 0.47/0.63      (![X39 : $i, X40 : $i]:
% 0.47/0.63         ((v1_yellow_1 @ (k7_funcop_1 @ X39 @ X40)) | ~ (l1_orders_2 @ X40))),
% 0.47/0.63      inference('demod', [status(thm)], ['35', '36'])).
% 0.47/0.63  thf('38', plain,
% 0.47/0.63      (![X0 : $i]: ((v1_yellow_1 @ k1_xboole_0) | ~ (l1_orders_2 @ X0))),
% 0.47/0.63      inference('sup+', [status(thm)], ['34', '37'])).
% 0.47/0.63  thf('39', plain, ((v1_yellow_1 @ k1_xboole_0)),
% 0.47/0.63      inference('sup-', [status(thm)], ['29', '38'])).
% 0.47/0.63  thf('40', plain,
% 0.47/0.63      (((k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0)
% 0.47/0.63         = (g1_orders_2 @ (k1_tarski @ k1_xboole_0) @ 
% 0.47/0.63            (k6_relat_1 @ (k1_tarski @ k1_xboole_0))))),
% 0.47/0.63      inference('demod', [status(thm)], ['15', '16', '19', '25', '28', '39'])).
% 0.47/0.63  thf('41', plain,
% 0.47/0.63      (((k6_yellow_1 @ k1_xboole_0 @ sk_A_1)
% 0.47/0.63         != (k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0))),
% 0.47/0.63      inference('demod', [status(thm)], ['4', '40'])).
% 0.47/0.63  thf('42', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         (((k6_yellow_1 @ k1_xboole_0 @ sk_A_1)
% 0.47/0.63            != (k5_yellow_1 @ k1_xboole_0 @ X0))
% 0.47/0.63          | ~ (v1_xboole_0 @ X0))),
% 0.47/0.63      inference('sup-', [status(thm)], ['1', '41'])).
% 0.47/0.63  thf('43', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         (((k6_yellow_1 @ k1_xboole_0 @ sk_A_1)
% 0.47/0.63            != (k6_yellow_1 @ k1_xboole_0 @ X0))
% 0.47/0.63          | ~ (l1_orders_2 @ X0)
% 0.47/0.63          | ~ (v1_xboole_0 @ (k7_funcop_1 @ k1_xboole_0 @ X0)))),
% 0.47/0.63      inference('sup-', [status(thm)], ['0', '42'])).
% 0.47/0.63  thf('44', plain,
% 0.47/0.63      (![X0 : $i]: ((k7_funcop_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.47/0.63      inference('sup-', [status(thm)], ['32', '33'])).
% 0.47/0.63  thf('45', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.47/0.63      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.47/0.63  thf('46', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         (((k6_yellow_1 @ k1_xboole_0 @ sk_A_1)
% 0.47/0.63            != (k6_yellow_1 @ k1_xboole_0 @ X0))
% 0.47/0.63          | ~ (l1_orders_2 @ X0))),
% 0.47/0.63      inference('demod', [status(thm)], ['43', '44', '45'])).
% 0.47/0.63  thf('47', plain, (~ (l1_orders_2 @ sk_A_1)),
% 0.47/0.63      inference('eq_res', [status(thm)], ['46'])).
% 0.47/0.63  thf('48', plain, ((l1_orders_2 @ sk_A_1)),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('49', plain, ($false), inference('demod', [status(thm)], ['47', '48'])).
% 0.47/0.63  
% 0.47/0.63  % SZS output end Refutation
% 0.47/0.63  
% 0.47/0.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
