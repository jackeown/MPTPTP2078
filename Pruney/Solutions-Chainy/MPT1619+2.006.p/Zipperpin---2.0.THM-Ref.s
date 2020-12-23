%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.zNC9lKVIhY

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:24 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   82 (  97 expanded)
%              Number of leaves         :   39 (  49 expanded)
%              Depth                    :   10
%              Number of atoms          :  378 ( 464 expanded)
%              Number of equality atoms :   29 (  39 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(g1_orders_2_type,type,(
    g1_orders_2: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_orders_2_type,type,(
    v1_orders_2: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k5_yellow_1_type,type,(
    k5_yellow_1: $i > $i > $i )).

thf(k2_funcop_1_type,type,(
    k2_funcop_1: $i > $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_yellow_1_type,type,(
    v1_yellow_1: $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k6_yellow_1_type,type,(
    k6_yellow_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k7_funcop_1_type,type,(
    k7_funcop_1: $i > $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_A_1_type,type,(
    sk_A_1: $i )).

thf(fc2_funcop_1,axiom,(
    ! [A: $i] :
      ( v1_xboole_0 @ ( k2_funcop_1 @ k1_xboole_0 @ A ) ) )).

thf('0',plain,(
    ! [X40: $i] :
      ( v1_xboole_0 @ ( k2_funcop_1 @ k1_xboole_0 @ X40 ) ) ),
    inference(cnf,[status(esa)],[fc2_funcop_1])).

thf(redefinition_k7_funcop_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k7_funcop_1 @ A @ B )
      = ( k2_funcop_1 @ A @ B ) ) )).

thf('1',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k7_funcop_1 @ X41 @ X42 )
      = ( k2_funcop_1 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_funcop_1])).

thf('2',plain,(
    ! [X40: $i] :
      ( v1_xboole_0 @ ( k7_funcop_1 @ k1_xboole_0 @ X40 ) ) ),
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
    ! [X36: $i,X37: $i] :
      ( ( ( k6_yellow_1 @ X36 @ X37 )
        = ( k5_yellow_1 @ X36 @ ( k7_funcop_1 @ X36 @ X37 ) ) )
      | ~ ( l1_orders_2 @ X37 ) ) ),
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
    ! [X35: $i] :
      ( ( k6_partfun1 @ X35 )
      = ( k6_relat_1 @ X35 ) ) ),
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
    ! [X33: $i] :
      ( v1_partfun1 @ ( k6_partfun1 @ X33 ) @ X33 ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('14',plain,(
    ! [X35: $i] :
      ( ( k6_partfun1 @ X35 )
      = ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('15',plain,(
    ! [X33: $i] :
      ( v1_partfun1 @ ( k6_relat_1 @ X33 ) @ X33 ) ),
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
    ! [X43: $i] :
      ( ( ( k5_yellow_1 @ k1_xboole_0 @ X43 )
        = ( g1_orders_2 @ ( k1_tarski @ k1_xboole_0 ) @ ( k6_partfun1 @ ( k1_tarski @ k1_xboole_0 ) ) ) )
      | ~ ( v1_yellow_1 @ X43 )
      | ~ ( v1_partfun1 @ X43 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( v4_relat_1 @ X43 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t26_yellow_1])).

thf('18',plain,(
    ! [X35: $i] :
      ( ( k6_partfun1 @ X35 )
      = ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('19',plain,(
    ! [X43: $i] :
      ( ( ( k5_yellow_1 @ k1_xboole_0 @ X43 )
        = ( g1_orders_2 @ ( k1_tarski @ k1_xboole_0 ) @ ( k6_relat_1 @ ( k1_tarski @ k1_xboole_0 ) ) ) )
      | ~ ( v1_yellow_1 @ X43 )
      | ~ ( v1_partfun1 @ X43 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( v4_relat_1 @ X43 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X43 ) ) ),
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

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('21',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('22',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(cc1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_relat_1 @ A ) ) )).

thf('23',plain,(
    ! [X29: $i] :
      ( ( v1_relat_1 @ X29 )
      | ~ ( v1_xboole_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('24',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['22','23'])).

thf(l222_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v5_relat_1 @ k1_xboole_0 @ B )
      & ( v4_relat_1 @ k1_xboole_0 @ A ) ) )).

thf('25',plain,(
    ! [X31: $i] :
      ( v4_relat_1 @ k1_xboole_0 @ X31 ) ),
    inference(cnf,[status(esa)],[l222_relat_1])).

thf('26',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(cc1_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_funct_1 @ A ) ) )).

thf('27',plain,(
    ! [X32: $i] :
      ( ( v1_funct_1 @ X32 )
      | ~ ( v1_xboole_0 @ X32 ) ) ),
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

thf('30',plain,(
    ! [X0: $i] :
      ( ( k7_funcop_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(fc10_yellow_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( l1_orders_2 @ B )
     => ( v1_yellow_1 @ ( k2_funcop_1 @ A @ B ) ) ) )).

thf('31',plain,(
    ! [X38: $i,X39: $i] :
      ( ( v1_yellow_1 @ ( k2_funcop_1 @ X38 @ X39 ) )
      | ~ ( l1_orders_2 @ X39 ) ) ),
    inference(cnf,[status(esa)],[fc10_yellow_1])).

thf('32',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k7_funcop_1 @ X41 @ X42 )
      = ( k2_funcop_1 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_funcop_1])).

thf('33',plain,(
    ! [X38: $i,X39: $i] :
      ( ( v1_yellow_1 @ ( k7_funcop_1 @ X38 @ X39 ) )
      | ~ ( l1_orders_2 @ X39 ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( v1_yellow_1 @ k1_xboole_0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['30','33'])).

thf('35',plain,(
    v1_yellow_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['29','34'])).

thf('36',plain,
    ( ( k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0 )
    = ( g1_orders_2 @ ( k1_tarski @ k1_xboole_0 ) @ ( k6_relat_1 @ ( k1_tarski @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['20','21','24','25','28','35'])).

thf('37',plain,(
    ( k6_yellow_1 @ k1_xboole_0 @ sk_A_1 )
 != ( k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['9','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( ( k6_yellow_1 @ k1_xboole_0 @ sk_A_1 )
       != ( k6_yellow_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','37'])).

thf('39',plain,(
    ~ ( l1_orders_2 @ sk_A_1 ) ),
    inference(eq_res,[status(thm)],['38'])).

thf('40',plain,(
    l1_orders_2 @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    $false ),
    inference(demod,[status(thm)],['39','40'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.zNC9lKVIhY
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:04:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.37/0.60  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.37/0.60  % Solved by: fo/fo7.sh
% 0.37/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.60  % done 155 iterations in 0.150s
% 0.37/0.60  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.37/0.60  % SZS output start Refutation
% 0.37/0.60  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.37/0.60  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.37/0.60  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.37/0.60  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.37/0.60  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.37/0.60  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.37/0.60  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.37/0.60  thf(g1_orders_2_type, type, g1_orders_2: $i > $i > $i).
% 0.37/0.60  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.37/0.60  thf(v1_orders_2_type, type, v1_orders_2: $i > $o).
% 0.37/0.60  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.37/0.60  thf(k5_yellow_1_type, type, k5_yellow_1: $i > $i > $i).
% 0.37/0.60  thf(k2_funcop_1_type, type, k2_funcop_1: $i > $i > $i).
% 0.37/0.60  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.37/0.60  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.37/0.60  thf(v1_yellow_1_type, type, v1_yellow_1: $i > $o).
% 0.37/0.60  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.37/0.60  thf(k6_yellow_1_type, type, k6_yellow_1: $i > $i > $i).
% 0.37/0.60  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.37/0.60  thf(k7_funcop_1_type, type, k7_funcop_1: $i > $i > $i).
% 0.37/0.60  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.37/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.60  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.37/0.60  thf(sk_A_1_type, type, sk_A_1: $i).
% 0.37/0.60  thf(fc2_funcop_1, axiom,
% 0.37/0.60    (![A:$i]: ( v1_xboole_0 @ ( k2_funcop_1 @ k1_xboole_0 @ A ) ))).
% 0.37/0.60  thf('0', plain,
% 0.37/0.60      (![X40 : $i]: (v1_xboole_0 @ (k2_funcop_1 @ k1_xboole_0 @ X40))),
% 0.37/0.60      inference('cnf', [status(esa)], [fc2_funcop_1])).
% 0.37/0.60  thf(redefinition_k7_funcop_1, axiom,
% 0.37/0.60    (![A:$i,B:$i]: ( ( k7_funcop_1 @ A @ B ) = ( k2_funcop_1 @ A @ B ) ))).
% 0.37/0.60  thf('1', plain,
% 0.37/0.60      (![X41 : $i, X42 : $i]:
% 0.37/0.60         ((k7_funcop_1 @ X41 @ X42) = (k2_funcop_1 @ X41 @ X42))),
% 0.37/0.60      inference('cnf', [status(esa)], [redefinition_k7_funcop_1])).
% 0.37/0.60  thf('2', plain,
% 0.37/0.60      (![X40 : $i]: (v1_xboole_0 @ (k7_funcop_1 @ k1_xboole_0 @ X40))),
% 0.37/0.60      inference('demod', [status(thm)], ['0', '1'])).
% 0.37/0.60  thf(l13_xboole_0, axiom,
% 0.37/0.60    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.37/0.60  thf('3', plain,
% 0.37/0.60      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.37/0.60      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.37/0.60  thf('4', plain,
% 0.37/0.60      (![X0 : $i]: ((k7_funcop_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.37/0.60      inference('sup-', [status(thm)], ['2', '3'])).
% 0.37/0.60  thf(d5_yellow_1, axiom,
% 0.37/0.60    (![A:$i,B:$i]:
% 0.37/0.60     ( ( l1_orders_2 @ B ) =>
% 0.37/0.60       ( ( k6_yellow_1 @ A @ B ) =
% 0.37/0.60         ( k5_yellow_1 @ A @ ( k7_funcop_1 @ A @ B ) ) ) ))).
% 0.37/0.60  thf('5', plain,
% 0.37/0.60      (![X36 : $i, X37 : $i]:
% 0.37/0.60         (((k6_yellow_1 @ X36 @ X37)
% 0.37/0.60            = (k5_yellow_1 @ X36 @ (k7_funcop_1 @ X36 @ X37)))
% 0.37/0.60          | ~ (l1_orders_2 @ X37))),
% 0.37/0.60      inference('cnf', [status(esa)], [d5_yellow_1])).
% 0.37/0.60  thf('6', plain,
% 0.37/0.60      (![X0 : $i]:
% 0.37/0.60         (((k6_yellow_1 @ k1_xboole_0 @ X0)
% 0.37/0.60            = (k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0))
% 0.37/0.60          | ~ (l1_orders_2 @ X0))),
% 0.37/0.60      inference('sup+', [status(thm)], ['4', '5'])).
% 0.37/0.60  thf(t27_yellow_1, conjecture,
% 0.37/0.60    (![A:$i]:
% 0.37/0.60     ( ( l1_orders_2 @ A ) =>
% 0.37/0.60       ( ( k6_yellow_1 @ k1_xboole_0 @ A ) =
% 0.37/0.60         ( g1_orders_2 @
% 0.37/0.60           ( k1_tarski @ k1_xboole_0 ) @ 
% 0.37/0.60           ( k6_partfun1 @ ( k1_tarski @ k1_xboole_0 ) ) ) ) ))).
% 0.37/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.60    (~( ![A:$i]:
% 0.37/0.60        ( ( l1_orders_2 @ A ) =>
% 0.37/0.60          ( ( k6_yellow_1 @ k1_xboole_0 @ A ) =
% 0.37/0.60            ( g1_orders_2 @
% 0.37/0.60              ( k1_tarski @ k1_xboole_0 ) @ 
% 0.37/0.60              ( k6_partfun1 @ ( k1_tarski @ k1_xboole_0 ) ) ) ) ) )),
% 0.37/0.60    inference('cnf.neg', [status(esa)], [t27_yellow_1])).
% 0.37/0.60  thf('7', plain,
% 0.37/0.60      (((k6_yellow_1 @ k1_xboole_0 @ sk_A_1)
% 0.37/0.60         != (g1_orders_2 @ (k1_tarski @ k1_xboole_0) @ 
% 0.37/0.60             (k6_partfun1 @ (k1_tarski @ k1_xboole_0))))),
% 0.37/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.60  thf(redefinition_k6_partfun1, axiom,
% 0.37/0.60    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.37/0.60  thf('8', plain, (![X35 : $i]: ((k6_partfun1 @ X35) = (k6_relat_1 @ X35))),
% 0.37/0.60      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.37/0.60  thf('9', plain,
% 0.37/0.60      (((k6_yellow_1 @ k1_xboole_0 @ sk_A_1)
% 0.37/0.60         != (g1_orders_2 @ (k1_tarski @ k1_xboole_0) @ 
% 0.37/0.60             (k6_relat_1 @ (k1_tarski @ k1_xboole_0))))),
% 0.37/0.60      inference('demod', [status(thm)], ['7', '8'])).
% 0.37/0.60  thf('10', plain,
% 0.37/0.60      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.37/0.60      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.37/0.60  thf(t81_relat_1, axiom, (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.37/0.60  thf('11', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.37/0.60      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.37/0.60  thf('12', plain,
% 0.37/0.60      (![X0 : $i]: (((k6_relat_1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.37/0.60      inference('sup+', [status(thm)], ['10', '11'])).
% 0.37/0.60  thf(dt_k6_partfun1, axiom,
% 0.37/0.60    (![A:$i]:
% 0.37/0.60     ( ( m1_subset_1 @
% 0.37/0.60         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 0.37/0.60       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 0.37/0.60  thf('13', plain, (![X33 : $i]: (v1_partfun1 @ (k6_partfun1 @ X33) @ X33)),
% 0.37/0.60      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.37/0.60  thf('14', plain, (![X35 : $i]: ((k6_partfun1 @ X35) = (k6_relat_1 @ X35))),
% 0.37/0.60      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.37/0.60  thf('15', plain, (![X33 : $i]: (v1_partfun1 @ (k6_relat_1 @ X33) @ X33)),
% 0.37/0.60      inference('demod', [status(thm)], ['13', '14'])).
% 0.37/0.60  thf('16', plain,
% 0.37/0.60      (![X0 : $i]: ((v1_partfun1 @ k1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X0))),
% 0.37/0.60      inference('sup+', [status(thm)], ['12', '15'])).
% 0.37/0.60  thf(t26_yellow_1, axiom,
% 0.37/0.60    (![A:$i]:
% 0.37/0.60     ( ( ( v1_relat_1 @ A ) & ( v4_relat_1 @ A @ k1_xboole_0 ) & 
% 0.37/0.60         ( v1_funct_1 @ A ) & ( v1_partfun1 @ A @ k1_xboole_0 ) & 
% 0.37/0.60         ( v1_yellow_1 @ A ) ) =>
% 0.37/0.60       ( ( k5_yellow_1 @ k1_xboole_0 @ A ) =
% 0.37/0.60         ( g1_orders_2 @
% 0.37/0.60           ( k1_tarski @ k1_xboole_0 ) @ 
% 0.37/0.60           ( k6_partfun1 @ ( k1_tarski @ k1_xboole_0 ) ) ) ) ))).
% 0.37/0.60  thf('17', plain,
% 0.37/0.60      (![X43 : $i]:
% 0.37/0.60         (((k5_yellow_1 @ k1_xboole_0 @ X43)
% 0.37/0.60            = (g1_orders_2 @ (k1_tarski @ k1_xboole_0) @ 
% 0.37/0.60               (k6_partfun1 @ (k1_tarski @ k1_xboole_0))))
% 0.37/0.60          | ~ (v1_yellow_1 @ X43)
% 0.37/0.60          | ~ (v1_partfun1 @ X43 @ k1_xboole_0)
% 0.37/0.60          | ~ (v1_funct_1 @ X43)
% 0.37/0.60          | ~ (v4_relat_1 @ X43 @ k1_xboole_0)
% 0.37/0.60          | ~ (v1_relat_1 @ X43))),
% 0.37/0.60      inference('cnf', [status(esa)], [t26_yellow_1])).
% 0.37/0.60  thf('18', plain, (![X35 : $i]: ((k6_partfun1 @ X35) = (k6_relat_1 @ X35))),
% 0.37/0.60      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.37/0.60  thf('19', plain,
% 0.37/0.60      (![X43 : $i]:
% 0.37/0.60         (((k5_yellow_1 @ k1_xboole_0 @ X43)
% 0.37/0.60            = (g1_orders_2 @ (k1_tarski @ k1_xboole_0) @ 
% 0.37/0.60               (k6_relat_1 @ (k1_tarski @ k1_xboole_0))))
% 0.37/0.60          | ~ (v1_yellow_1 @ X43)
% 0.37/0.60          | ~ (v1_partfun1 @ X43 @ k1_xboole_0)
% 0.37/0.60          | ~ (v1_funct_1 @ X43)
% 0.37/0.60          | ~ (v4_relat_1 @ X43 @ k1_xboole_0)
% 0.37/0.60          | ~ (v1_relat_1 @ X43))),
% 0.37/0.60      inference('demod', [status(thm)], ['17', '18'])).
% 0.37/0.60  thf('20', plain,
% 0.37/0.60      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.37/0.60        | ~ (v1_relat_1 @ k1_xboole_0)
% 0.37/0.60        | ~ (v4_relat_1 @ k1_xboole_0 @ k1_xboole_0)
% 0.37/0.60        | ~ (v1_funct_1 @ k1_xboole_0)
% 0.37/0.60        | ~ (v1_yellow_1 @ k1_xboole_0)
% 0.37/0.60        | ((k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0)
% 0.37/0.60            = (g1_orders_2 @ (k1_tarski @ k1_xboole_0) @ 
% 0.37/0.60               (k6_relat_1 @ (k1_tarski @ k1_xboole_0)))))),
% 0.37/0.60      inference('sup-', [status(thm)], ['16', '19'])).
% 0.37/0.60  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.37/0.60  thf('21', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.37/0.60      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.37/0.60  thf('22', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.37/0.60      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.37/0.60  thf(cc1_relat_1, axiom,
% 0.37/0.60    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 0.37/0.60  thf('23', plain, (![X29 : $i]: ((v1_relat_1 @ X29) | ~ (v1_xboole_0 @ X29))),
% 0.37/0.60      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.37/0.60  thf('24', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.37/0.60      inference('sup-', [status(thm)], ['22', '23'])).
% 0.37/0.60  thf(l222_relat_1, axiom,
% 0.37/0.60    (![A:$i,B:$i]:
% 0.37/0.60     ( ( v5_relat_1 @ k1_xboole_0 @ B ) & ( v4_relat_1 @ k1_xboole_0 @ A ) ))).
% 0.37/0.60  thf('25', plain, (![X31 : $i]: (v4_relat_1 @ k1_xboole_0 @ X31)),
% 0.37/0.60      inference('cnf', [status(esa)], [l222_relat_1])).
% 0.37/0.60  thf('26', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.37/0.60      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.37/0.60  thf(cc1_funct_1, axiom,
% 0.37/0.60    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_funct_1 @ A ) ))).
% 0.37/0.60  thf('27', plain, (![X32 : $i]: ((v1_funct_1 @ X32) | ~ (v1_xboole_0 @ X32))),
% 0.37/0.60      inference('cnf', [status(esa)], [cc1_funct_1])).
% 0.37/0.60  thf('28', plain, ((v1_funct_1 @ k1_xboole_0)),
% 0.37/0.60      inference('sup-', [status(thm)], ['26', '27'])).
% 0.37/0.60  thf(rc4_orders_2, axiom,
% 0.37/0.60    (?[A:$i]:
% 0.37/0.60     ( ( v1_orders_2 @ A ) & ( v2_struct_0 @ A ) & ( l1_orders_2 @ A ) ))).
% 0.37/0.60  thf('29', plain, ((l1_orders_2 @ sk_A)),
% 0.37/0.60      inference('cnf', [status(esa)], [rc4_orders_2])).
% 0.37/0.60  thf('30', plain,
% 0.37/0.60      (![X0 : $i]: ((k7_funcop_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.37/0.60      inference('sup-', [status(thm)], ['2', '3'])).
% 0.37/0.60  thf(fc10_yellow_1, axiom,
% 0.37/0.60    (![A:$i,B:$i]:
% 0.37/0.60     ( ( l1_orders_2 @ B ) => ( v1_yellow_1 @ ( k2_funcop_1 @ A @ B ) ) ))).
% 0.37/0.60  thf('31', plain,
% 0.37/0.60      (![X38 : $i, X39 : $i]:
% 0.37/0.60         ((v1_yellow_1 @ (k2_funcop_1 @ X38 @ X39)) | ~ (l1_orders_2 @ X39))),
% 0.37/0.60      inference('cnf', [status(esa)], [fc10_yellow_1])).
% 0.37/0.60  thf('32', plain,
% 0.37/0.60      (![X41 : $i, X42 : $i]:
% 0.37/0.60         ((k7_funcop_1 @ X41 @ X42) = (k2_funcop_1 @ X41 @ X42))),
% 0.37/0.60      inference('cnf', [status(esa)], [redefinition_k7_funcop_1])).
% 0.37/0.60  thf('33', plain,
% 0.37/0.60      (![X38 : $i, X39 : $i]:
% 0.37/0.60         ((v1_yellow_1 @ (k7_funcop_1 @ X38 @ X39)) | ~ (l1_orders_2 @ X39))),
% 0.37/0.60      inference('demod', [status(thm)], ['31', '32'])).
% 0.37/0.60  thf('34', plain,
% 0.37/0.60      (![X0 : $i]: ((v1_yellow_1 @ k1_xboole_0) | ~ (l1_orders_2 @ X0))),
% 0.37/0.60      inference('sup+', [status(thm)], ['30', '33'])).
% 0.37/0.60  thf('35', plain, ((v1_yellow_1 @ k1_xboole_0)),
% 0.37/0.60      inference('sup-', [status(thm)], ['29', '34'])).
% 0.37/0.60  thf('36', plain,
% 0.37/0.60      (((k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0)
% 0.37/0.60         = (g1_orders_2 @ (k1_tarski @ k1_xboole_0) @ 
% 0.37/0.60            (k6_relat_1 @ (k1_tarski @ k1_xboole_0))))),
% 0.37/0.60      inference('demod', [status(thm)], ['20', '21', '24', '25', '28', '35'])).
% 0.37/0.60  thf('37', plain,
% 0.37/0.60      (((k6_yellow_1 @ k1_xboole_0 @ sk_A_1)
% 0.37/0.60         != (k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0))),
% 0.37/0.60      inference('demod', [status(thm)], ['9', '36'])).
% 0.37/0.60  thf('38', plain,
% 0.37/0.60      (![X0 : $i]:
% 0.37/0.60         (((k6_yellow_1 @ k1_xboole_0 @ sk_A_1)
% 0.37/0.60            != (k6_yellow_1 @ k1_xboole_0 @ X0))
% 0.37/0.60          | ~ (l1_orders_2 @ X0))),
% 0.37/0.60      inference('sup-', [status(thm)], ['6', '37'])).
% 0.37/0.60  thf('39', plain, (~ (l1_orders_2 @ sk_A_1)),
% 0.37/0.60      inference('eq_res', [status(thm)], ['38'])).
% 0.37/0.60  thf('40', plain, ((l1_orders_2 @ sk_A_1)),
% 0.37/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.60  thf('41', plain, ($false), inference('demod', [status(thm)], ['39', '40'])).
% 0.37/0.60  
% 0.37/0.60  % SZS output end Refutation
% 0.37/0.60  
% 0.37/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
