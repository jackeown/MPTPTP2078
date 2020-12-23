%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wtRUAid75a

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:25 EST 2020

% Result     : Theorem 0.59s
% Output     : Refutation 0.59s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 109 expanded)
%              Number of leaves         :   41 (  54 expanded)
%              Depth                    :   10
%              Number of atoms          :  417 ( 531 expanded)
%              Number of equality atoms :   35 (  50 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_yellow_1_type,type,(
    v1_yellow_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k7_funcop_1_type,type,(
    k7_funcop_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k6_yellow_1_type,type,(
    k6_yellow_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k5_yellow_1_type,type,(
    k5_yellow_1: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v1_orders_2_type,type,(
    v1_orders_2: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(g1_orders_2_type,type,(
    g1_orders_2: $i > $i > $i )).

thf(k2_funcop_1_type,type,(
    k2_funcop_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(sk_A_1_type,type,(
    sk_A_1: $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(fc2_funcop_1,axiom,(
    ! [A: $i] :
      ( v1_xboole_0 @ ( k2_funcop_1 @ k1_xboole_0 @ A ) ) )).

thf('0',plain,(
    ! [X42: $i] :
      ( v1_xboole_0 @ ( k2_funcop_1 @ k1_xboole_0 @ X42 ) ) ),
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
    ! [X43: $i,X44: $i] :
      ( ( k7_funcop_1 @ X43 @ X44 )
      = ( k2_funcop_1 @ X43 @ X44 ) ) ),
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
    ! [X38: $i,X39: $i] :
      ( ( ( k6_yellow_1 @ X38 @ X39 )
        = ( k5_yellow_1 @ X38 @ ( k7_funcop_1 @ X38 @ X39 ) ) )
      | ~ ( l1_orders_2 @ X39 ) ) ),
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
    ! [X37: $i] :
      ( ( k6_partfun1 @ X37 )
      = ( k6_relat_1 @ X37 ) ) ),
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
    ! [X35: $i] :
      ( v1_partfun1 @ ( k6_partfun1 @ X35 ) @ X35 ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('14',plain,(
    ! [X37: $i] :
      ( ( k6_partfun1 @ X37 )
      = ( k6_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('15',plain,(
    ! [X35: $i] :
      ( v1_partfun1 @ ( k6_relat_1 @ X35 ) @ X35 ) ),
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
    ! [X45: $i] :
      ( ( ( k5_yellow_1 @ k1_xboole_0 @ X45 )
        = ( g1_orders_2 @ ( k1_tarski @ k1_xboole_0 ) @ ( k6_partfun1 @ ( k1_tarski @ k1_xboole_0 ) ) ) )
      | ~ ( v1_yellow_1 @ X45 )
      | ~ ( v1_partfun1 @ X45 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ X45 )
      | ~ ( v4_relat_1 @ X45 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t26_yellow_1])).

thf('18',plain,(
    ! [X37: $i] :
      ( ( k6_partfun1 @ X37 )
      = ( k6_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('19',plain,(
    ! [X45: $i] :
      ( ( ( k5_yellow_1 @ k1_xboole_0 @ X45 )
        = ( g1_orders_2 @ ( k1_tarski @ k1_xboole_0 ) @ ( k6_relat_1 @ ( k1_tarski @ k1_xboole_0 ) ) ) )
      | ~ ( v1_yellow_1 @ X45 )
      | ~ ( v1_partfun1 @ X45 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ X45 )
      | ~ ( v4_relat_1 @ X45 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X45 ) ) ),
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

thf('22',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('23',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('24',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['22','23'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('25',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('26',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X31 ) @ X32 )
      | ( v4_relat_1 @ X31 @ X32 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( v4_relat_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('28',plain,(
    ! [X1: $i] :
      ( r1_tarski @ k1_xboole_0 @ X1 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('29',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['22','23'])).

thf('30',plain,(
    ! [X0: $i] :
      ( v4_relat_1 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('31',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf('32',plain,(
    ! [X34: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('33',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['31','32'])).

thf(rc1_orders_2,axiom,(
    ? [A: $i] :
      ( ( v1_orders_2 @ A )
      & ( l1_orders_2 @ A ) ) )).

thf('34',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[rc1_orders_2])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k7_funcop_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(fc10_yellow_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( l1_orders_2 @ B )
     => ( v1_yellow_1 @ ( k2_funcop_1 @ A @ B ) ) ) )).

thf('36',plain,(
    ! [X40: $i,X41: $i] :
      ( ( v1_yellow_1 @ ( k2_funcop_1 @ X40 @ X41 ) )
      | ~ ( l1_orders_2 @ X41 ) ) ),
    inference(cnf,[status(esa)],[fc10_yellow_1])).

thf('37',plain,(
    ! [X43: $i,X44: $i] :
      ( ( k7_funcop_1 @ X43 @ X44 )
      = ( k2_funcop_1 @ X43 @ X44 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_funcop_1])).

thf('38',plain,(
    ! [X40: $i,X41: $i] :
      ( ( v1_yellow_1 @ ( k7_funcop_1 @ X40 @ X41 ) )
      | ~ ( l1_orders_2 @ X41 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( v1_yellow_1 @ k1_xboole_0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['35','38'])).

thf('40',plain,(
    v1_yellow_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['34','39'])).

thf('41',plain,
    ( ( k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0 )
    = ( g1_orders_2 @ ( k1_tarski @ k1_xboole_0 ) @ ( k6_relat_1 @ ( k1_tarski @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['20','21','24','30','33','40'])).

thf('42',plain,(
    ( k6_yellow_1 @ k1_xboole_0 @ sk_A_1 )
 != ( k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['9','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( ( k6_yellow_1 @ k1_xboole_0 @ sk_A_1 )
       != ( k6_yellow_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','42'])).

thf('44',plain,(
    ~ ( l1_orders_2 @ sk_A_1 ) ),
    inference(eq_res,[status(thm)],['43'])).

thf('45',plain,(
    l1_orders_2 @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    $false ),
    inference(demod,[status(thm)],['44','45'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wtRUAid75a
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:55:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.59/0.84  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.59/0.84  % Solved by: fo/fo7.sh
% 0.59/0.84  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.59/0.84  % done 211 iterations in 0.349s
% 0.59/0.84  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.59/0.84  % SZS output start Refutation
% 0.59/0.84  thf(sk_A_type, type, sk_A: $i).
% 0.59/0.84  thf(v1_yellow_1_type, type, v1_yellow_1: $i > $o).
% 0.59/0.84  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.59/0.84  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.59/0.84  thf(k7_funcop_1_type, type, k7_funcop_1: $i > $i > $i).
% 0.59/0.84  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.59/0.84  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.59/0.84  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.59/0.84  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.59/0.84  thf(k6_yellow_1_type, type, k6_yellow_1: $i > $i > $i).
% 0.59/0.84  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.59/0.84  thf(k5_yellow_1_type, type, k5_yellow_1: $i > $i > $i).
% 0.59/0.84  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.59/0.84  thf(v1_orders_2_type, type, v1_orders_2: $i > $o).
% 0.59/0.84  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.59/0.84  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.59/0.84  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.59/0.84  thf(g1_orders_2_type, type, g1_orders_2: $i > $i > $i).
% 0.59/0.84  thf(k2_funcop_1_type, type, k2_funcop_1: $i > $i > $i).
% 0.59/0.84  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.59/0.84  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.59/0.84  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.59/0.84  thf(sk_A_1_type, type, sk_A_1: $i).
% 0.59/0.84  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.59/0.84  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.59/0.84  thf(fc2_funcop_1, axiom,
% 0.59/0.84    (![A:$i]: ( v1_xboole_0 @ ( k2_funcop_1 @ k1_xboole_0 @ A ) ))).
% 0.59/0.84  thf('0', plain,
% 0.59/0.84      (![X42 : $i]: (v1_xboole_0 @ (k2_funcop_1 @ k1_xboole_0 @ X42))),
% 0.59/0.84      inference('cnf', [status(esa)], [fc2_funcop_1])).
% 0.59/0.84  thf(l13_xboole_0, axiom,
% 0.59/0.84    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.59/0.84  thf('1', plain,
% 0.59/0.84      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.59/0.84      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.59/0.84  thf('2', plain,
% 0.59/0.84      (![X0 : $i]: ((k2_funcop_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.59/0.84      inference('sup-', [status(thm)], ['0', '1'])).
% 0.59/0.84  thf(redefinition_k7_funcop_1, axiom,
% 0.59/0.84    (![A:$i,B:$i]: ( ( k7_funcop_1 @ A @ B ) = ( k2_funcop_1 @ A @ B ) ))).
% 0.59/0.84  thf('3', plain,
% 0.59/0.84      (![X43 : $i, X44 : $i]:
% 0.59/0.84         ((k7_funcop_1 @ X43 @ X44) = (k2_funcop_1 @ X43 @ X44))),
% 0.59/0.84      inference('cnf', [status(esa)], [redefinition_k7_funcop_1])).
% 0.59/0.84  thf('4', plain,
% 0.59/0.84      (![X0 : $i]: ((k7_funcop_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.59/0.84      inference('demod', [status(thm)], ['2', '3'])).
% 0.59/0.84  thf(d5_yellow_1, axiom,
% 0.59/0.84    (![A:$i,B:$i]:
% 0.59/0.84     ( ( l1_orders_2 @ B ) =>
% 0.59/0.84       ( ( k6_yellow_1 @ A @ B ) =
% 0.59/0.84         ( k5_yellow_1 @ A @ ( k7_funcop_1 @ A @ B ) ) ) ))).
% 0.59/0.84  thf('5', plain,
% 0.59/0.84      (![X38 : $i, X39 : $i]:
% 0.59/0.84         (((k6_yellow_1 @ X38 @ X39)
% 0.59/0.84            = (k5_yellow_1 @ X38 @ (k7_funcop_1 @ X38 @ X39)))
% 0.59/0.84          | ~ (l1_orders_2 @ X39))),
% 0.59/0.84      inference('cnf', [status(esa)], [d5_yellow_1])).
% 0.59/0.84  thf('6', plain,
% 0.59/0.84      (![X0 : $i]:
% 0.59/0.84         (((k6_yellow_1 @ k1_xboole_0 @ X0)
% 0.59/0.84            = (k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0))
% 0.59/0.84          | ~ (l1_orders_2 @ X0))),
% 0.59/0.84      inference('sup+', [status(thm)], ['4', '5'])).
% 0.59/0.84  thf(t27_yellow_1, conjecture,
% 0.59/0.84    (![A:$i]:
% 0.59/0.84     ( ( l1_orders_2 @ A ) =>
% 0.59/0.84       ( ( k6_yellow_1 @ k1_xboole_0 @ A ) =
% 0.59/0.84         ( g1_orders_2 @
% 0.59/0.84           ( k1_tarski @ k1_xboole_0 ) @ 
% 0.59/0.84           ( k6_partfun1 @ ( k1_tarski @ k1_xboole_0 ) ) ) ) ))).
% 0.59/0.84  thf(zf_stmt_0, negated_conjecture,
% 0.59/0.84    (~( ![A:$i]:
% 0.59/0.84        ( ( l1_orders_2 @ A ) =>
% 0.59/0.84          ( ( k6_yellow_1 @ k1_xboole_0 @ A ) =
% 0.59/0.84            ( g1_orders_2 @
% 0.59/0.84              ( k1_tarski @ k1_xboole_0 ) @ 
% 0.59/0.84              ( k6_partfun1 @ ( k1_tarski @ k1_xboole_0 ) ) ) ) ) )),
% 0.59/0.84    inference('cnf.neg', [status(esa)], [t27_yellow_1])).
% 0.59/0.84  thf('7', plain,
% 0.59/0.84      (((k6_yellow_1 @ k1_xboole_0 @ sk_A_1)
% 0.59/0.84         != (g1_orders_2 @ (k1_tarski @ k1_xboole_0) @ 
% 0.59/0.84             (k6_partfun1 @ (k1_tarski @ k1_xboole_0))))),
% 0.59/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.84  thf(redefinition_k6_partfun1, axiom,
% 0.59/0.84    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.59/0.84  thf('8', plain, (![X37 : $i]: ((k6_partfun1 @ X37) = (k6_relat_1 @ X37))),
% 0.59/0.84      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.59/0.84  thf('9', plain,
% 0.59/0.84      (((k6_yellow_1 @ k1_xboole_0 @ sk_A_1)
% 0.59/0.84         != (g1_orders_2 @ (k1_tarski @ k1_xboole_0) @ 
% 0.59/0.84             (k6_relat_1 @ (k1_tarski @ k1_xboole_0))))),
% 0.59/0.84      inference('demod', [status(thm)], ['7', '8'])).
% 0.59/0.84  thf('10', plain,
% 0.59/0.84      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.59/0.84      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.59/0.84  thf(t81_relat_1, axiom, (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.59/0.84  thf('11', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.59/0.84      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.59/0.84  thf('12', plain,
% 0.59/0.84      (![X0 : $i]: (((k6_relat_1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.59/0.84      inference('sup+', [status(thm)], ['10', '11'])).
% 0.59/0.84  thf(dt_k6_partfun1, axiom,
% 0.59/0.84    (![A:$i]:
% 0.59/0.84     ( ( m1_subset_1 @
% 0.59/0.84         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 0.59/0.84       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 0.59/0.84  thf('13', plain, (![X35 : $i]: (v1_partfun1 @ (k6_partfun1 @ X35) @ X35)),
% 0.59/0.84      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.59/0.84  thf('14', plain, (![X37 : $i]: ((k6_partfun1 @ X37) = (k6_relat_1 @ X37))),
% 0.59/0.84      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.59/0.84  thf('15', plain, (![X35 : $i]: (v1_partfun1 @ (k6_relat_1 @ X35) @ X35)),
% 0.59/0.84      inference('demod', [status(thm)], ['13', '14'])).
% 0.59/0.84  thf('16', plain,
% 0.59/0.84      (![X0 : $i]: ((v1_partfun1 @ k1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X0))),
% 0.59/0.84      inference('sup+', [status(thm)], ['12', '15'])).
% 0.59/0.84  thf(t26_yellow_1, axiom,
% 0.59/0.84    (![A:$i]:
% 0.59/0.84     ( ( ( v1_relat_1 @ A ) & ( v4_relat_1 @ A @ k1_xboole_0 ) & 
% 0.59/0.84         ( v1_funct_1 @ A ) & ( v1_partfun1 @ A @ k1_xboole_0 ) & 
% 0.59/0.84         ( v1_yellow_1 @ A ) ) =>
% 0.59/0.84       ( ( k5_yellow_1 @ k1_xboole_0 @ A ) =
% 0.59/0.84         ( g1_orders_2 @
% 0.59/0.84           ( k1_tarski @ k1_xboole_0 ) @ 
% 0.59/0.84           ( k6_partfun1 @ ( k1_tarski @ k1_xboole_0 ) ) ) ) ))).
% 0.59/0.84  thf('17', plain,
% 0.59/0.84      (![X45 : $i]:
% 0.59/0.84         (((k5_yellow_1 @ k1_xboole_0 @ X45)
% 0.59/0.84            = (g1_orders_2 @ (k1_tarski @ k1_xboole_0) @ 
% 0.59/0.84               (k6_partfun1 @ (k1_tarski @ k1_xboole_0))))
% 0.59/0.84          | ~ (v1_yellow_1 @ X45)
% 0.59/0.84          | ~ (v1_partfun1 @ X45 @ k1_xboole_0)
% 0.59/0.84          | ~ (v1_funct_1 @ X45)
% 0.59/0.84          | ~ (v4_relat_1 @ X45 @ k1_xboole_0)
% 0.59/0.84          | ~ (v1_relat_1 @ X45))),
% 0.59/0.84      inference('cnf', [status(esa)], [t26_yellow_1])).
% 0.59/0.84  thf('18', plain, (![X37 : $i]: ((k6_partfun1 @ X37) = (k6_relat_1 @ X37))),
% 0.59/0.84      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.59/0.84  thf('19', plain,
% 0.59/0.84      (![X45 : $i]:
% 0.59/0.84         (((k5_yellow_1 @ k1_xboole_0 @ X45)
% 0.59/0.84            = (g1_orders_2 @ (k1_tarski @ k1_xboole_0) @ 
% 0.59/0.84               (k6_relat_1 @ (k1_tarski @ k1_xboole_0))))
% 0.59/0.84          | ~ (v1_yellow_1 @ X45)
% 0.59/0.84          | ~ (v1_partfun1 @ X45 @ k1_xboole_0)
% 0.59/0.84          | ~ (v1_funct_1 @ X45)
% 0.59/0.84          | ~ (v4_relat_1 @ X45 @ k1_xboole_0)
% 0.59/0.84          | ~ (v1_relat_1 @ X45))),
% 0.59/0.84      inference('demod', [status(thm)], ['17', '18'])).
% 0.59/0.84  thf('20', plain,
% 0.59/0.84      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.59/0.84        | ~ (v1_relat_1 @ k1_xboole_0)
% 0.59/0.84        | ~ (v4_relat_1 @ k1_xboole_0 @ k1_xboole_0)
% 0.59/0.84        | ~ (v1_funct_1 @ k1_xboole_0)
% 0.59/0.84        | ~ (v1_yellow_1 @ k1_xboole_0)
% 0.59/0.84        | ((k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0)
% 0.59/0.84            = (g1_orders_2 @ (k1_tarski @ k1_xboole_0) @ 
% 0.59/0.84               (k6_relat_1 @ (k1_tarski @ k1_xboole_0)))))),
% 0.59/0.84      inference('sup-', [status(thm)], ['16', '19'])).
% 0.59/0.84  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.59/0.84  thf('21', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.59/0.84      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.59/0.84  thf('22', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.59/0.84      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.59/0.84  thf(fc3_funct_1, axiom,
% 0.59/0.84    (![A:$i]:
% 0.59/0.84     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.59/0.84       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.59/0.84  thf('23', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 0.59/0.84      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.59/0.84  thf('24', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.59/0.84      inference('sup+', [status(thm)], ['22', '23'])).
% 0.59/0.84  thf(t60_relat_1, axiom,
% 0.59/0.84    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.59/0.84     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.59/0.84  thf('25', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.59/0.84      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.59/0.84  thf(d18_relat_1, axiom,
% 0.59/0.84    (![A:$i,B:$i]:
% 0.59/0.84     ( ( v1_relat_1 @ B ) =>
% 0.59/0.84       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.59/0.84  thf('26', plain,
% 0.59/0.84      (![X31 : $i, X32 : $i]:
% 0.59/0.84         (~ (r1_tarski @ (k1_relat_1 @ X31) @ X32)
% 0.59/0.84          | (v4_relat_1 @ X31 @ X32)
% 0.59/0.84          | ~ (v1_relat_1 @ X31))),
% 0.59/0.84      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.59/0.84  thf('27', plain,
% 0.59/0.84      (![X0 : $i]:
% 0.59/0.84         (~ (r1_tarski @ k1_xboole_0 @ X0)
% 0.59/0.84          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.59/0.84          | (v4_relat_1 @ k1_xboole_0 @ X0))),
% 0.59/0.84      inference('sup-', [status(thm)], ['25', '26'])).
% 0.59/0.84  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.59/0.84  thf('28', plain, (![X1 : $i]: (r1_tarski @ k1_xboole_0 @ X1)),
% 0.59/0.84      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.59/0.84  thf('29', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.59/0.84      inference('sup+', [status(thm)], ['22', '23'])).
% 0.59/0.84  thf('30', plain, (![X0 : $i]: (v4_relat_1 @ k1_xboole_0 @ X0)),
% 0.59/0.84      inference('demod', [status(thm)], ['27', '28', '29'])).
% 0.59/0.84  thf('31', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.59/0.84      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.59/0.84  thf('32', plain, (![X34 : $i]: (v1_funct_1 @ (k6_relat_1 @ X34))),
% 0.59/0.84      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.59/0.84  thf('33', plain, ((v1_funct_1 @ k1_xboole_0)),
% 0.59/0.84      inference('sup+', [status(thm)], ['31', '32'])).
% 0.59/0.84  thf(rc1_orders_2, axiom,
% 0.59/0.84    (?[A:$i]: ( ( v1_orders_2 @ A ) & ( l1_orders_2 @ A ) ))).
% 0.59/0.84  thf('34', plain, ((l1_orders_2 @ sk_A)),
% 0.59/0.84      inference('cnf', [status(esa)], [rc1_orders_2])).
% 0.59/0.84  thf('35', plain,
% 0.59/0.84      (![X0 : $i]: ((k7_funcop_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.59/0.84      inference('demod', [status(thm)], ['2', '3'])).
% 0.59/0.84  thf(fc10_yellow_1, axiom,
% 0.59/0.84    (![A:$i,B:$i]:
% 0.59/0.84     ( ( l1_orders_2 @ B ) => ( v1_yellow_1 @ ( k2_funcop_1 @ A @ B ) ) ))).
% 0.59/0.84  thf('36', plain,
% 0.59/0.84      (![X40 : $i, X41 : $i]:
% 0.59/0.84         ((v1_yellow_1 @ (k2_funcop_1 @ X40 @ X41)) | ~ (l1_orders_2 @ X41))),
% 0.59/0.84      inference('cnf', [status(esa)], [fc10_yellow_1])).
% 0.59/0.84  thf('37', plain,
% 0.59/0.84      (![X43 : $i, X44 : $i]:
% 0.59/0.84         ((k7_funcop_1 @ X43 @ X44) = (k2_funcop_1 @ X43 @ X44))),
% 0.59/0.84      inference('cnf', [status(esa)], [redefinition_k7_funcop_1])).
% 0.59/0.84  thf('38', plain,
% 0.59/0.84      (![X40 : $i, X41 : $i]:
% 0.59/0.84         ((v1_yellow_1 @ (k7_funcop_1 @ X40 @ X41)) | ~ (l1_orders_2 @ X41))),
% 0.59/0.84      inference('demod', [status(thm)], ['36', '37'])).
% 0.59/0.84  thf('39', plain,
% 0.59/0.84      (![X0 : $i]: ((v1_yellow_1 @ k1_xboole_0) | ~ (l1_orders_2 @ X0))),
% 0.59/0.84      inference('sup+', [status(thm)], ['35', '38'])).
% 0.59/0.84  thf('40', plain, ((v1_yellow_1 @ k1_xboole_0)),
% 0.59/0.84      inference('sup-', [status(thm)], ['34', '39'])).
% 0.59/0.84  thf('41', plain,
% 0.59/0.84      (((k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0)
% 0.59/0.84         = (g1_orders_2 @ (k1_tarski @ k1_xboole_0) @ 
% 0.59/0.84            (k6_relat_1 @ (k1_tarski @ k1_xboole_0))))),
% 0.59/0.84      inference('demod', [status(thm)], ['20', '21', '24', '30', '33', '40'])).
% 0.59/0.84  thf('42', plain,
% 0.59/0.84      (((k6_yellow_1 @ k1_xboole_0 @ sk_A_1)
% 0.59/0.84         != (k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0))),
% 0.59/0.84      inference('demod', [status(thm)], ['9', '41'])).
% 0.59/0.84  thf('43', plain,
% 0.59/0.84      (![X0 : $i]:
% 0.59/0.84         (((k6_yellow_1 @ k1_xboole_0 @ sk_A_1)
% 0.59/0.84            != (k6_yellow_1 @ k1_xboole_0 @ X0))
% 0.59/0.84          | ~ (l1_orders_2 @ X0))),
% 0.59/0.84      inference('sup-', [status(thm)], ['6', '42'])).
% 0.59/0.84  thf('44', plain, (~ (l1_orders_2 @ sk_A_1)),
% 0.59/0.84      inference('eq_res', [status(thm)], ['43'])).
% 0.59/0.84  thf('45', plain, ((l1_orders_2 @ sk_A_1)),
% 0.59/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.84  thf('46', plain, ($false), inference('demod', [status(thm)], ['44', '45'])).
% 0.59/0.84  
% 0.59/0.84  % SZS output end Refutation
% 0.59/0.84  
% 0.59/0.84  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
