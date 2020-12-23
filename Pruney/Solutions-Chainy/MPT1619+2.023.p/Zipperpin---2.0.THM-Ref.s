%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.VPgfCijSFR

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:27 EST 2020

% Result     : Theorem 0.44s
% Output     : Refutation 0.44s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 114 expanded)
%              Number of leaves         :   33 (  52 expanded)
%              Depth                    :   12
%              Number of atoms          :  419 ( 598 expanded)
%              Number of equality atoms :   36 (  57 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_yellow_1_type,type,(
    v1_yellow_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_funcop_1_type,type,(
    k2_funcop_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(g1_orders_2_type,type,(
    g1_orders_2: $i > $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(k6_yellow_1_type,type,(
    k6_yellow_1: $i > $i > $i )).

thf(k5_yellow_1_type,type,(
    k5_yellow_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k7_funcop_1_type,type,(
    k7_funcop_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(fc2_funcop_1,axiom,(
    ! [A: $i] :
      ( v1_xboole_0 @ ( k2_funcop_1 @ k1_xboole_0 @ A ) ) )).

thf('0',plain,(
    ! [X40: $i] :
      ( v1_xboole_0 @ ( k2_funcop_1 @ k1_xboole_0 @ X40 ) ) ),
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
    ! [X41: $i,X42: $i] :
      ( ( k7_funcop_1 @ X41 @ X42 )
      = ( k2_funcop_1 @ X41 @ X42 ) ) ),
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
    ( k6_yellow_1 @ k1_xboole_0 @ sk_A )
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
    inference(demod,[status(thm)],['2','3'])).

thf(fc10_yellow_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( l1_orders_2 @ B )
     => ( v1_yellow_1 @ ( k2_funcop_1 @ A @ B ) ) ) )).

thf('13',plain,(
    ! [X38: $i,X39: $i] :
      ( ( v1_yellow_1 @ ( k2_funcop_1 @ X38 @ X39 ) )
      | ~ ( l1_orders_2 @ X39 ) ) ),
    inference(cnf,[status(esa)],[fc10_yellow_1])).

thf('14',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k7_funcop_1 @ X41 @ X42 )
      = ( k2_funcop_1 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_funcop_1])).

thf('15',plain,(
    ! [X38: $i,X39: $i] :
      ( ( v1_yellow_1 @ ( k7_funcop_1 @ X38 @ X39 ) )
      | ~ ( l1_orders_2 @ X39 ) ) ),
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
    ! [X33: $i] :
      ( v1_partfun1 @ ( k6_partfun1 @ X33 ) @ X33 ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('23',plain,(
    ! [X35: $i] :
      ( ( k6_partfun1 @ X35 )
      = ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('24',plain,(
    ! [X33: $i] :
      ( v1_partfun1 @ ( k6_relat_1 @ X33 ) @ X33 ) ),
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
    ! [X43: $i] :
      ( ( ( k5_yellow_1 @ k1_xboole_0 @ X43 )
        = ( g1_orders_2 @ ( k1_tarski @ k1_xboole_0 ) @ ( k6_partfun1 @ ( k1_tarski @ k1_xboole_0 ) ) ) )
      | ~ ( v1_yellow_1 @ X43 )
      | ~ ( v1_partfun1 @ X43 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( v4_relat_1 @ X43 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t26_yellow_1])).

thf('27',plain,(
    ! [X35: $i] :
      ( ( k6_partfun1 @ X35 )
      = ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('28',plain,(
    ! [X43: $i] :
      ( ( ( k5_yellow_1 @ k1_xboole_0 @ X43 )
        = ( g1_orders_2 @ ( k1_tarski @ k1_xboole_0 ) @ ( k6_relat_1 @ ( k1_tarski @ k1_xboole_0 ) ) ) )
      | ~ ( v1_yellow_1 @ X43 )
      | ~ ( v1_partfun1 @ X43 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( v4_relat_1 @ X43 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X43 ) ) ),
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
    ! [X40: $i] :
      ( v1_xboole_0 @ ( k2_funcop_1 @ k1_xboole_0 @ X40 ) ) ),
    inference(cnf,[status(esa)],[fc2_funcop_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k2_funcop_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('32',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('34',plain,(
    ! [X31: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('35',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['33','34'])).

thf(l222_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v5_relat_1 @ k1_xboole_0 @ B )
      & ( v4_relat_1 @ k1_xboole_0 @ A ) ) )).

thf('36',plain,(
    ! [X30: $i] :
      ( v4_relat_1 @ k1_xboole_0 @ X30 ) ),
    inference(cnf,[status(esa)],[l222_relat_1])).

thf('37',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf('38',plain,(
    ! [X32: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('39',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,
    ( ~ ( v1_yellow_1 @ k1_xboole_0 )
    | ( ( k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0 )
      = ( g1_orders_2 @ ( k1_tarski @ k1_xboole_0 ) @ ( k6_relat_1 @ ( k1_tarski @ k1_xboole_0 ) ) ) ) ),
    inference(demod,[status(thm)],['29','32','35','36','39'])).

thf('41',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( ( k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0 )
      = ( g1_orders_2 @ ( k1_tarski @ k1_xboole_0 ) @ ( k6_relat_1 @ ( k1_tarski @ k1_xboole_0 ) ) ) ) ),
    inference('sup-',[status(thm)],['18','40'])).

thf('42',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['30','31'])).

thf('43',plain,
    ( ( k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0 )
    = ( g1_orders_2 @ ( k1_tarski @ k1_xboole_0 ) @ ( k6_relat_1 @ ( k1_tarski @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ( k6_yellow_1 @ k1_xboole_0 @ sk_A )
 != ( k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['9','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( ( k6_yellow_1 @ k1_xboole_0 @ sk_A )
       != ( k6_yellow_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','44'])).

thf('46',plain,(
    ~ ( l1_orders_2 @ sk_A ) ),
    inference(eq_res,[status(thm)],['45'])).

thf('47',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    $false ),
    inference(demod,[status(thm)],['46','47'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.VPgfCijSFR
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:54:32 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.44/0.66  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.44/0.66  % Solved by: fo/fo7.sh
% 0.44/0.66  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.44/0.66  % done 172 iterations in 0.202s
% 0.44/0.66  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.44/0.66  % SZS output start Refutation
% 0.44/0.66  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.44/0.66  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.44/0.66  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.44/0.66  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.44/0.66  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.44/0.66  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.44/0.66  thf(v1_yellow_1_type, type, v1_yellow_1: $i > $o).
% 0.44/0.66  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.44/0.66  thf(k2_funcop_1_type, type, k2_funcop_1: $i > $i > $i).
% 0.44/0.66  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.44/0.66  thf(g1_orders_2_type, type, g1_orders_2: $i > $i > $i).
% 0.44/0.66  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.44/0.66  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.44/0.66  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.44/0.66  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.44/0.66  thf(k6_yellow_1_type, type, k6_yellow_1: $i > $i > $i).
% 0.44/0.66  thf(k5_yellow_1_type, type, k5_yellow_1: $i > $i > $i).
% 0.44/0.66  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.44/0.66  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.44/0.66  thf(k7_funcop_1_type, type, k7_funcop_1: $i > $i > $i).
% 0.44/0.66  thf(sk_A_type, type, sk_A: $i).
% 0.44/0.66  thf(fc2_funcop_1, axiom,
% 0.44/0.66    (![A:$i]: ( v1_xboole_0 @ ( k2_funcop_1 @ k1_xboole_0 @ A ) ))).
% 0.44/0.66  thf('0', plain,
% 0.44/0.66      (![X40 : $i]: (v1_xboole_0 @ (k2_funcop_1 @ k1_xboole_0 @ X40))),
% 0.44/0.66      inference('cnf', [status(esa)], [fc2_funcop_1])).
% 0.44/0.66  thf(l13_xboole_0, axiom,
% 0.44/0.66    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.44/0.66  thf('1', plain,
% 0.44/0.66      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.44/0.66      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.44/0.66  thf('2', plain,
% 0.44/0.66      (![X0 : $i]: ((k2_funcop_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.44/0.66      inference('sup-', [status(thm)], ['0', '1'])).
% 0.44/0.66  thf(redefinition_k7_funcop_1, axiom,
% 0.44/0.66    (![A:$i,B:$i]: ( ( k7_funcop_1 @ A @ B ) = ( k2_funcop_1 @ A @ B ) ))).
% 0.44/0.66  thf('3', plain,
% 0.44/0.66      (![X41 : $i, X42 : $i]:
% 0.44/0.66         ((k7_funcop_1 @ X41 @ X42) = (k2_funcop_1 @ X41 @ X42))),
% 0.44/0.66      inference('cnf', [status(esa)], [redefinition_k7_funcop_1])).
% 0.44/0.66  thf('4', plain,
% 0.44/0.66      (![X0 : $i]: ((k7_funcop_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.44/0.66      inference('demod', [status(thm)], ['2', '3'])).
% 0.44/0.66  thf(d5_yellow_1, axiom,
% 0.44/0.66    (![A:$i,B:$i]:
% 0.44/0.66     ( ( l1_orders_2 @ B ) =>
% 0.44/0.66       ( ( k6_yellow_1 @ A @ B ) =
% 0.44/0.66         ( k5_yellow_1 @ A @ ( k7_funcop_1 @ A @ B ) ) ) ))).
% 0.44/0.66  thf('5', plain,
% 0.44/0.66      (![X36 : $i, X37 : $i]:
% 0.44/0.66         (((k6_yellow_1 @ X36 @ X37)
% 0.44/0.66            = (k5_yellow_1 @ X36 @ (k7_funcop_1 @ X36 @ X37)))
% 0.44/0.66          | ~ (l1_orders_2 @ X37))),
% 0.44/0.66      inference('cnf', [status(esa)], [d5_yellow_1])).
% 0.44/0.66  thf('6', plain,
% 0.44/0.66      (![X0 : $i]:
% 0.44/0.66         (((k6_yellow_1 @ k1_xboole_0 @ X0)
% 0.44/0.66            = (k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0))
% 0.44/0.66          | ~ (l1_orders_2 @ X0))),
% 0.44/0.66      inference('sup+', [status(thm)], ['4', '5'])).
% 0.44/0.66  thf(t27_yellow_1, conjecture,
% 0.44/0.66    (![A:$i]:
% 0.44/0.66     ( ( l1_orders_2 @ A ) =>
% 0.44/0.66       ( ( k6_yellow_1 @ k1_xboole_0 @ A ) =
% 0.44/0.66         ( g1_orders_2 @
% 0.44/0.66           ( k1_tarski @ k1_xboole_0 ) @ 
% 0.44/0.66           ( k6_partfun1 @ ( k1_tarski @ k1_xboole_0 ) ) ) ) ))).
% 0.44/0.66  thf(zf_stmt_0, negated_conjecture,
% 0.44/0.66    (~( ![A:$i]:
% 0.44/0.66        ( ( l1_orders_2 @ A ) =>
% 0.44/0.66          ( ( k6_yellow_1 @ k1_xboole_0 @ A ) =
% 0.44/0.66            ( g1_orders_2 @
% 0.44/0.66              ( k1_tarski @ k1_xboole_0 ) @ 
% 0.44/0.66              ( k6_partfun1 @ ( k1_tarski @ k1_xboole_0 ) ) ) ) ) )),
% 0.44/0.66    inference('cnf.neg', [status(esa)], [t27_yellow_1])).
% 0.44/0.66  thf('7', plain,
% 0.44/0.66      (((k6_yellow_1 @ k1_xboole_0 @ sk_A)
% 0.44/0.66         != (g1_orders_2 @ (k1_tarski @ k1_xboole_0) @ 
% 0.44/0.66             (k6_partfun1 @ (k1_tarski @ k1_xboole_0))))),
% 0.44/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.66  thf(redefinition_k6_partfun1, axiom,
% 0.44/0.66    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.44/0.66  thf('8', plain, (![X35 : $i]: ((k6_partfun1 @ X35) = (k6_relat_1 @ X35))),
% 0.44/0.66      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.44/0.66  thf('9', plain,
% 0.44/0.66      (((k6_yellow_1 @ k1_xboole_0 @ sk_A)
% 0.44/0.66         != (g1_orders_2 @ (k1_tarski @ k1_xboole_0) @ 
% 0.44/0.66             (k6_relat_1 @ (k1_tarski @ k1_xboole_0))))),
% 0.44/0.66      inference('demod', [status(thm)], ['7', '8'])).
% 0.44/0.66  thf('10', plain, ((l1_orders_2 @ sk_A)),
% 0.44/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.66  thf('11', plain,
% 0.44/0.66      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.44/0.66      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.44/0.66  thf('12', plain,
% 0.44/0.66      (![X0 : $i]: ((k7_funcop_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.44/0.66      inference('demod', [status(thm)], ['2', '3'])).
% 0.44/0.66  thf(fc10_yellow_1, axiom,
% 0.44/0.66    (![A:$i,B:$i]:
% 0.44/0.66     ( ( l1_orders_2 @ B ) => ( v1_yellow_1 @ ( k2_funcop_1 @ A @ B ) ) ))).
% 0.44/0.66  thf('13', plain,
% 0.44/0.66      (![X38 : $i, X39 : $i]:
% 0.44/0.66         ((v1_yellow_1 @ (k2_funcop_1 @ X38 @ X39)) | ~ (l1_orders_2 @ X39))),
% 0.44/0.66      inference('cnf', [status(esa)], [fc10_yellow_1])).
% 0.44/0.66  thf('14', plain,
% 0.44/0.66      (![X41 : $i, X42 : $i]:
% 0.44/0.66         ((k7_funcop_1 @ X41 @ X42) = (k2_funcop_1 @ X41 @ X42))),
% 0.44/0.66      inference('cnf', [status(esa)], [redefinition_k7_funcop_1])).
% 0.44/0.66  thf('15', plain,
% 0.44/0.66      (![X38 : $i, X39 : $i]:
% 0.44/0.66         ((v1_yellow_1 @ (k7_funcop_1 @ X38 @ X39)) | ~ (l1_orders_2 @ X39))),
% 0.44/0.66      inference('demod', [status(thm)], ['13', '14'])).
% 0.44/0.66  thf('16', plain,
% 0.44/0.66      (![X0 : $i]: ((v1_yellow_1 @ k1_xboole_0) | ~ (l1_orders_2 @ X0))),
% 0.44/0.66      inference('sup+', [status(thm)], ['12', '15'])).
% 0.44/0.66  thf('17', plain,
% 0.44/0.66      (![X0 : $i, X1 : $i]:
% 0.44/0.66         ((v1_yellow_1 @ X0) | ~ (v1_xboole_0 @ X0) | ~ (l1_orders_2 @ X1))),
% 0.44/0.66      inference('sup+', [status(thm)], ['11', '16'])).
% 0.44/0.66  thf('18', plain, (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (v1_yellow_1 @ X0))),
% 0.44/0.66      inference('sup-', [status(thm)], ['10', '17'])).
% 0.44/0.66  thf('19', plain,
% 0.44/0.66      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.44/0.66      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.44/0.66  thf(t81_relat_1, axiom, (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.44/0.66  thf('20', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.44/0.66      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.44/0.66  thf('21', plain,
% 0.44/0.66      (![X0 : $i]: (((k6_relat_1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.44/0.66      inference('sup+', [status(thm)], ['19', '20'])).
% 0.44/0.66  thf(dt_k6_partfun1, axiom,
% 0.44/0.66    (![A:$i]:
% 0.44/0.66     ( ( m1_subset_1 @
% 0.44/0.66         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 0.44/0.66       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 0.44/0.66  thf('22', plain, (![X33 : $i]: (v1_partfun1 @ (k6_partfun1 @ X33) @ X33)),
% 0.44/0.66      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.44/0.66  thf('23', plain, (![X35 : $i]: ((k6_partfun1 @ X35) = (k6_relat_1 @ X35))),
% 0.44/0.66      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.44/0.66  thf('24', plain, (![X33 : $i]: (v1_partfun1 @ (k6_relat_1 @ X33) @ X33)),
% 0.44/0.66      inference('demod', [status(thm)], ['22', '23'])).
% 0.44/0.66  thf('25', plain,
% 0.44/0.66      (![X0 : $i]: ((v1_partfun1 @ k1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X0))),
% 0.44/0.66      inference('sup+', [status(thm)], ['21', '24'])).
% 0.44/0.66  thf(t26_yellow_1, axiom,
% 0.44/0.66    (![A:$i]:
% 0.44/0.66     ( ( ( v1_relat_1 @ A ) & ( v4_relat_1 @ A @ k1_xboole_0 ) & 
% 0.44/0.66         ( v1_funct_1 @ A ) & ( v1_partfun1 @ A @ k1_xboole_0 ) & 
% 0.44/0.66         ( v1_yellow_1 @ A ) ) =>
% 0.44/0.66       ( ( k5_yellow_1 @ k1_xboole_0 @ A ) =
% 0.44/0.66         ( g1_orders_2 @
% 0.44/0.66           ( k1_tarski @ k1_xboole_0 ) @ 
% 0.44/0.66           ( k6_partfun1 @ ( k1_tarski @ k1_xboole_0 ) ) ) ) ))).
% 0.44/0.66  thf('26', plain,
% 0.44/0.66      (![X43 : $i]:
% 0.44/0.66         (((k5_yellow_1 @ k1_xboole_0 @ X43)
% 0.44/0.66            = (g1_orders_2 @ (k1_tarski @ k1_xboole_0) @ 
% 0.44/0.66               (k6_partfun1 @ (k1_tarski @ k1_xboole_0))))
% 0.44/0.66          | ~ (v1_yellow_1 @ X43)
% 0.44/0.66          | ~ (v1_partfun1 @ X43 @ k1_xboole_0)
% 0.44/0.66          | ~ (v1_funct_1 @ X43)
% 0.44/0.66          | ~ (v4_relat_1 @ X43 @ k1_xboole_0)
% 0.44/0.66          | ~ (v1_relat_1 @ X43))),
% 0.44/0.66      inference('cnf', [status(esa)], [t26_yellow_1])).
% 0.44/0.66  thf('27', plain, (![X35 : $i]: ((k6_partfun1 @ X35) = (k6_relat_1 @ X35))),
% 0.44/0.66      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.44/0.66  thf('28', plain,
% 0.44/0.66      (![X43 : $i]:
% 0.44/0.66         (((k5_yellow_1 @ k1_xboole_0 @ X43)
% 0.44/0.66            = (g1_orders_2 @ (k1_tarski @ k1_xboole_0) @ 
% 0.44/0.66               (k6_relat_1 @ (k1_tarski @ k1_xboole_0))))
% 0.44/0.66          | ~ (v1_yellow_1 @ X43)
% 0.44/0.66          | ~ (v1_partfun1 @ X43 @ k1_xboole_0)
% 0.44/0.66          | ~ (v1_funct_1 @ X43)
% 0.44/0.66          | ~ (v4_relat_1 @ X43 @ k1_xboole_0)
% 0.44/0.66          | ~ (v1_relat_1 @ X43))),
% 0.44/0.66      inference('demod', [status(thm)], ['26', '27'])).
% 0.44/0.66  thf('29', plain,
% 0.44/0.66      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.44/0.66        | ~ (v1_relat_1 @ k1_xboole_0)
% 0.44/0.66        | ~ (v4_relat_1 @ k1_xboole_0 @ k1_xboole_0)
% 0.44/0.66        | ~ (v1_funct_1 @ k1_xboole_0)
% 0.44/0.66        | ~ (v1_yellow_1 @ k1_xboole_0)
% 0.44/0.66        | ((k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0)
% 0.44/0.66            = (g1_orders_2 @ (k1_tarski @ k1_xboole_0) @ 
% 0.44/0.66               (k6_relat_1 @ (k1_tarski @ k1_xboole_0)))))),
% 0.44/0.66      inference('sup-', [status(thm)], ['25', '28'])).
% 0.44/0.66  thf('30', plain,
% 0.44/0.66      (![X40 : $i]: (v1_xboole_0 @ (k2_funcop_1 @ k1_xboole_0 @ X40))),
% 0.44/0.66      inference('cnf', [status(esa)], [fc2_funcop_1])).
% 0.44/0.66  thf('31', plain,
% 0.44/0.66      (![X0 : $i]: ((k2_funcop_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.44/0.66      inference('sup-', [status(thm)], ['0', '1'])).
% 0.44/0.66  thf('32', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.44/0.66      inference('demod', [status(thm)], ['30', '31'])).
% 0.44/0.66  thf('33', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.44/0.66      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.44/0.66  thf(fc3_funct_1, axiom,
% 0.44/0.66    (![A:$i]:
% 0.44/0.66     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.44/0.66       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.44/0.66  thf('34', plain, (![X31 : $i]: (v1_relat_1 @ (k6_relat_1 @ X31))),
% 0.44/0.66      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.44/0.66  thf('35', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.44/0.66      inference('sup+', [status(thm)], ['33', '34'])).
% 0.44/0.66  thf(l222_relat_1, axiom,
% 0.44/0.66    (![A:$i,B:$i]:
% 0.44/0.66     ( ( v5_relat_1 @ k1_xboole_0 @ B ) & ( v4_relat_1 @ k1_xboole_0 @ A ) ))).
% 0.44/0.66  thf('36', plain, (![X30 : $i]: (v4_relat_1 @ k1_xboole_0 @ X30)),
% 0.44/0.66      inference('cnf', [status(esa)], [l222_relat_1])).
% 0.44/0.66  thf('37', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.44/0.66      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.44/0.66  thf('38', plain, (![X32 : $i]: (v1_funct_1 @ (k6_relat_1 @ X32))),
% 0.44/0.66      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.44/0.66  thf('39', plain, ((v1_funct_1 @ k1_xboole_0)),
% 0.44/0.66      inference('sup+', [status(thm)], ['37', '38'])).
% 0.44/0.66  thf('40', plain,
% 0.44/0.66      ((~ (v1_yellow_1 @ k1_xboole_0)
% 0.44/0.66        | ((k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0)
% 0.44/0.66            = (g1_orders_2 @ (k1_tarski @ k1_xboole_0) @ 
% 0.44/0.66               (k6_relat_1 @ (k1_tarski @ k1_xboole_0)))))),
% 0.44/0.66      inference('demod', [status(thm)], ['29', '32', '35', '36', '39'])).
% 0.44/0.66  thf('41', plain,
% 0.44/0.66      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.44/0.66        | ((k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0)
% 0.44/0.66            = (g1_orders_2 @ (k1_tarski @ k1_xboole_0) @ 
% 0.44/0.66               (k6_relat_1 @ (k1_tarski @ k1_xboole_0)))))),
% 0.44/0.66      inference('sup-', [status(thm)], ['18', '40'])).
% 0.44/0.66  thf('42', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.44/0.66      inference('demod', [status(thm)], ['30', '31'])).
% 0.44/0.66  thf('43', plain,
% 0.44/0.66      (((k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0)
% 0.44/0.66         = (g1_orders_2 @ (k1_tarski @ k1_xboole_0) @ 
% 0.44/0.66            (k6_relat_1 @ (k1_tarski @ k1_xboole_0))))),
% 0.44/0.66      inference('demod', [status(thm)], ['41', '42'])).
% 0.44/0.66  thf('44', plain,
% 0.44/0.66      (((k6_yellow_1 @ k1_xboole_0 @ sk_A)
% 0.44/0.66         != (k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0))),
% 0.44/0.66      inference('demod', [status(thm)], ['9', '43'])).
% 0.44/0.66  thf('45', plain,
% 0.44/0.66      (![X0 : $i]:
% 0.44/0.66         (((k6_yellow_1 @ k1_xboole_0 @ sk_A)
% 0.44/0.66            != (k6_yellow_1 @ k1_xboole_0 @ X0))
% 0.44/0.66          | ~ (l1_orders_2 @ X0))),
% 0.44/0.66      inference('sup-', [status(thm)], ['6', '44'])).
% 0.44/0.66  thf('46', plain, (~ (l1_orders_2 @ sk_A)),
% 0.44/0.66      inference('eq_res', [status(thm)], ['45'])).
% 0.44/0.66  thf('47', plain, ((l1_orders_2 @ sk_A)),
% 0.44/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.66  thf('48', plain, ($false), inference('demod', [status(thm)], ['46', '47'])).
% 0.44/0.66  
% 0.44/0.66  % SZS output end Refutation
% 0.44/0.66  
% 0.44/0.67  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
