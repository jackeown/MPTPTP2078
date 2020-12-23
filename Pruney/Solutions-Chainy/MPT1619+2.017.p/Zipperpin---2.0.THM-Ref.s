%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.24OC1nNPQT

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:26 EST 2020

% Result     : Theorem 0.44s
% Output     : Refutation 0.44s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 128 expanded)
%              Number of leaves         :   44 (  64 expanded)
%              Depth                    :   12
%              Number of atoms          :  460 ( 634 expanded)
%              Number of equality atoms :   41 (  61 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(g1_orders_2_type,type,(
    g1_orders_2: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k6_yellow_1_type,type,(
    k6_yellow_1: $i > $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_funcop_1_type,type,(
    k2_funcop_1: $i > $i > $i )).

thf(v1_yellow_1_type,type,(
    v1_yellow_1: $i > $o )).

thf(k5_yellow_1_type,type,(
    k5_yellow_1: $i > $i > $i )).

thf(v5_ordinal1_type,type,(
    v5_ordinal1: $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v1_orders_2_type,type,(
    v1_orders_2: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k7_funcop_1_type,type,(
    k7_funcop_1: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_1_type,type,(
    sk_A_1: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(d5_yellow_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( l1_orders_2 @ B )
     => ( ( k6_yellow_1 @ A @ B )
        = ( k5_yellow_1 @ A @ ( k7_funcop_1 @ A @ B ) ) ) ) )).

thf('0',plain,(
    ! [X36: $i,X37: $i] :
      ( ( ( k6_yellow_1 @ X36 @ X37 )
        = ( k5_yellow_1 @ X36 @ ( k7_funcop_1 @ X36 @ X37 ) ) )
      | ~ ( l1_orders_2 @ X37 ) ) ),
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

thf(t1_zfmisc_1,axiom,
    ( ( k1_zfmisc_1 @ k1_xboole_0 )
    = ( k1_tarski @ k1_xboole_0 ) )).

thf('3',plain,
    ( ( k1_zfmisc_1 @ k1_xboole_0 )
    = ( k1_tarski @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t1_zfmisc_1])).

thf('4',plain,
    ( ( k1_zfmisc_1 @ k1_xboole_0 )
    = ( k1_tarski @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t1_zfmisc_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('5',plain,(
    ! [X35: $i] :
      ( ( k6_partfun1 @ X35 )
      = ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('6',plain,(
    ( k6_yellow_1 @ k1_xboole_0 @ sk_A_1 )
 != ( g1_orders_2 @ ( k1_zfmisc_1 @ k1_xboole_0 ) @ ( k6_relat_1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['2','3','4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t81_relat_1,axiom,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('8',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( ( k6_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('10',plain,(
    ! [X33: $i] :
      ( v1_partfun1 @ ( k6_partfun1 @ X33 ) @ X33 ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('11',plain,(
    ! [X35: $i] :
      ( ( k6_partfun1 @ X35 )
      = ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('12',plain,(
    ! [X33: $i] :
      ( v1_partfun1 @ ( k6_relat_1 @ X33 ) @ X33 ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( v1_partfun1 @ k1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','12'])).

thf(t26_yellow_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v4_relat_1 @ A @ k1_xboole_0 )
        & ( v1_funct_1 @ A )
        & ( v1_partfun1 @ A @ k1_xboole_0 )
        & ( v1_yellow_1 @ A ) )
     => ( ( k5_yellow_1 @ k1_xboole_0 @ A )
        = ( g1_orders_2 @ ( k1_tarski @ k1_xboole_0 ) @ ( k6_partfun1 @ ( k1_tarski @ k1_xboole_0 ) ) ) ) ) )).

thf('14',plain,(
    ! [X43: $i] :
      ( ( ( k5_yellow_1 @ k1_xboole_0 @ X43 )
        = ( g1_orders_2 @ ( k1_tarski @ k1_xboole_0 ) @ ( k6_partfun1 @ ( k1_tarski @ k1_xboole_0 ) ) ) )
      | ~ ( v1_yellow_1 @ X43 )
      | ~ ( v1_partfun1 @ X43 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( v4_relat_1 @ X43 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t26_yellow_1])).

thf('15',plain,
    ( ( k1_zfmisc_1 @ k1_xboole_0 )
    = ( k1_tarski @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t1_zfmisc_1])).

thf('16',plain,
    ( ( k1_zfmisc_1 @ k1_xboole_0 )
    = ( k1_tarski @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t1_zfmisc_1])).

thf('17',plain,(
    ! [X35: $i] :
      ( ( k6_partfun1 @ X35 )
      = ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('18',plain,(
    ! [X43: $i] :
      ( ( ( k5_yellow_1 @ k1_xboole_0 @ X43 )
        = ( g1_orders_2 @ ( k1_zfmisc_1 @ k1_xboole_0 ) @ ( k6_relat_1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ) )
      | ~ ( v1_yellow_1 @ X43 )
      | ~ ( v1_partfun1 @ X43 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( v4_relat_1 @ X43 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X43 ) ) ),
    inference(demod,[status(thm)],['14','15','16','17'])).

thf('19',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 )
    | ~ ( v4_relat_1 @ k1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_funct_1 @ k1_xboole_0 )
    | ~ ( v1_yellow_1 @ k1_xboole_0 )
    | ( ( k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0 )
      = ( g1_orders_2 @ ( k1_zfmisc_1 @ k1_xboole_0 ) @ ( k6_relat_1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ) ) ),
    inference('sup-',[status(thm)],['13','18'])).

thf(fc2_funcop_1,axiom,(
    ! [A: $i] :
      ( v1_xboole_0 @ ( k2_funcop_1 @ k1_xboole_0 @ A ) ) )).

thf('20',plain,(
    ! [X40: $i] :
      ( v1_xboole_0 @ ( k2_funcop_1 @ k1_xboole_0 @ X40 ) ) ),
    inference(cnf,[status(esa)],[fc2_funcop_1])).

thf('21',plain,(
    ! [X40: $i] :
      ( v1_xboole_0 @ ( k2_funcop_1 @ k1_xboole_0 @ X40 ) ) ),
    inference(cnf,[status(esa)],[fc2_funcop_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k2_funcop_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['20','23'])).

thf(t45_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v5_ordinal1 @ k1_xboole_0 )
      & ( v1_funct_1 @ k1_xboole_0 )
      & ( v5_relat_1 @ k1_xboole_0 @ A )
      & ( v1_relat_1 @ k1_xboole_0 ) ) )).

thf('25',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[t45_ordinal1])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('26',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('27',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X30 ) @ X31 )
      | ( v4_relat_1 @ X30 @ X31 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( v4_relat_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('29',plain,(
    ! [X1: $i] :
      ( r1_tarski @ k1_xboole_0 @ X1 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('30',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[t45_ordinal1])).

thf('31',plain,(
    ! [X0: $i] :
      ( v4_relat_1 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['28','29','30'])).

thf('32',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[t45_ordinal1])).

thf(rc4_orders_2,axiom,(
    ? [A: $i] :
      ( ( v1_orders_2 @ A )
      & ( v2_struct_0 @ A )
      & ( l1_orders_2 @ A ) ) )).

thf('33',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[rc4_orders_2])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k2_funcop_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf(redefinition_k7_funcop_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k7_funcop_1 @ A @ B )
      = ( k2_funcop_1 @ A @ B ) ) )).

thf('35',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k7_funcop_1 @ X41 @ X42 )
      = ( k2_funcop_1 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_funcop_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k7_funcop_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['34','35'])).

thf(fc10_yellow_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( l1_orders_2 @ B )
     => ( v1_yellow_1 @ ( k2_funcop_1 @ A @ B ) ) ) )).

thf('37',plain,(
    ! [X38: $i,X39: $i] :
      ( ( v1_yellow_1 @ ( k2_funcop_1 @ X38 @ X39 ) )
      | ~ ( l1_orders_2 @ X39 ) ) ),
    inference(cnf,[status(esa)],[fc10_yellow_1])).

thf('38',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k7_funcop_1 @ X41 @ X42 )
      = ( k2_funcop_1 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_funcop_1])).

thf('39',plain,(
    ! [X38: $i,X39: $i] :
      ( ( v1_yellow_1 @ ( k7_funcop_1 @ X38 @ X39 ) )
      | ~ ( l1_orders_2 @ X39 ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( v1_yellow_1 @ k1_xboole_0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['36','39'])).

thf('41',plain,(
    v1_yellow_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['33','40'])).

thf('42',plain,
    ( ( k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0 )
    = ( g1_orders_2 @ ( k1_zfmisc_1 @ k1_xboole_0 ) @ ( k6_relat_1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['19','24','25','31','32','41'])).

thf('43',plain,(
    ( k6_yellow_1 @ k1_xboole_0 @ sk_A_1 )
 != ( k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['6','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( ( k6_yellow_1 @ k1_xboole_0 @ sk_A_1 )
       != ( k5_yellow_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( ( k6_yellow_1 @ k1_xboole_0 @ sk_A_1 )
       != ( k6_yellow_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v1_xboole_0 @ ( k7_funcop_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['0','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k7_funcop_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('47',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['20','23'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( ( k6_yellow_1 @ k1_xboole_0 @ sk_A_1 )
       != ( k6_yellow_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(demod,[status(thm)],['45','46','47'])).

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
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.24OC1nNPQT
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:35:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.44/0.63  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.44/0.63  % Solved by: fo/fo7.sh
% 0.44/0.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.44/0.63  % done 194 iterations in 0.176s
% 0.44/0.63  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.44/0.63  % SZS output start Refutation
% 0.44/0.63  thf(g1_orders_2_type, type, g1_orders_2: $i > $i > $i).
% 0.44/0.63  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.44/0.63  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.44/0.63  thf(k6_yellow_1_type, type, k6_yellow_1: $i > $i > $i).
% 0.44/0.63  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.44/0.63  thf(sk_A_type, type, sk_A: $i).
% 0.44/0.63  thf(k2_funcop_1_type, type, k2_funcop_1: $i > $i > $i).
% 0.44/0.63  thf(v1_yellow_1_type, type, v1_yellow_1: $i > $o).
% 0.44/0.63  thf(k5_yellow_1_type, type, k5_yellow_1: $i > $i > $i).
% 0.44/0.63  thf(v5_ordinal1_type, type, v5_ordinal1: $i > $o).
% 0.44/0.63  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.44/0.63  thf(v1_orders_2_type, type, v1_orders_2: $i > $o).
% 0.44/0.63  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.44/0.63  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.44/0.63  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.44/0.63  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.44/0.63  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.44/0.63  thf(k7_funcop_1_type, type, k7_funcop_1: $i > $i > $i).
% 0.44/0.63  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.44/0.63  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.44/0.63  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.44/0.63  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.44/0.63  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.44/0.63  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.44/0.63  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.44/0.63  thf(sk_A_1_type, type, sk_A_1: $i).
% 0.44/0.63  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.44/0.63  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.44/0.63  thf(d5_yellow_1, axiom,
% 0.44/0.63    (![A:$i,B:$i]:
% 0.44/0.63     ( ( l1_orders_2 @ B ) =>
% 0.44/0.63       ( ( k6_yellow_1 @ A @ B ) =
% 0.44/0.63         ( k5_yellow_1 @ A @ ( k7_funcop_1 @ A @ B ) ) ) ))).
% 0.44/0.63  thf('0', plain,
% 0.44/0.63      (![X36 : $i, X37 : $i]:
% 0.44/0.63         (((k6_yellow_1 @ X36 @ X37)
% 0.44/0.63            = (k5_yellow_1 @ X36 @ (k7_funcop_1 @ X36 @ X37)))
% 0.44/0.63          | ~ (l1_orders_2 @ X37))),
% 0.44/0.63      inference('cnf', [status(esa)], [d5_yellow_1])).
% 0.44/0.63  thf(l13_xboole_0, axiom,
% 0.44/0.63    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.44/0.63  thf('1', plain,
% 0.44/0.63      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.44/0.63      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.44/0.63  thf(t27_yellow_1, conjecture,
% 0.44/0.63    (![A:$i]:
% 0.44/0.63     ( ( l1_orders_2 @ A ) =>
% 0.44/0.63       ( ( k6_yellow_1 @ k1_xboole_0 @ A ) =
% 0.44/0.63         ( g1_orders_2 @
% 0.44/0.63           ( k1_tarski @ k1_xboole_0 ) @ 
% 0.44/0.63           ( k6_partfun1 @ ( k1_tarski @ k1_xboole_0 ) ) ) ) ))).
% 0.44/0.63  thf(zf_stmt_0, negated_conjecture,
% 0.44/0.63    (~( ![A:$i]:
% 0.44/0.63        ( ( l1_orders_2 @ A ) =>
% 0.44/0.63          ( ( k6_yellow_1 @ k1_xboole_0 @ A ) =
% 0.44/0.63            ( g1_orders_2 @
% 0.44/0.63              ( k1_tarski @ k1_xboole_0 ) @ 
% 0.44/0.63              ( k6_partfun1 @ ( k1_tarski @ k1_xboole_0 ) ) ) ) ) )),
% 0.44/0.63    inference('cnf.neg', [status(esa)], [t27_yellow_1])).
% 0.44/0.63  thf('2', plain,
% 0.44/0.63      (((k6_yellow_1 @ k1_xboole_0 @ sk_A_1)
% 0.44/0.63         != (g1_orders_2 @ (k1_tarski @ k1_xboole_0) @ 
% 0.44/0.63             (k6_partfun1 @ (k1_tarski @ k1_xboole_0))))),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf(t1_zfmisc_1, axiom,
% 0.44/0.63    (( k1_zfmisc_1 @ k1_xboole_0 ) = ( k1_tarski @ k1_xboole_0 ))).
% 0.44/0.63  thf('3', plain, (((k1_zfmisc_1 @ k1_xboole_0) = (k1_tarski @ k1_xboole_0))),
% 0.44/0.63      inference('cnf', [status(esa)], [t1_zfmisc_1])).
% 0.44/0.63  thf('4', plain, (((k1_zfmisc_1 @ k1_xboole_0) = (k1_tarski @ k1_xboole_0))),
% 0.44/0.63      inference('cnf', [status(esa)], [t1_zfmisc_1])).
% 0.44/0.63  thf(redefinition_k6_partfun1, axiom,
% 0.44/0.63    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.44/0.63  thf('5', plain, (![X35 : $i]: ((k6_partfun1 @ X35) = (k6_relat_1 @ X35))),
% 0.44/0.63      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.44/0.63  thf('6', plain,
% 0.44/0.63      (((k6_yellow_1 @ k1_xboole_0 @ sk_A_1)
% 0.44/0.63         != (g1_orders_2 @ (k1_zfmisc_1 @ k1_xboole_0) @ 
% 0.44/0.63             (k6_relat_1 @ (k1_zfmisc_1 @ k1_xboole_0))))),
% 0.44/0.63      inference('demod', [status(thm)], ['2', '3', '4', '5'])).
% 0.44/0.63  thf('7', plain,
% 0.44/0.63      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.44/0.63      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.44/0.63  thf(t81_relat_1, axiom, (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.44/0.63  thf('8', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.44/0.63      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.44/0.63  thf('9', plain,
% 0.44/0.63      (![X0 : $i]: (((k6_relat_1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.44/0.63      inference('sup+', [status(thm)], ['7', '8'])).
% 0.44/0.63  thf(dt_k6_partfun1, axiom,
% 0.44/0.63    (![A:$i]:
% 0.44/0.63     ( ( m1_subset_1 @
% 0.44/0.63         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 0.44/0.63       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 0.44/0.63  thf('10', plain, (![X33 : $i]: (v1_partfun1 @ (k6_partfun1 @ X33) @ X33)),
% 0.44/0.63      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.44/0.63  thf('11', plain, (![X35 : $i]: ((k6_partfun1 @ X35) = (k6_relat_1 @ X35))),
% 0.44/0.63      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.44/0.63  thf('12', plain, (![X33 : $i]: (v1_partfun1 @ (k6_relat_1 @ X33) @ X33)),
% 0.44/0.63      inference('demod', [status(thm)], ['10', '11'])).
% 0.44/0.63  thf('13', plain,
% 0.44/0.63      (![X0 : $i]: ((v1_partfun1 @ k1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X0))),
% 0.44/0.63      inference('sup+', [status(thm)], ['9', '12'])).
% 0.44/0.63  thf(t26_yellow_1, axiom,
% 0.44/0.63    (![A:$i]:
% 0.44/0.63     ( ( ( v1_relat_1 @ A ) & ( v4_relat_1 @ A @ k1_xboole_0 ) & 
% 0.44/0.63         ( v1_funct_1 @ A ) & ( v1_partfun1 @ A @ k1_xboole_0 ) & 
% 0.44/0.63         ( v1_yellow_1 @ A ) ) =>
% 0.44/0.63       ( ( k5_yellow_1 @ k1_xboole_0 @ A ) =
% 0.44/0.63         ( g1_orders_2 @
% 0.44/0.63           ( k1_tarski @ k1_xboole_0 ) @ 
% 0.44/0.63           ( k6_partfun1 @ ( k1_tarski @ k1_xboole_0 ) ) ) ) ))).
% 0.44/0.63  thf('14', plain,
% 0.44/0.63      (![X43 : $i]:
% 0.44/0.63         (((k5_yellow_1 @ k1_xboole_0 @ X43)
% 0.44/0.63            = (g1_orders_2 @ (k1_tarski @ k1_xboole_0) @ 
% 0.44/0.63               (k6_partfun1 @ (k1_tarski @ k1_xboole_0))))
% 0.44/0.63          | ~ (v1_yellow_1 @ X43)
% 0.44/0.63          | ~ (v1_partfun1 @ X43 @ k1_xboole_0)
% 0.44/0.63          | ~ (v1_funct_1 @ X43)
% 0.44/0.63          | ~ (v4_relat_1 @ X43 @ k1_xboole_0)
% 0.44/0.63          | ~ (v1_relat_1 @ X43))),
% 0.44/0.63      inference('cnf', [status(esa)], [t26_yellow_1])).
% 0.44/0.63  thf('15', plain, (((k1_zfmisc_1 @ k1_xboole_0) = (k1_tarski @ k1_xboole_0))),
% 0.44/0.63      inference('cnf', [status(esa)], [t1_zfmisc_1])).
% 0.44/0.63  thf('16', plain, (((k1_zfmisc_1 @ k1_xboole_0) = (k1_tarski @ k1_xboole_0))),
% 0.44/0.63      inference('cnf', [status(esa)], [t1_zfmisc_1])).
% 0.44/0.63  thf('17', plain, (![X35 : $i]: ((k6_partfun1 @ X35) = (k6_relat_1 @ X35))),
% 0.44/0.63      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.44/0.63  thf('18', plain,
% 0.44/0.63      (![X43 : $i]:
% 0.44/0.63         (((k5_yellow_1 @ k1_xboole_0 @ X43)
% 0.44/0.63            = (g1_orders_2 @ (k1_zfmisc_1 @ k1_xboole_0) @ 
% 0.44/0.63               (k6_relat_1 @ (k1_zfmisc_1 @ k1_xboole_0))))
% 0.44/0.63          | ~ (v1_yellow_1 @ X43)
% 0.44/0.63          | ~ (v1_partfun1 @ X43 @ k1_xboole_0)
% 0.44/0.63          | ~ (v1_funct_1 @ X43)
% 0.44/0.63          | ~ (v4_relat_1 @ X43 @ k1_xboole_0)
% 0.44/0.63          | ~ (v1_relat_1 @ X43))),
% 0.44/0.63      inference('demod', [status(thm)], ['14', '15', '16', '17'])).
% 0.44/0.63  thf('19', plain,
% 0.44/0.63      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.44/0.63        | ~ (v1_relat_1 @ k1_xboole_0)
% 0.44/0.63        | ~ (v4_relat_1 @ k1_xboole_0 @ k1_xboole_0)
% 0.44/0.63        | ~ (v1_funct_1 @ k1_xboole_0)
% 0.44/0.63        | ~ (v1_yellow_1 @ k1_xboole_0)
% 0.44/0.63        | ((k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0)
% 0.44/0.63            = (g1_orders_2 @ (k1_zfmisc_1 @ k1_xboole_0) @ 
% 0.44/0.63               (k6_relat_1 @ (k1_zfmisc_1 @ k1_xboole_0)))))),
% 0.44/0.63      inference('sup-', [status(thm)], ['13', '18'])).
% 0.44/0.63  thf(fc2_funcop_1, axiom,
% 0.44/0.63    (![A:$i]: ( v1_xboole_0 @ ( k2_funcop_1 @ k1_xboole_0 @ A ) ))).
% 0.44/0.63  thf('20', plain,
% 0.44/0.63      (![X40 : $i]: (v1_xboole_0 @ (k2_funcop_1 @ k1_xboole_0 @ X40))),
% 0.44/0.63      inference('cnf', [status(esa)], [fc2_funcop_1])).
% 0.44/0.63  thf('21', plain,
% 0.44/0.63      (![X40 : $i]: (v1_xboole_0 @ (k2_funcop_1 @ k1_xboole_0 @ X40))),
% 0.44/0.63      inference('cnf', [status(esa)], [fc2_funcop_1])).
% 0.44/0.63  thf('22', plain,
% 0.44/0.63      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.44/0.63      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.44/0.63  thf('23', plain,
% 0.44/0.63      (![X0 : $i]: ((k2_funcop_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.44/0.63      inference('sup-', [status(thm)], ['21', '22'])).
% 0.44/0.63  thf('24', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.44/0.63      inference('demod', [status(thm)], ['20', '23'])).
% 0.44/0.63  thf(t45_ordinal1, axiom,
% 0.44/0.63    (![A:$i]:
% 0.44/0.63     ( ( v5_ordinal1 @ k1_xboole_0 ) & ( v1_funct_1 @ k1_xboole_0 ) & 
% 0.44/0.63       ( v5_relat_1 @ k1_xboole_0 @ A ) & ( v1_relat_1 @ k1_xboole_0 ) ))).
% 0.44/0.63  thf('25', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.44/0.63      inference('cnf', [status(esa)], [t45_ordinal1])).
% 0.44/0.63  thf(t60_relat_1, axiom,
% 0.44/0.63    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.44/0.63     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.44/0.63  thf('26', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.44/0.63      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.44/0.63  thf(d18_relat_1, axiom,
% 0.44/0.63    (![A:$i,B:$i]:
% 0.44/0.63     ( ( v1_relat_1 @ B ) =>
% 0.44/0.63       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.44/0.63  thf('27', plain,
% 0.44/0.63      (![X30 : $i, X31 : $i]:
% 0.44/0.63         (~ (r1_tarski @ (k1_relat_1 @ X30) @ X31)
% 0.44/0.63          | (v4_relat_1 @ X30 @ X31)
% 0.44/0.63          | ~ (v1_relat_1 @ X30))),
% 0.44/0.63      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.44/0.63  thf('28', plain,
% 0.44/0.63      (![X0 : $i]:
% 0.44/0.63         (~ (r1_tarski @ k1_xboole_0 @ X0)
% 0.44/0.63          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.44/0.63          | (v4_relat_1 @ k1_xboole_0 @ X0))),
% 0.44/0.63      inference('sup-', [status(thm)], ['26', '27'])).
% 0.44/0.63  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.44/0.63  thf('29', plain, (![X1 : $i]: (r1_tarski @ k1_xboole_0 @ X1)),
% 0.44/0.63      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.44/0.63  thf('30', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.44/0.63      inference('cnf', [status(esa)], [t45_ordinal1])).
% 0.44/0.63  thf('31', plain, (![X0 : $i]: (v4_relat_1 @ k1_xboole_0 @ X0)),
% 0.44/0.63      inference('demod', [status(thm)], ['28', '29', '30'])).
% 0.44/0.63  thf('32', plain, ((v1_funct_1 @ k1_xboole_0)),
% 0.44/0.63      inference('cnf', [status(esa)], [t45_ordinal1])).
% 0.44/0.63  thf(rc4_orders_2, axiom,
% 0.44/0.63    (?[A:$i]:
% 0.44/0.63     ( ( v1_orders_2 @ A ) & ( v2_struct_0 @ A ) & ( l1_orders_2 @ A ) ))).
% 0.44/0.63  thf('33', plain, ((l1_orders_2 @ sk_A)),
% 0.44/0.63      inference('cnf', [status(esa)], [rc4_orders_2])).
% 0.44/0.63  thf('34', plain,
% 0.44/0.63      (![X0 : $i]: ((k2_funcop_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.44/0.63      inference('sup-', [status(thm)], ['21', '22'])).
% 0.44/0.63  thf(redefinition_k7_funcop_1, axiom,
% 0.44/0.63    (![A:$i,B:$i]: ( ( k7_funcop_1 @ A @ B ) = ( k2_funcop_1 @ A @ B ) ))).
% 0.44/0.63  thf('35', plain,
% 0.44/0.63      (![X41 : $i, X42 : $i]:
% 0.44/0.63         ((k7_funcop_1 @ X41 @ X42) = (k2_funcop_1 @ X41 @ X42))),
% 0.44/0.63      inference('cnf', [status(esa)], [redefinition_k7_funcop_1])).
% 0.44/0.63  thf('36', plain,
% 0.44/0.63      (![X0 : $i]: ((k7_funcop_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.44/0.63      inference('demod', [status(thm)], ['34', '35'])).
% 0.44/0.63  thf(fc10_yellow_1, axiom,
% 0.44/0.63    (![A:$i,B:$i]:
% 0.44/0.63     ( ( l1_orders_2 @ B ) => ( v1_yellow_1 @ ( k2_funcop_1 @ A @ B ) ) ))).
% 0.44/0.63  thf('37', plain,
% 0.44/0.63      (![X38 : $i, X39 : $i]:
% 0.44/0.63         ((v1_yellow_1 @ (k2_funcop_1 @ X38 @ X39)) | ~ (l1_orders_2 @ X39))),
% 0.44/0.63      inference('cnf', [status(esa)], [fc10_yellow_1])).
% 0.44/0.63  thf('38', plain,
% 0.44/0.63      (![X41 : $i, X42 : $i]:
% 0.44/0.63         ((k7_funcop_1 @ X41 @ X42) = (k2_funcop_1 @ X41 @ X42))),
% 0.44/0.63      inference('cnf', [status(esa)], [redefinition_k7_funcop_1])).
% 0.44/0.63  thf('39', plain,
% 0.44/0.63      (![X38 : $i, X39 : $i]:
% 0.44/0.63         ((v1_yellow_1 @ (k7_funcop_1 @ X38 @ X39)) | ~ (l1_orders_2 @ X39))),
% 0.44/0.63      inference('demod', [status(thm)], ['37', '38'])).
% 0.44/0.63  thf('40', plain,
% 0.44/0.63      (![X0 : $i]: ((v1_yellow_1 @ k1_xboole_0) | ~ (l1_orders_2 @ X0))),
% 0.44/0.63      inference('sup+', [status(thm)], ['36', '39'])).
% 0.44/0.63  thf('41', plain, ((v1_yellow_1 @ k1_xboole_0)),
% 0.44/0.63      inference('sup-', [status(thm)], ['33', '40'])).
% 0.44/0.63  thf('42', plain,
% 0.44/0.63      (((k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0)
% 0.44/0.63         = (g1_orders_2 @ (k1_zfmisc_1 @ k1_xboole_0) @ 
% 0.44/0.63            (k6_relat_1 @ (k1_zfmisc_1 @ k1_xboole_0))))),
% 0.44/0.63      inference('demod', [status(thm)], ['19', '24', '25', '31', '32', '41'])).
% 0.44/0.63  thf('43', plain,
% 0.44/0.63      (((k6_yellow_1 @ k1_xboole_0 @ sk_A_1)
% 0.44/0.63         != (k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0))),
% 0.44/0.63      inference('demod', [status(thm)], ['6', '42'])).
% 0.44/0.63  thf('44', plain,
% 0.44/0.63      (![X0 : $i]:
% 0.44/0.63         (((k6_yellow_1 @ k1_xboole_0 @ sk_A_1)
% 0.44/0.63            != (k5_yellow_1 @ k1_xboole_0 @ X0))
% 0.44/0.63          | ~ (v1_xboole_0 @ X0))),
% 0.44/0.63      inference('sup-', [status(thm)], ['1', '43'])).
% 0.44/0.63  thf('45', plain,
% 0.44/0.63      (![X0 : $i]:
% 0.44/0.63         (((k6_yellow_1 @ k1_xboole_0 @ sk_A_1)
% 0.44/0.63            != (k6_yellow_1 @ k1_xboole_0 @ X0))
% 0.44/0.63          | ~ (l1_orders_2 @ X0)
% 0.44/0.63          | ~ (v1_xboole_0 @ (k7_funcop_1 @ k1_xboole_0 @ X0)))),
% 0.44/0.63      inference('sup-', [status(thm)], ['0', '44'])).
% 0.44/0.63  thf('46', plain,
% 0.44/0.63      (![X0 : $i]: ((k7_funcop_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.44/0.63      inference('demod', [status(thm)], ['34', '35'])).
% 0.44/0.63  thf('47', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.44/0.63      inference('demod', [status(thm)], ['20', '23'])).
% 0.44/0.63  thf('48', plain,
% 0.44/0.63      (![X0 : $i]:
% 0.44/0.63         (((k6_yellow_1 @ k1_xboole_0 @ sk_A_1)
% 0.44/0.63            != (k6_yellow_1 @ k1_xboole_0 @ X0))
% 0.44/0.63          | ~ (l1_orders_2 @ X0))),
% 0.44/0.63      inference('demod', [status(thm)], ['45', '46', '47'])).
% 0.44/0.63  thf('49', plain, (~ (l1_orders_2 @ sk_A_1)),
% 0.44/0.63      inference('eq_res', [status(thm)], ['48'])).
% 0.44/0.63  thf('50', plain, ((l1_orders_2 @ sk_A_1)),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf('51', plain, ($false), inference('demod', [status(thm)], ['49', '50'])).
% 0.44/0.63  
% 0.44/0.63  % SZS output end Refutation
% 0.44/0.63  
% 0.44/0.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
