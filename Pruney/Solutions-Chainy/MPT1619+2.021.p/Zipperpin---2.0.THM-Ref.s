%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.SjFBZlyQhV

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:27 EST 2020

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 134 expanded)
%              Number of leaves         :   36 (  61 expanded)
%              Depth                    :   14
%              Number of atoms          :  479 ( 792 expanded)
%              Number of equality atoms :   48 (  74 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k6_yellow_1_type,type,(
    k6_yellow_1: $i > $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_funcop_1_type,type,(
    k2_funcop_1: $i > $i > $i )).

thf(g1_orders_2_type,type,(
    g1_orders_2: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k7_funcop_1_type,type,(
    k7_funcop_1: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k5_yellow_1_type,type,(
    k5_yellow_1: $i > $i > $i )).

thf(v1_yellow_1_type,type,(
    v1_yellow_1: $i > $o )).

thf(d5_yellow_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( l1_orders_2 @ B )
     => ( ( k6_yellow_1 @ A @ B )
        = ( k5_yellow_1 @ A @ ( k7_funcop_1 @ A @ B ) ) ) ) )).

thf('0',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k6_yellow_1 @ X19 @ X20 )
        = ( k5_yellow_1 @ X19 @ ( k7_funcop_1 @ X19 @ X20 ) ) )
      | ~ ( l1_orders_2 @ X20 ) ) ),
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

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('3',plain,(
    ! [X18: $i] :
      ( ( k6_partfun1 @ X18 )
      = ( k6_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('4',plain,(
    ( k6_yellow_1 @ k1_xboole_0 @ sk_A )
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

thf('7',plain,(
    ! [X0: $i] :
      ( ( ( k6_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('8',plain,(
    ! [X16: $i] :
      ( v1_partfun1 @ ( k6_partfun1 @ X16 ) @ X16 ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('9',plain,(
    ! [X18: $i] :
      ( ( k6_partfun1 @ X18 )
      = ( k6_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('10',plain,(
    ! [X16: $i] :
      ( v1_partfun1 @ ( k6_relat_1 @ X16 ) @ X16 ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( v1_partfun1 @ k1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','10'])).

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
    ! [X25: $i] :
      ( ( ( k5_yellow_1 @ k1_xboole_0 @ X25 )
        = ( g1_orders_2 @ ( k1_tarski @ k1_xboole_0 ) @ ( k6_partfun1 @ ( k1_tarski @ k1_xboole_0 ) ) ) )
      | ~ ( v1_yellow_1 @ X25 )
      | ~ ( v1_partfun1 @ X25 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v4_relat_1 @ X25 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t26_yellow_1])).

thf('13',plain,(
    ! [X18: $i] :
      ( ( k6_partfun1 @ X18 )
      = ( k6_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('14',plain,(
    ! [X25: $i] :
      ( ( ( k5_yellow_1 @ k1_xboole_0 @ X25 )
        = ( g1_orders_2 @ ( k1_tarski @ k1_xboole_0 ) @ ( k6_relat_1 @ ( k1_tarski @ k1_xboole_0 ) ) ) )
      | ~ ( v1_yellow_1 @ X25 )
      | ~ ( v1_partfun1 @ X25 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v4_relat_1 @ X25 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
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

thf(fc2_funcop_1,axiom,(
    ! [A: $i] :
      ( v1_xboole_0 @ ( k2_funcop_1 @ k1_xboole_0 @ A ) ) )).

thf('16',plain,(
    ! [X21: $i] :
      ( v1_xboole_0 @ ( k2_funcop_1 @ k1_xboole_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc2_funcop_1])).

thf('17',plain,(
    ! [X21: $i] :
      ( v1_xboole_0 @ ( k2_funcop_1 @ k1_xboole_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc2_funcop_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k2_funcop_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['16','19'])).

thf('21',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('22',plain,(
    ! [X12: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('23',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['21','22'])).

thf(rc1_yellow_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( ( v1_yellow_1 @ B )
      & ( v1_partfun1 @ B @ A )
      & ( v1_funct_1 @ B )
      & ( v4_relat_1 @ B @ A )
      & ( v1_relat_1 @ B ) ) )).

thf('24',plain,(
    ! [X22: $i] :
      ( v1_partfun1 @ ( sk_B @ X22 ) @ X22 ) ),
    inference(cnf,[status(esa)],[rc1_yellow_1])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('25',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_partfun1 @ X15 @ X14 )
      | ( ( k1_relat_1 @ X15 )
        = X14 )
      | ~ ( v4_relat_1 @ X15 @ X14 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( sk_B @ X0 ) )
      | ~ ( v4_relat_1 @ ( sk_B @ X0 ) @ X0 )
      | ( ( k1_relat_1 @ ( sk_B @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X22: $i] :
      ( v1_relat_1 @ ( sk_B @ X22 ) ) ),
    inference(cnf,[status(esa)],[rc1_yellow_1])).

thf('28',plain,(
    ! [X22: $i] :
      ( v4_relat_1 @ ( sk_B @ X22 ) @ X22 ) ),
    inference(cnf,[status(esa)],[rc1_yellow_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( sk_B @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['26','27','28'])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('30',plain,(
    ! [X11: $i] :
      ( ( ( k1_relat_1 @ X11 )
       != k1_xboole_0 )
      | ( X11 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_B @ X0 ) )
      | ( ( sk_B @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X22: $i] :
      ( v1_relat_1 @ ( sk_B @ X22 ) ) ),
    inference(cnf,[status(esa)],[rc1_yellow_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( ( sk_B @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,
    ( ( sk_B @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X22: $i] :
      ( v4_relat_1 @ ( sk_B @ X22 ) @ X22 ) ),
    inference(cnf,[status(esa)],[rc1_yellow_1])).

thf('36',plain,(
    v4_relat_1 @ k1_xboole_0 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf('38',plain,(
    ! [X13: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('39',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( sk_B @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['33'])).

thf('41',plain,(
    ! [X22: $i] :
      ( v1_yellow_1 @ ( sk_B @ X22 ) ) ),
    inference(cnf,[status(esa)],[rc1_yellow_1])).

thf('42',plain,(
    v1_yellow_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0 )
    = ( g1_orders_2 @ ( k1_tarski @ k1_xboole_0 ) @ ( k6_relat_1 @ ( k1_tarski @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['15','20','23','36','39','42'])).

thf('44',plain,(
    ( k6_yellow_1 @ k1_xboole_0 @ sk_A )
 != ( k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['4','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( ( k6_yellow_1 @ k1_xboole_0 @ sk_A )
       != ( k5_yellow_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( ( k6_yellow_1 @ k1_xboole_0 @ sk_A )
       != ( k6_yellow_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v1_xboole_0 @ ( k7_funcop_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['0','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k2_funcop_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf(redefinition_k7_funcop_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k7_funcop_1 @ A @ B )
      = ( k2_funcop_1 @ A @ B ) ) )).

thf('48',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k7_funcop_1 @ X23 @ X24 )
      = ( k2_funcop_1 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_funcop_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k7_funcop_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['16','19'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( ( k6_yellow_1 @ k1_xboole_0 @ sk_A )
       != ( k6_yellow_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(demod,[status(thm)],['46','49','50'])).

thf('52',plain,(
    ~ ( l1_orders_2 @ sk_A ) ),
    inference(eq_res,[status(thm)],['51'])).

thf('53',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    $false ),
    inference(demod,[status(thm)],['52','53'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.SjFBZlyQhV
% 0.13/0.35  % Computer   : n005.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:07:48 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.47/0.66  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.47/0.66  % Solved by: fo/fo7.sh
% 0.47/0.66  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.47/0.66  % done 209 iterations in 0.194s
% 0.47/0.66  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.47/0.66  % SZS output start Refutation
% 0.47/0.66  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.47/0.66  thf(sk_B_type, type, sk_B: $i > $i).
% 0.47/0.66  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.47/0.66  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.47/0.66  thf(k6_yellow_1_type, type, k6_yellow_1: $i > $i > $i).
% 0.47/0.66  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.47/0.66  thf(sk_A_type, type, sk_A: $i).
% 0.47/0.66  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.47/0.66  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.47/0.66  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.47/0.66  thf(k2_funcop_1_type, type, k2_funcop_1: $i > $i > $i).
% 0.47/0.66  thf(g1_orders_2_type, type, g1_orders_2: $i > $i > $i).
% 0.47/0.66  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.47/0.66  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.47/0.66  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.47/0.66  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.47/0.66  thf(k7_funcop_1_type, type, k7_funcop_1: $i > $i > $i).
% 0.47/0.66  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.47/0.66  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.47/0.66  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.47/0.66  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.47/0.66  thf(k5_yellow_1_type, type, k5_yellow_1: $i > $i > $i).
% 0.47/0.66  thf(v1_yellow_1_type, type, v1_yellow_1: $i > $o).
% 0.47/0.66  thf(d5_yellow_1, axiom,
% 0.47/0.66    (![A:$i,B:$i]:
% 0.47/0.66     ( ( l1_orders_2 @ B ) =>
% 0.47/0.66       ( ( k6_yellow_1 @ A @ B ) =
% 0.47/0.66         ( k5_yellow_1 @ A @ ( k7_funcop_1 @ A @ B ) ) ) ))).
% 0.47/0.66  thf('0', plain,
% 0.47/0.66      (![X19 : $i, X20 : $i]:
% 0.47/0.66         (((k6_yellow_1 @ X19 @ X20)
% 0.47/0.66            = (k5_yellow_1 @ X19 @ (k7_funcop_1 @ X19 @ X20)))
% 0.47/0.66          | ~ (l1_orders_2 @ X20))),
% 0.47/0.66      inference('cnf', [status(esa)], [d5_yellow_1])).
% 0.47/0.66  thf(l13_xboole_0, axiom,
% 0.47/0.66    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.47/0.66  thf('1', plain,
% 0.47/0.66      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.47/0.66      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.47/0.66  thf(t27_yellow_1, conjecture,
% 0.47/0.66    (![A:$i]:
% 0.47/0.66     ( ( l1_orders_2 @ A ) =>
% 0.47/0.66       ( ( k6_yellow_1 @ k1_xboole_0 @ A ) =
% 0.47/0.66         ( g1_orders_2 @
% 0.47/0.66           ( k1_tarski @ k1_xboole_0 ) @ 
% 0.47/0.66           ( k6_partfun1 @ ( k1_tarski @ k1_xboole_0 ) ) ) ) ))).
% 0.47/0.66  thf(zf_stmt_0, negated_conjecture,
% 0.47/0.66    (~( ![A:$i]:
% 0.47/0.66        ( ( l1_orders_2 @ A ) =>
% 0.47/0.66          ( ( k6_yellow_1 @ k1_xboole_0 @ A ) =
% 0.47/0.66            ( g1_orders_2 @
% 0.47/0.66              ( k1_tarski @ k1_xboole_0 ) @ 
% 0.47/0.66              ( k6_partfun1 @ ( k1_tarski @ k1_xboole_0 ) ) ) ) ) )),
% 0.47/0.66    inference('cnf.neg', [status(esa)], [t27_yellow_1])).
% 0.47/0.66  thf('2', plain,
% 0.47/0.66      (((k6_yellow_1 @ k1_xboole_0 @ sk_A)
% 0.47/0.66         != (g1_orders_2 @ (k1_tarski @ k1_xboole_0) @ 
% 0.47/0.66             (k6_partfun1 @ (k1_tarski @ k1_xboole_0))))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf(redefinition_k6_partfun1, axiom,
% 0.47/0.66    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.47/0.66  thf('3', plain, (![X18 : $i]: ((k6_partfun1 @ X18) = (k6_relat_1 @ X18))),
% 0.47/0.66      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.47/0.66  thf('4', plain,
% 0.47/0.66      (((k6_yellow_1 @ k1_xboole_0 @ sk_A)
% 0.47/0.66         != (g1_orders_2 @ (k1_tarski @ k1_xboole_0) @ 
% 0.47/0.66             (k6_relat_1 @ (k1_tarski @ k1_xboole_0))))),
% 0.47/0.66      inference('demod', [status(thm)], ['2', '3'])).
% 0.47/0.66  thf('5', plain,
% 0.47/0.66      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.47/0.66      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.47/0.66  thf(t81_relat_1, axiom, (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.47/0.66  thf('6', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.47/0.66      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.47/0.66  thf('7', plain,
% 0.47/0.66      (![X0 : $i]: (((k6_relat_1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.47/0.66      inference('sup+', [status(thm)], ['5', '6'])).
% 0.47/0.66  thf(dt_k6_partfun1, axiom,
% 0.47/0.66    (![A:$i]:
% 0.47/0.66     ( ( m1_subset_1 @
% 0.47/0.66         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 0.47/0.66       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 0.47/0.66  thf('8', plain, (![X16 : $i]: (v1_partfun1 @ (k6_partfun1 @ X16) @ X16)),
% 0.47/0.66      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.47/0.66  thf('9', plain, (![X18 : $i]: ((k6_partfun1 @ X18) = (k6_relat_1 @ X18))),
% 0.47/0.66      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.47/0.66  thf('10', plain, (![X16 : $i]: (v1_partfun1 @ (k6_relat_1 @ X16) @ X16)),
% 0.47/0.66      inference('demod', [status(thm)], ['8', '9'])).
% 0.47/0.66  thf('11', plain,
% 0.47/0.66      (![X0 : $i]: ((v1_partfun1 @ k1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X0))),
% 0.47/0.66      inference('sup+', [status(thm)], ['7', '10'])).
% 0.47/0.66  thf(t26_yellow_1, axiom,
% 0.47/0.66    (![A:$i]:
% 0.47/0.66     ( ( ( v1_relat_1 @ A ) & ( v4_relat_1 @ A @ k1_xboole_0 ) & 
% 0.47/0.66         ( v1_funct_1 @ A ) & ( v1_partfun1 @ A @ k1_xboole_0 ) & 
% 0.47/0.66         ( v1_yellow_1 @ A ) ) =>
% 0.47/0.66       ( ( k5_yellow_1 @ k1_xboole_0 @ A ) =
% 0.47/0.66         ( g1_orders_2 @
% 0.47/0.66           ( k1_tarski @ k1_xboole_0 ) @ 
% 0.47/0.66           ( k6_partfun1 @ ( k1_tarski @ k1_xboole_0 ) ) ) ) ))).
% 0.47/0.66  thf('12', plain,
% 0.47/0.66      (![X25 : $i]:
% 0.47/0.66         (((k5_yellow_1 @ k1_xboole_0 @ X25)
% 0.47/0.66            = (g1_orders_2 @ (k1_tarski @ k1_xboole_0) @ 
% 0.47/0.66               (k6_partfun1 @ (k1_tarski @ k1_xboole_0))))
% 0.47/0.66          | ~ (v1_yellow_1 @ X25)
% 0.47/0.66          | ~ (v1_partfun1 @ X25 @ k1_xboole_0)
% 0.47/0.66          | ~ (v1_funct_1 @ X25)
% 0.47/0.66          | ~ (v4_relat_1 @ X25 @ k1_xboole_0)
% 0.47/0.66          | ~ (v1_relat_1 @ X25))),
% 0.47/0.66      inference('cnf', [status(esa)], [t26_yellow_1])).
% 0.47/0.66  thf('13', plain, (![X18 : $i]: ((k6_partfun1 @ X18) = (k6_relat_1 @ X18))),
% 0.47/0.66      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.47/0.66  thf('14', plain,
% 0.47/0.66      (![X25 : $i]:
% 0.47/0.66         (((k5_yellow_1 @ k1_xboole_0 @ X25)
% 0.47/0.66            = (g1_orders_2 @ (k1_tarski @ k1_xboole_0) @ 
% 0.47/0.66               (k6_relat_1 @ (k1_tarski @ k1_xboole_0))))
% 0.47/0.66          | ~ (v1_yellow_1 @ X25)
% 0.47/0.66          | ~ (v1_partfun1 @ X25 @ k1_xboole_0)
% 0.47/0.66          | ~ (v1_funct_1 @ X25)
% 0.47/0.66          | ~ (v4_relat_1 @ X25 @ k1_xboole_0)
% 0.47/0.66          | ~ (v1_relat_1 @ X25))),
% 0.47/0.66      inference('demod', [status(thm)], ['12', '13'])).
% 0.47/0.66  thf('15', plain,
% 0.47/0.66      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.47/0.66        | ~ (v1_relat_1 @ k1_xboole_0)
% 0.47/0.66        | ~ (v4_relat_1 @ k1_xboole_0 @ k1_xboole_0)
% 0.47/0.66        | ~ (v1_funct_1 @ k1_xboole_0)
% 0.47/0.66        | ~ (v1_yellow_1 @ k1_xboole_0)
% 0.47/0.66        | ((k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0)
% 0.47/0.66            = (g1_orders_2 @ (k1_tarski @ k1_xboole_0) @ 
% 0.47/0.66               (k6_relat_1 @ (k1_tarski @ k1_xboole_0)))))),
% 0.47/0.66      inference('sup-', [status(thm)], ['11', '14'])).
% 0.47/0.66  thf(fc2_funcop_1, axiom,
% 0.47/0.66    (![A:$i]: ( v1_xboole_0 @ ( k2_funcop_1 @ k1_xboole_0 @ A ) ))).
% 0.47/0.66  thf('16', plain,
% 0.47/0.66      (![X21 : $i]: (v1_xboole_0 @ (k2_funcop_1 @ k1_xboole_0 @ X21))),
% 0.47/0.66      inference('cnf', [status(esa)], [fc2_funcop_1])).
% 0.47/0.66  thf('17', plain,
% 0.47/0.66      (![X21 : $i]: (v1_xboole_0 @ (k2_funcop_1 @ k1_xboole_0 @ X21))),
% 0.47/0.66      inference('cnf', [status(esa)], [fc2_funcop_1])).
% 0.47/0.66  thf('18', plain,
% 0.47/0.66      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.47/0.66      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.47/0.66  thf('19', plain,
% 0.47/0.66      (![X0 : $i]: ((k2_funcop_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.47/0.66      inference('sup-', [status(thm)], ['17', '18'])).
% 0.47/0.66  thf('20', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.47/0.66      inference('demod', [status(thm)], ['16', '19'])).
% 0.47/0.66  thf('21', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.47/0.66      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.47/0.66  thf(fc3_funct_1, axiom,
% 0.47/0.66    (![A:$i]:
% 0.47/0.66     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.47/0.66       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.47/0.66  thf('22', plain, (![X12 : $i]: (v1_relat_1 @ (k6_relat_1 @ X12))),
% 0.47/0.66      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.47/0.66  thf('23', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.47/0.66      inference('sup+', [status(thm)], ['21', '22'])).
% 0.47/0.66  thf(rc1_yellow_1, axiom,
% 0.47/0.66    (![A:$i]:
% 0.47/0.66     ( ?[B:$i]:
% 0.47/0.66       ( ( v1_yellow_1 @ B ) & ( v1_partfun1 @ B @ A ) & ( v1_funct_1 @ B ) & 
% 0.47/0.66         ( v4_relat_1 @ B @ A ) & ( v1_relat_1 @ B ) ) ))).
% 0.47/0.66  thf('24', plain, (![X22 : $i]: (v1_partfun1 @ (sk_B @ X22) @ X22)),
% 0.47/0.66      inference('cnf', [status(esa)], [rc1_yellow_1])).
% 0.47/0.66  thf(d4_partfun1, axiom,
% 0.47/0.66    (![A:$i,B:$i]:
% 0.47/0.66     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.47/0.66       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 0.47/0.66  thf('25', plain,
% 0.47/0.66      (![X14 : $i, X15 : $i]:
% 0.47/0.66         (~ (v1_partfun1 @ X15 @ X14)
% 0.47/0.66          | ((k1_relat_1 @ X15) = (X14))
% 0.47/0.66          | ~ (v4_relat_1 @ X15 @ X14)
% 0.47/0.66          | ~ (v1_relat_1 @ X15))),
% 0.47/0.66      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.47/0.66  thf('26', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         (~ (v1_relat_1 @ (sk_B @ X0))
% 0.47/0.66          | ~ (v4_relat_1 @ (sk_B @ X0) @ X0)
% 0.47/0.66          | ((k1_relat_1 @ (sk_B @ X0)) = (X0)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['24', '25'])).
% 0.47/0.66  thf('27', plain, (![X22 : $i]: (v1_relat_1 @ (sk_B @ X22))),
% 0.47/0.66      inference('cnf', [status(esa)], [rc1_yellow_1])).
% 0.47/0.66  thf('28', plain, (![X22 : $i]: (v4_relat_1 @ (sk_B @ X22) @ X22)),
% 0.47/0.66      inference('cnf', [status(esa)], [rc1_yellow_1])).
% 0.47/0.66  thf('29', plain, (![X0 : $i]: ((k1_relat_1 @ (sk_B @ X0)) = (X0))),
% 0.47/0.66      inference('demod', [status(thm)], ['26', '27', '28'])).
% 0.47/0.66  thf(t64_relat_1, axiom,
% 0.47/0.66    (![A:$i]:
% 0.47/0.66     ( ( v1_relat_1 @ A ) =>
% 0.47/0.66       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.47/0.66           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.47/0.66         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.47/0.66  thf('30', plain,
% 0.47/0.66      (![X11 : $i]:
% 0.47/0.66         (((k1_relat_1 @ X11) != (k1_xboole_0))
% 0.47/0.66          | ((X11) = (k1_xboole_0))
% 0.47/0.66          | ~ (v1_relat_1 @ X11))),
% 0.47/0.66      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.47/0.66  thf('31', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         (((X0) != (k1_xboole_0))
% 0.47/0.66          | ~ (v1_relat_1 @ (sk_B @ X0))
% 0.47/0.66          | ((sk_B @ X0) = (k1_xboole_0)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['29', '30'])).
% 0.47/0.66  thf('32', plain, (![X22 : $i]: (v1_relat_1 @ (sk_B @ X22))),
% 0.47/0.66      inference('cnf', [status(esa)], [rc1_yellow_1])).
% 0.47/0.66  thf('33', plain,
% 0.47/0.66      (![X0 : $i]: (((X0) != (k1_xboole_0)) | ((sk_B @ X0) = (k1_xboole_0)))),
% 0.47/0.66      inference('demod', [status(thm)], ['31', '32'])).
% 0.47/0.66  thf('34', plain, (((sk_B @ k1_xboole_0) = (k1_xboole_0))),
% 0.47/0.66      inference('simplify', [status(thm)], ['33'])).
% 0.47/0.66  thf('35', plain, (![X22 : $i]: (v4_relat_1 @ (sk_B @ X22) @ X22)),
% 0.47/0.66      inference('cnf', [status(esa)], [rc1_yellow_1])).
% 0.47/0.66  thf('36', plain, ((v4_relat_1 @ k1_xboole_0 @ k1_xboole_0)),
% 0.47/0.66      inference('sup+', [status(thm)], ['34', '35'])).
% 0.47/0.66  thf('37', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.47/0.66      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.47/0.66  thf('38', plain, (![X13 : $i]: (v1_funct_1 @ (k6_relat_1 @ X13))),
% 0.47/0.66      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.47/0.66  thf('39', plain, ((v1_funct_1 @ k1_xboole_0)),
% 0.47/0.66      inference('sup+', [status(thm)], ['37', '38'])).
% 0.47/0.66  thf('40', plain, (((sk_B @ k1_xboole_0) = (k1_xboole_0))),
% 0.47/0.66      inference('simplify', [status(thm)], ['33'])).
% 0.47/0.66  thf('41', plain, (![X22 : $i]: (v1_yellow_1 @ (sk_B @ X22))),
% 0.47/0.66      inference('cnf', [status(esa)], [rc1_yellow_1])).
% 0.47/0.66  thf('42', plain, ((v1_yellow_1 @ k1_xboole_0)),
% 0.47/0.66      inference('sup+', [status(thm)], ['40', '41'])).
% 0.47/0.66  thf('43', plain,
% 0.47/0.66      (((k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0)
% 0.47/0.66         = (g1_orders_2 @ (k1_tarski @ k1_xboole_0) @ 
% 0.47/0.66            (k6_relat_1 @ (k1_tarski @ k1_xboole_0))))),
% 0.47/0.66      inference('demod', [status(thm)], ['15', '20', '23', '36', '39', '42'])).
% 0.47/0.66  thf('44', plain,
% 0.47/0.66      (((k6_yellow_1 @ k1_xboole_0 @ sk_A)
% 0.47/0.66         != (k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0))),
% 0.47/0.66      inference('demod', [status(thm)], ['4', '43'])).
% 0.47/0.66  thf('45', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         (((k6_yellow_1 @ k1_xboole_0 @ sk_A)
% 0.47/0.66            != (k5_yellow_1 @ k1_xboole_0 @ X0))
% 0.47/0.66          | ~ (v1_xboole_0 @ X0))),
% 0.47/0.66      inference('sup-', [status(thm)], ['1', '44'])).
% 0.47/0.66  thf('46', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         (((k6_yellow_1 @ k1_xboole_0 @ sk_A)
% 0.47/0.66            != (k6_yellow_1 @ k1_xboole_0 @ X0))
% 0.47/0.66          | ~ (l1_orders_2 @ X0)
% 0.47/0.66          | ~ (v1_xboole_0 @ (k7_funcop_1 @ k1_xboole_0 @ X0)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['0', '45'])).
% 0.47/0.66  thf('47', plain,
% 0.47/0.66      (![X0 : $i]: ((k2_funcop_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.47/0.66      inference('sup-', [status(thm)], ['17', '18'])).
% 0.47/0.66  thf(redefinition_k7_funcop_1, axiom,
% 0.47/0.66    (![A:$i,B:$i]: ( ( k7_funcop_1 @ A @ B ) = ( k2_funcop_1 @ A @ B ) ))).
% 0.47/0.66  thf('48', plain,
% 0.47/0.66      (![X23 : $i, X24 : $i]:
% 0.47/0.66         ((k7_funcop_1 @ X23 @ X24) = (k2_funcop_1 @ X23 @ X24))),
% 0.47/0.66      inference('cnf', [status(esa)], [redefinition_k7_funcop_1])).
% 0.47/0.66  thf('49', plain,
% 0.47/0.66      (![X0 : $i]: ((k7_funcop_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.47/0.66      inference('demod', [status(thm)], ['47', '48'])).
% 0.47/0.66  thf('50', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.47/0.66      inference('demod', [status(thm)], ['16', '19'])).
% 0.47/0.66  thf('51', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         (((k6_yellow_1 @ k1_xboole_0 @ sk_A)
% 0.47/0.66            != (k6_yellow_1 @ k1_xboole_0 @ X0))
% 0.47/0.66          | ~ (l1_orders_2 @ X0))),
% 0.47/0.66      inference('demod', [status(thm)], ['46', '49', '50'])).
% 0.47/0.66  thf('52', plain, (~ (l1_orders_2 @ sk_A)),
% 0.47/0.66      inference('eq_res', [status(thm)], ['51'])).
% 0.47/0.66  thf('53', plain, ((l1_orders_2 @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('54', plain, ($false), inference('demod', [status(thm)], ['52', '53'])).
% 0.47/0.66  
% 0.47/0.66  % SZS output end Refutation
% 0.47/0.66  
% 0.47/0.67  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
