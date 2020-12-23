%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.vTe0UpvT3L

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:26 EST 2020

% Result     : Theorem 1.16s
% Output     : Refutation 1.16s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 141 expanded)
%              Number of leaves         :   39 (  64 expanded)
%              Depth                    :   12
%              Number of atoms          :  488 ( 837 expanded)
%              Number of equality atoms :   46 (  74 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k7_funcop_1_type,type,(
    k7_funcop_1: $i > $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k5_yellow_1_type,type,(
    k5_yellow_1: $i > $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k6_yellow_1_type,type,(
    k6_yellow_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(v1_yellow_1_type,type,(
    v1_yellow_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(g1_orders_2_type,type,(
    g1_orders_2: $i > $i > $i )).

thf(k2_funcop_1_type,type,(
    k2_funcop_1: $i > $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(fc2_funcop_1,axiom,(
    ! [A: $i] :
      ( v1_xboole_0 @ ( k2_funcop_1 @ k1_xboole_0 @ A ) ) )).

thf('0',plain,(
    ! [X35: $i] :
      ( v1_xboole_0 @ ( k2_funcop_1 @ k1_xboole_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[fc2_funcop_1])).

thf(redefinition_k7_funcop_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k7_funcop_1 @ A @ B )
      = ( k2_funcop_1 @ A @ B ) ) )).

thf('1',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k7_funcop_1 @ X37 @ X38 )
      = ( k2_funcop_1 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_funcop_1])).

thf('2',plain,(
    ! [X35: $i] :
      ( v1_xboole_0 @ ( k7_funcop_1 @ k1_xboole_0 @ X35 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('3',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k7_funcop_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf(d5_yellow_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( l1_orders_2 @ B )
     => ( ( k6_yellow_1 @ A @ B )
        = ( k5_yellow_1 @ A @ ( k7_funcop_1 @ A @ B ) ) ) ) )).

thf('7',plain,(
    ! [X33: $i,X34: $i] :
      ( ( ( k6_yellow_1 @ X33 @ X34 )
        = ( k5_yellow_1 @ X33 @ ( k7_funcop_1 @ X33 @ X34 ) ) )
      | ~ ( l1_orders_2 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d5_yellow_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( ( k6_yellow_1 @ k1_xboole_0 @ X0 )
        = ( k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

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

thf('9',plain,(
    ( k6_yellow_1 @ k1_xboole_0 @ sk_A )
 != ( g1_orders_2 @ ( k1_tarski @ k1_xboole_0 ) @ ( k6_partfun1 @ ( k1_tarski @ k1_xboole_0 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('10',plain,(
    ! [X32: $i] :
      ( ( k6_partfun1 @ X32 )
      = ( k6_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('11',plain,(
    ( k6_yellow_1 @ k1_xboole_0 @ sk_A )
 != ( g1_orders_2 @ ( k1_tarski @ k1_xboole_0 ) @ ( k6_relat_1 @ ( k1_tarski @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t81_relat_1,axiom,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('13',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('14',plain,(
    ! [X30: $i] :
      ( v1_partfun1 @ ( k6_partfun1 @ X30 ) @ X30 ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('15',plain,(
    ! [X32: $i] :
      ( ( k6_partfun1 @ X32 )
      = ( k6_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('16',plain,(
    ! [X30: $i] :
      ( v1_partfun1 @ ( k6_relat_1 @ X30 ) @ X30 ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    v1_partfun1 @ k1_xboole_0 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( v1_partfun1 @ k1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','17'])).

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
    ! [X39: $i] :
      ( ( ( k5_yellow_1 @ k1_xboole_0 @ X39 )
        = ( g1_orders_2 @ ( k1_tarski @ k1_xboole_0 ) @ ( k6_partfun1 @ ( k1_tarski @ k1_xboole_0 ) ) ) )
      | ~ ( v1_yellow_1 @ X39 )
      | ~ ( v1_partfun1 @ X39 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( v4_relat_1 @ X39 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t26_yellow_1])).

thf('20',plain,(
    ! [X32: $i] :
      ( ( k6_partfun1 @ X32 )
      = ( k6_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('21',plain,(
    ! [X39: $i] :
      ( ( ( k5_yellow_1 @ k1_xboole_0 @ X39 )
        = ( g1_orders_2 @ ( k1_tarski @ k1_xboole_0 ) @ ( k6_relat_1 @ ( k1_tarski @ k1_xboole_0 ) ) ) )
      | ~ ( v1_yellow_1 @ X39 )
      | ~ ( v1_partfun1 @ X39 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( v4_relat_1 @ X39 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 )
    | ~ ( v4_relat_1 @ k1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_funct_1 @ k1_xboole_0 )
    | ~ ( v1_yellow_1 @ k1_xboole_0 )
    | ( ( k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0 )
      = ( g1_orders_2 @ ( k1_tarski @ k1_xboole_0 ) @ ( k6_relat_1 @ ( k1_tarski @ k1_xboole_0 ) ) ) ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X35: $i] :
      ( v1_xboole_0 @ ( k7_funcop_1 @ k1_xboole_0 @ X35 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k7_funcop_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf('25',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('27',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('28',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf('30',plain,(
    ! [X27: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('31',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,
    ( ~ ( v4_relat_1 @ k1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_yellow_1 @ k1_xboole_0 )
    | ( ( k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0 )
      = ( g1_orders_2 @ ( k1_tarski @ k1_xboole_0 ) @ ( k6_relat_1 @ ( k1_tarski @ k1_xboole_0 ) ) ) ) ),
    inference(demod,[status(thm)],['22','25','28','31'])).

thf(rc1_yellow_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( ( v1_yellow_1 @ B )
      & ( v1_partfun1 @ B @ A )
      & ( v1_funct_1 @ B )
      & ( v4_relat_1 @ B @ A )
      & ( v1_relat_1 @ B ) ) )).

thf('33',plain,(
    ! [X36: $i] :
      ( v1_partfun1 @ ( sk_B_2 @ X36 ) @ X36 ) ),
    inference(cnf,[status(esa)],[rc1_yellow_1])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('34',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( v1_partfun1 @ X29 @ X28 )
      | ( ( k1_relat_1 @ X29 )
        = X28 )
      | ~ ( v4_relat_1 @ X29 @ X28 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( sk_B_2 @ X0 ) )
      | ~ ( v4_relat_1 @ ( sk_B_2 @ X0 ) @ X0 )
      | ( ( k1_relat_1 @ ( sk_B_2 @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X36: $i] :
      ( v1_relat_1 @ ( sk_B_2 @ X36 ) ) ),
    inference(cnf,[status(esa)],[rc1_yellow_1])).

thf('37',plain,(
    ! [X36: $i] :
      ( v4_relat_1 @ ( sk_B_2 @ X36 ) @ X36 ) ),
    inference(cnf,[status(esa)],[rc1_yellow_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( sk_B_2 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('39',plain,(
    ! [X25: $i] :
      ( ( ( k1_relat_1 @ X25 )
       != k1_xboole_0 )
      | ( X25 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_B_2 @ X0 ) )
      | ( ( sk_B_2 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X36: $i] :
      ( v1_relat_1 @ ( sk_B_2 @ X36 ) ) ),
    inference(cnf,[status(esa)],[rc1_yellow_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( ( sk_B_2 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,
    ( ( sk_B_2 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X36: $i] :
      ( v4_relat_1 @ ( sk_B_2 @ X36 ) @ X36 ) ),
    inference(cnf,[status(esa)],[rc1_yellow_1])).

thf('45',plain,(
    v4_relat_1 @ k1_xboole_0 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( sk_B_2 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['42'])).

thf('47',plain,(
    ! [X36: $i] :
      ( v1_yellow_1 @ ( sk_B_2 @ X36 ) ) ),
    inference(cnf,[status(esa)],[rc1_yellow_1])).

thf('48',plain,(
    v1_yellow_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0 )
    = ( g1_orders_2 @ ( k1_tarski @ k1_xboole_0 ) @ ( k6_relat_1 @ ( k1_tarski @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['32','45','48'])).

thf('50',plain,(
    ( k6_yellow_1 @ k1_xboole_0 @ sk_A )
 != ( k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['11','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( ( k6_yellow_1 @ k1_xboole_0 @ sk_A )
       != ( k6_yellow_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','50'])).

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
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.vTe0UpvT3L
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:13:10 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.16/1.37  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.16/1.37  % Solved by: fo/fo7.sh
% 1.16/1.37  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.16/1.37  % done 1407 iterations in 0.940s
% 1.16/1.37  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.16/1.37  % SZS output start Refutation
% 1.16/1.37  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.16/1.37  thf(k7_funcop_1_type, type, k7_funcop_1: $i > $i > $i).
% 1.16/1.37  thf(sk_B_2_type, type, sk_B_2: $i > $i).
% 1.16/1.37  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.16/1.37  thf(k5_yellow_1_type, type, k5_yellow_1: $i > $i > $i).
% 1.16/1.37  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 1.16/1.37  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.16/1.37  thf(k6_yellow_1_type, type, k6_yellow_1: $i > $i > $i).
% 1.16/1.37  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.16/1.37  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.16/1.37  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 1.16/1.37  thf(v1_yellow_1_type, type, v1_yellow_1: $i > $o).
% 1.16/1.37  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.16/1.37  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.16/1.37  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.16/1.37  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.16/1.37  thf(sk_A_type, type, sk_A: $i).
% 1.16/1.37  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 1.16/1.37  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.16/1.37  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 1.16/1.37  thf(g1_orders_2_type, type, g1_orders_2: $i > $i > $i).
% 1.16/1.37  thf(k2_funcop_1_type, type, k2_funcop_1: $i > $i > $i).
% 1.16/1.37  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 1.16/1.37  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.16/1.37  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.16/1.37  thf(fc2_funcop_1, axiom,
% 1.16/1.37    (![A:$i]: ( v1_xboole_0 @ ( k2_funcop_1 @ k1_xboole_0 @ A ) ))).
% 1.16/1.37  thf('0', plain,
% 1.16/1.37      (![X35 : $i]: (v1_xboole_0 @ (k2_funcop_1 @ k1_xboole_0 @ X35))),
% 1.16/1.37      inference('cnf', [status(esa)], [fc2_funcop_1])).
% 1.16/1.37  thf(redefinition_k7_funcop_1, axiom,
% 1.16/1.37    (![A:$i,B:$i]: ( ( k7_funcop_1 @ A @ B ) = ( k2_funcop_1 @ A @ B ) ))).
% 1.16/1.37  thf('1', plain,
% 1.16/1.37      (![X37 : $i, X38 : $i]:
% 1.16/1.37         ((k7_funcop_1 @ X37 @ X38) = (k2_funcop_1 @ X37 @ X38))),
% 1.16/1.37      inference('cnf', [status(esa)], [redefinition_k7_funcop_1])).
% 1.16/1.37  thf('2', plain,
% 1.16/1.37      (![X35 : $i]: (v1_xboole_0 @ (k7_funcop_1 @ k1_xboole_0 @ X35))),
% 1.16/1.37      inference('demod', [status(thm)], ['0', '1'])).
% 1.16/1.37  thf(t7_xboole_0, axiom,
% 1.16/1.37    (![A:$i]:
% 1.16/1.37     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 1.16/1.37          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 1.16/1.37  thf('3', plain,
% 1.16/1.37      (![X3 : $i]: (((X3) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X3) @ X3))),
% 1.16/1.37      inference('cnf', [status(esa)], [t7_xboole_0])).
% 1.16/1.37  thf(d1_xboole_0, axiom,
% 1.16/1.37    (![A:$i]:
% 1.16/1.37     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 1.16/1.37  thf('4', plain,
% 1.16/1.37      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 1.16/1.37      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.16/1.37  thf('5', plain,
% 1.16/1.37      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.16/1.37      inference('sup-', [status(thm)], ['3', '4'])).
% 1.16/1.37  thf('6', plain,
% 1.16/1.37      (![X0 : $i]: ((k7_funcop_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 1.16/1.37      inference('sup-', [status(thm)], ['2', '5'])).
% 1.16/1.37  thf(d5_yellow_1, axiom,
% 1.16/1.37    (![A:$i,B:$i]:
% 1.16/1.37     ( ( l1_orders_2 @ B ) =>
% 1.16/1.37       ( ( k6_yellow_1 @ A @ B ) =
% 1.16/1.37         ( k5_yellow_1 @ A @ ( k7_funcop_1 @ A @ B ) ) ) ))).
% 1.16/1.37  thf('7', plain,
% 1.16/1.37      (![X33 : $i, X34 : $i]:
% 1.16/1.37         (((k6_yellow_1 @ X33 @ X34)
% 1.16/1.37            = (k5_yellow_1 @ X33 @ (k7_funcop_1 @ X33 @ X34)))
% 1.16/1.37          | ~ (l1_orders_2 @ X34))),
% 1.16/1.37      inference('cnf', [status(esa)], [d5_yellow_1])).
% 1.16/1.37  thf('8', plain,
% 1.16/1.37      (![X0 : $i]:
% 1.16/1.37         (((k6_yellow_1 @ k1_xboole_0 @ X0)
% 1.16/1.37            = (k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0))
% 1.16/1.37          | ~ (l1_orders_2 @ X0))),
% 1.16/1.37      inference('sup+', [status(thm)], ['6', '7'])).
% 1.16/1.37  thf(t27_yellow_1, conjecture,
% 1.16/1.37    (![A:$i]:
% 1.16/1.37     ( ( l1_orders_2 @ A ) =>
% 1.16/1.37       ( ( k6_yellow_1 @ k1_xboole_0 @ A ) =
% 1.16/1.37         ( g1_orders_2 @
% 1.16/1.37           ( k1_tarski @ k1_xboole_0 ) @ 
% 1.16/1.37           ( k6_partfun1 @ ( k1_tarski @ k1_xboole_0 ) ) ) ) ))).
% 1.16/1.37  thf(zf_stmt_0, negated_conjecture,
% 1.16/1.37    (~( ![A:$i]:
% 1.16/1.37        ( ( l1_orders_2 @ A ) =>
% 1.16/1.37          ( ( k6_yellow_1 @ k1_xboole_0 @ A ) =
% 1.16/1.37            ( g1_orders_2 @
% 1.16/1.37              ( k1_tarski @ k1_xboole_0 ) @ 
% 1.16/1.37              ( k6_partfun1 @ ( k1_tarski @ k1_xboole_0 ) ) ) ) ) )),
% 1.16/1.37    inference('cnf.neg', [status(esa)], [t27_yellow_1])).
% 1.16/1.37  thf('9', plain,
% 1.16/1.37      (((k6_yellow_1 @ k1_xboole_0 @ sk_A)
% 1.16/1.37         != (g1_orders_2 @ (k1_tarski @ k1_xboole_0) @ 
% 1.16/1.37             (k6_partfun1 @ (k1_tarski @ k1_xboole_0))))),
% 1.16/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.16/1.37  thf(redefinition_k6_partfun1, axiom,
% 1.16/1.37    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 1.16/1.37  thf('10', plain, (![X32 : $i]: ((k6_partfun1 @ X32) = (k6_relat_1 @ X32))),
% 1.16/1.37      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.16/1.37  thf('11', plain,
% 1.16/1.37      (((k6_yellow_1 @ k1_xboole_0 @ sk_A)
% 1.16/1.37         != (g1_orders_2 @ (k1_tarski @ k1_xboole_0) @ 
% 1.16/1.37             (k6_relat_1 @ (k1_tarski @ k1_xboole_0))))),
% 1.16/1.37      inference('demod', [status(thm)], ['9', '10'])).
% 1.16/1.37  thf('12', plain,
% 1.16/1.37      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.16/1.37      inference('sup-', [status(thm)], ['3', '4'])).
% 1.16/1.37  thf(t81_relat_1, axiom, (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 1.16/1.37  thf('13', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.16/1.37      inference('cnf', [status(esa)], [t81_relat_1])).
% 1.16/1.37  thf(dt_k6_partfun1, axiom,
% 1.16/1.37    (![A:$i]:
% 1.16/1.37     ( ( m1_subset_1 @
% 1.16/1.37         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 1.16/1.37       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 1.16/1.37  thf('14', plain, (![X30 : $i]: (v1_partfun1 @ (k6_partfun1 @ X30) @ X30)),
% 1.16/1.37      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 1.16/1.37  thf('15', plain, (![X32 : $i]: ((k6_partfun1 @ X32) = (k6_relat_1 @ X32))),
% 1.16/1.37      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.16/1.37  thf('16', plain, (![X30 : $i]: (v1_partfun1 @ (k6_relat_1 @ X30) @ X30)),
% 1.16/1.37      inference('demod', [status(thm)], ['14', '15'])).
% 1.16/1.37  thf('17', plain, ((v1_partfun1 @ k1_xboole_0 @ k1_xboole_0)),
% 1.16/1.37      inference('sup+', [status(thm)], ['13', '16'])).
% 1.16/1.37  thf('18', plain,
% 1.16/1.37      (![X0 : $i]: ((v1_partfun1 @ k1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X0))),
% 1.16/1.37      inference('sup+', [status(thm)], ['12', '17'])).
% 1.16/1.37  thf(t26_yellow_1, axiom,
% 1.16/1.37    (![A:$i]:
% 1.16/1.37     ( ( ( v1_relat_1 @ A ) & ( v4_relat_1 @ A @ k1_xboole_0 ) & 
% 1.16/1.37         ( v1_funct_1 @ A ) & ( v1_partfun1 @ A @ k1_xboole_0 ) & 
% 1.16/1.37         ( v1_yellow_1 @ A ) ) =>
% 1.16/1.37       ( ( k5_yellow_1 @ k1_xboole_0 @ A ) =
% 1.16/1.37         ( g1_orders_2 @
% 1.16/1.37           ( k1_tarski @ k1_xboole_0 ) @ 
% 1.16/1.37           ( k6_partfun1 @ ( k1_tarski @ k1_xboole_0 ) ) ) ) ))).
% 1.16/1.37  thf('19', plain,
% 1.16/1.37      (![X39 : $i]:
% 1.16/1.37         (((k5_yellow_1 @ k1_xboole_0 @ X39)
% 1.16/1.37            = (g1_orders_2 @ (k1_tarski @ k1_xboole_0) @ 
% 1.16/1.37               (k6_partfun1 @ (k1_tarski @ k1_xboole_0))))
% 1.16/1.37          | ~ (v1_yellow_1 @ X39)
% 1.16/1.37          | ~ (v1_partfun1 @ X39 @ k1_xboole_0)
% 1.16/1.37          | ~ (v1_funct_1 @ X39)
% 1.16/1.37          | ~ (v4_relat_1 @ X39 @ k1_xboole_0)
% 1.16/1.37          | ~ (v1_relat_1 @ X39))),
% 1.16/1.37      inference('cnf', [status(esa)], [t26_yellow_1])).
% 1.16/1.37  thf('20', plain, (![X32 : $i]: ((k6_partfun1 @ X32) = (k6_relat_1 @ X32))),
% 1.16/1.37      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.16/1.37  thf('21', plain,
% 1.16/1.37      (![X39 : $i]:
% 1.16/1.37         (((k5_yellow_1 @ k1_xboole_0 @ X39)
% 1.16/1.37            = (g1_orders_2 @ (k1_tarski @ k1_xboole_0) @ 
% 1.16/1.37               (k6_relat_1 @ (k1_tarski @ k1_xboole_0))))
% 1.16/1.37          | ~ (v1_yellow_1 @ X39)
% 1.16/1.37          | ~ (v1_partfun1 @ X39 @ k1_xboole_0)
% 1.16/1.37          | ~ (v1_funct_1 @ X39)
% 1.16/1.37          | ~ (v4_relat_1 @ X39 @ k1_xboole_0)
% 1.16/1.37          | ~ (v1_relat_1 @ X39))),
% 1.16/1.37      inference('demod', [status(thm)], ['19', '20'])).
% 1.16/1.37  thf('22', plain,
% 1.16/1.37      ((~ (v1_xboole_0 @ k1_xboole_0)
% 1.16/1.37        | ~ (v1_relat_1 @ k1_xboole_0)
% 1.16/1.37        | ~ (v4_relat_1 @ k1_xboole_0 @ k1_xboole_0)
% 1.16/1.37        | ~ (v1_funct_1 @ k1_xboole_0)
% 1.16/1.37        | ~ (v1_yellow_1 @ k1_xboole_0)
% 1.16/1.37        | ((k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0)
% 1.16/1.37            = (g1_orders_2 @ (k1_tarski @ k1_xboole_0) @ 
% 1.16/1.37               (k6_relat_1 @ (k1_tarski @ k1_xboole_0)))))),
% 1.16/1.37      inference('sup-', [status(thm)], ['18', '21'])).
% 1.16/1.37  thf('23', plain,
% 1.16/1.37      (![X35 : $i]: (v1_xboole_0 @ (k7_funcop_1 @ k1_xboole_0 @ X35))),
% 1.16/1.37      inference('demod', [status(thm)], ['0', '1'])).
% 1.16/1.37  thf('24', plain,
% 1.16/1.37      (![X0 : $i]: ((k7_funcop_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 1.16/1.37      inference('sup-', [status(thm)], ['2', '5'])).
% 1.16/1.37  thf('25', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.16/1.37      inference('demod', [status(thm)], ['23', '24'])).
% 1.16/1.37  thf('26', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.16/1.37      inference('cnf', [status(esa)], [t81_relat_1])).
% 1.16/1.37  thf(fc3_funct_1, axiom,
% 1.16/1.37    (![A:$i]:
% 1.16/1.37     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 1.16/1.37       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 1.16/1.37  thf('27', plain, (![X26 : $i]: (v1_relat_1 @ (k6_relat_1 @ X26))),
% 1.16/1.37      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.16/1.37  thf('28', plain, ((v1_relat_1 @ k1_xboole_0)),
% 1.16/1.37      inference('sup+', [status(thm)], ['26', '27'])).
% 1.16/1.37  thf('29', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.16/1.37      inference('cnf', [status(esa)], [t81_relat_1])).
% 1.16/1.37  thf('30', plain, (![X27 : $i]: (v1_funct_1 @ (k6_relat_1 @ X27))),
% 1.16/1.37      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.16/1.37  thf('31', plain, ((v1_funct_1 @ k1_xboole_0)),
% 1.16/1.37      inference('sup+', [status(thm)], ['29', '30'])).
% 1.16/1.37  thf('32', plain,
% 1.16/1.37      ((~ (v4_relat_1 @ k1_xboole_0 @ k1_xboole_0)
% 1.16/1.37        | ~ (v1_yellow_1 @ k1_xboole_0)
% 1.16/1.37        | ((k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0)
% 1.16/1.37            = (g1_orders_2 @ (k1_tarski @ k1_xboole_0) @ 
% 1.16/1.37               (k6_relat_1 @ (k1_tarski @ k1_xboole_0)))))),
% 1.16/1.37      inference('demod', [status(thm)], ['22', '25', '28', '31'])).
% 1.16/1.37  thf(rc1_yellow_1, axiom,
% 1.16/1.37    (![A:$i]:
% 1.16/1.37     ( ?[B:$i]:
% 1.16/1.37       ( ( v1_yellow_1 @ B ) & ( v1_partfun1 @ B @ A ) & ( v1_funct_1 @ B ) & 
% 1.16/1.37         ( v4_relat_1 @ B @ A ) & ( v1_relat_1 @ B ) ) ))).
% 1.16/1.37  thf('33', plain, (![X36 : $i]: (v1_partfun1 @ (sk_B_2 @ X36) @ X36)),
% 1.16/1.37      inference('cnf', [status(esa)], [rc1_yellow_1])).
% 1.16/1.37  thf(d4_partfun1, axiom,
% 1.16/1.37    (![A:$i,B:$i]:
% 1.16/1.37     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 1.16/1.37       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 1.16/1.37  thf('34', plain,
% 1.16/1.37      (![X28 : $i, X29 : $i]:
% 1.16/1.37         (~ (v1_partfun1 @ X29 @ X28)
% 1.16/1.37          | ((k1_relat_1 @ X29) = (X28))
% 1.16/1.37          | ~ (v4_relat_1 @ X29 @ X28)
% 1.16/1.37          | ~ (v1_relat_1 @ X29))),
% 1.16/1.37      inference('cnf', [status(esa)], [d4_partfun1])).
% 1.16/1.37  thf('35', plain,
% 1.16/1.37      (![X0 : $i]:
% 1.16/1.37         (~ (v1_relat_1 @ (sk_B_2 @ X0))
% 1.16/1.37          | ~ (v4_relat_1 @ (sk_B_2 @ X0) @ X0)
% 1.16/1.37          | ((k1_relat_1 @ (sk_B_2 @ X0)) = (X0)))),
% 1.16/1.37      inference('sup-', [status(thm)], ['33', '34'])).
% 1.16/1.37  thf('36', plain, (![X36 : $i]: (v1_relat_1 @ (sk_B_2 @ X36))),
% 1.16/1.37      inference('cnf', [status(esa)], [rc1_yellow_1])).
% 1.16/1.37  thf('37', plain, (![X36 : $i]: (v4_relat_1 @ (sk_B_2 @ X36) @ X36)),
% 1.16/1.37      inference('cnf', [status(esa)], [rc1_yellow_1])).
% 1.16/1.37  thf('38', plain, (![X0 : $i]: ((k1_relat_1 @ (sk_B_2 @ X0)) = (X0))),
% 1.16/1.37      inference('demod', [status(thm)], ['35', '36', '37'])).
% 1.16/1.37  thf(t64_relat_1, axiom,
% 1.16/1.37    (![A:$i]:
% 1.16/1.37     ( ( v1_relat_1 @ A ) =>
% 1.16/1.37       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 1.16/1.37           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 1.16/1.37         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 1.16/1.37  thf('39', plain,
% 1.16/1.37      (![X25 : $i]:
% 1.16/1.37         (((k1_relat_1 @ X25) != (k1_xboole_0))
% 1.16/1.37          | ((X25) = (k1_xboole_0))
% 1.16/1.37          | ~ (v1_relat_1 @ X25))),
% 1.16/1.37      inference('cnf', [status(esa)], [t64_relat_1])).
% 1.16/1.37  thf('40', plain,
% 1.16/1.37      (![X0 : $i]:
% 1.16/1.37         (((X0) != (k1_xboole_0))
% 1.16/1.37          | ~ (v1_relat_1 @ (sk_B_2 @ X0))
% 1.16/1.37          | ((sk_B_2 @ X0) = (k1_xboole_0)))),
% 1.16/1.37      inference('sup-', [status(thm)], ['38', '39'])).
% 1.16/1.37  thf('41', plain, (![X36 : $i]: (v1_relat_1 @ (sk_B_2 @ X36))),
% 1.16/1.37      inference('cnf', [status(esa)], [rc1_yellow_1])).
% 1.16/1.37  thf('42', plain,
% 1.16/1.37      (![X0 : $i]: (((X0) != (k1_xboole_0)) | ((sk_B_2 @ X0) = (k1_xboole_0)))),
% 1.16/1.37      inference('demod', [status(thm)], ['40', '41'])).
% 1.16/1.37  thf('43', plain, (((sk_B_2 @ k1_xboole_0) = (k1_xboole_0))),
% 1.16/1.37      inference('simplify', [status(thm)], ['42'])).
% 1.16/1.37  thf('44', plain, (![X36 : $i]: (v4_relat_1 @ (sk_B_2 @ X36) @ X36)),
% 1.16/1.37      inference('cnf', [status(esa)], [rc1_yellow_1])).
% 1.16/1.37  thf('45', plain, ((v4_relat_1 @ k1_xboole_0 @ k1_xboole_0)),
% 1.16/1.37      inference('sup+', [status(thm)], ['43', '44'])).
% 1.16/1.37  thf('46', plain, (((sk_B_2 @ k1_xboole_0) = (k1_xboole_0))),
% 1.16/1.37      inference('simplify', [status(thm)], ['42'])).
% 1.16/1.37  thf('47', plain, (![X36 : $i]: (v1_yellow_1 @ (sk_B_2 @ X36))),
% 1.16/1.37      inference('cnf', [status(esa)], [rc1_yellow_1])).
% 1.16/1.37  thf('48', plain, ((v1_yellow_1 @ k1_xboole_0)),
% 1.16/1.37      inference('sup+', [status(thm)], ['46', '47'])).
% 1.16/1.37  thf('49', plain,
% 1.16/1.37      (((k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0)
% 1.16/1.37         = (g1_orders_2 @ (k1_tarski @ k1_xboole_0) @ 
% 1.16/1.37            (k6_relat_1 @ (k1_tarski @ k1_xboole_0))))),
% 1.16/1.37      inference('demod', [status(thm)], ['32', '45', '48'])).
% 1.16/1.37  thf('50', plain,
% 1.16/1.37      (((k6_yellow_1 @ k1_xboole_0 @ sk_A)
% 1.16/1.37         != (k5_yellow_1 @ k1_xboole_0 @ k1_xboole_0))),
% 1.16/1.37      inference('demod', [status(thm)], ['11', '49'])).
% 1.16/1.37  thf('51', plain,
% 1.16/1.37      (![X0 : $i]:
% 1.16/1.37         (((k6_yellow_1 @ k1_xboole_0 @ sk_A)
% 1.16/1.37            != (k6_yellow_1 @ k1_xboole_0 @ X0))
% 1.16/1.37          | ~ (l1_orders_2 @ X0))),
% 1.16/1.37      inference('sup-', [status(thm)], ['8', '50'])).
% 1.16/1.37  thf('52', plain, (~ (l1_orders_2 @ sk_A)),
% 1.16/1.37      inference('eq_res', [status(thm)], ['51'])).
% 1.16/1.37  thf('53', plain, ((l1_orders_2 @ sk_A)),
% 1.16/1.37      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.16/1.37  thf('54', plain, ($false), inference('demod', [status(thm)], ['52', '53'])).
% 1.16/1.37  
% 1.16/1.37  % SZS output end Refutation
% 1.16/1.37  
% 1.16/1.38  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
