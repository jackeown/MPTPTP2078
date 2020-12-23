%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZLlTnsXtXA

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:49 EST 2020

% Result     : Theorem 0.24s
% Output     : Refutation 0.24s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 107 expanded)
%              Number of leaves         :   34 (  46 expanded)
%              Depth                    :   13
%              Number of atoms          :  384 ( 632 expanded)
%              Number of equality atoms :   28 (  33 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_yellow_1_type,type,(
    k2_yellow_1: $i > $i )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_yellow_1_type,type,(
    k1_yellow_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(v1_orders_2_type,type,(
    v1_orders_2: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t6_tex_2,conjecture,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ A )
         => ~ ( ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A )
              & ( v1_zfmisc_1 @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( v1_xboole_0 @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ A )
           => ~ ( ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A )
                & ( v1_zfmisc_1 @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t6_tex_2])).

thf('0',plain,(
    v1_subset_1 @ ( k6_domain_1 @ sk_A @ sk_B ) @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('2',plain,(
    ! [X18: $i,X19: $i] :
      ( ( v1_xboole_0 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ X18 )
      | ( ( k6_domain_1 @ X18 @ X19 )
        = ( k1_tarski @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('3',plain,
    ( ( ( k6_domain_1 @ sk_A @ sk_B )
      = ( k1_tarski @ sk_B ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( k6_domain_1 @ sk_A @ sk_B )
    = ( k1_tarski @ sk_B ) ),
    inference(clc,[status(thm)],['3','4'])).

thf('6',plain,(
    v1_subset_1 @ ( k1_tarski @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['0','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('8',plain,(
    ! [X15: $i,X16: $i] :
      ( ( v1_xboole_0 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ X15 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X15 @ X16 ) @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('9',plain,
    ( ( m1_subset_1 @ ( k6_domain_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( k6_domain_1 @ sk_A @ sk_B )
    = ( k1_tarski @ sk_B ) ),
    inference(clc,[status(thm)],['3','4'])).

thf('11',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    m1_subset_1 @ ( k1_tarski @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['11','12'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('14',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('15',plain,(
    r1_tarski @ ( k1_tarski @ sk_B ) @ sk_A ),
    inference('sup-',[status(thm)],['13','14'])).

thf(t1_tex_2,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( v1_zfmisc_1 @ B ) )
         => ( ( r1_tarski @ A @ B )
           => ( A = B ) ) ) ) )).

thf('16',plain,(
    ! [X24: $i,X25: $i] :
      ( ( v1_xboole_0 @ X24 )
      | ~ ( v1_zfmisc_1 @ X24 )
      | ( X25 = X24 )
      | ~ ( r1_tarski @ X25 @ X24 )
      | ( v1_xboole_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t1_tex_2])).

thf('17',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ sk_B ) )
    | ( ( k1_tarski @ sk_B )
      = sk_A )
    | ~ ( v1_zfmisc_1 @ sk_A )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v1_zfmisc_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ sk_B ) )
    | ( ( k1_tarski @ sk_B )
      = sk_A )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['17','18'])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('20',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X2 )
      | ( X1 = X2 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf('22',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X8 ) @ X9 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('25',plain,(
    ! [X1: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_tarski @ X1 ) )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('26',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('27',plain,(
    ! [X1: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X1 ) ) ),
    inference('simplify_reflect+',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( ( k1_tarski @ sk_B )
      = sk_A ) ),
    inference(clc,[status(thm)],['19','27'])).

thf('29',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( k1_tarski @ sk_B )
    = sk_A ),
    inference(clc,[status(thm)],['28','29'])).

thf('31',plain,(
    v1_subset_1 @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['6','30'])).

thf(dt_l1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('32',plain,(
    ! [X17: $i] :
      ( ( l1_struct_0 @ X17 )
      | ~ ( l1_orders_2 @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_orders_2])).

thf(t1_yellow_1,axiom,(
    ! [A: $i] :
      ( ( ( u1_orders_2 @ ( k2_yellow_1 @ A ) )
        = ( k1_yellow_1 @ A ) )
      & ( ( u1_struct_0 @ ( k2_yellow_1 @ A ) )
        = A ) ) )).

thf('33',plain,(
    ! [X22: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X22 ) )
      = X22 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf(fc12_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ~ ( v1_subset_1 @ ( k2_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) )).

thf('34',plain,(
    ! [X14: $i] :
      ( ~ ( v1_subset_1 @ ( k2_struct_0 @ X14 ) @ ( u1_struct_0 @ X14 ) )
      | ~ ( l1_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc12_struct_0])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( v1_subset_1 @ ( k2_struct_0 @ ( k2_yellow_1 @ X0 ) ) @ X0 )
      | ~ ( l1_struct_0 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X17: $i] :
      ( ( l1_struct_0 @ X17 )
      | ~ ( l1_orders_2 @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_orders_2])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('37',plain,(
    ! [X13: $i] :
      ( ( ( k2_struct_0 @ X13 )
        = ( u1_struct_0 @ X13 ) )
      | ~ ( l1_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('38',plain,(
    ! [X22: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X22 ) )
      = X22 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( ( k2_struct_0 @ ( k2_yellow_1 @ X0 ) )
        = X0 )
      | ~ ( l1_struct_0 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ( ( k2_struct_0 @ ( k2_yellow_1 @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf(dt_k2_yellow_1,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ) )).

thf('41',plain,(
    ! [X21: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k2_struct_0 @ ( k2_yellow_1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( v1_subset_1 @ X0 @ X0 )
      | ~ ( l1_struct_0 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['35','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v1_subset_1 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','43'])).

thf('45',plain,(
    ! [X21: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('46',plain,(
    ! [X0: $i] :
      ~ ( v1_subset_1 @ X0 @ X0 ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    $false ),
    inference('sup-',[status(thm)],['31','46'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZLlTnsXtXA
% 0.15/0.38  % Computer   : n016.cluster.edu
% 0.15/0.38  % Model      : x86_64 x86_64
% 0.15/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.38  % Memory     : 8042.1875MB
% 0.15/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.38  % CPULimit   : 60
% 0.15/0.38  % DateTime   : Tue Dec  1 10:34:50 EST 2020
% 0.15/0.38  % CPUTime    : 
% 0.15/0.38  % Running portfolio for 600 s
% 0.15/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.38  % Number of cores: 8
% 0.15/0.38  % Python version: Python 3.6.8
% 0.15/0.38  % Running in FO mode
% 0.24/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.24/0.55  % Solved by: fo/fo7.sh
% 0.24/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.24/0.55  % done 108 iterations in 0.056s
% 0.24/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.24/0.55  % SZS output start Refutation
% 0.24/0.55  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.24/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.24/0.55  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.24/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.24/0.55  thf(k2_yellow_1_type, type, k2_yellow_1: $i > $i).
% 0.24/0.55  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.24/0.55  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.24/0.55  thf(u1_orders_2_type, type, u1_orders_2: $i > $i).
% 0.24/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.24/0.55  thf(k1_yellow_1_type, type, k1_yellow_1: $i > $i).
% 0.24/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.24/0.55  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.24/0.55  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.24/0.55  thf(v1_orders_2_type, type, v1_orders_2: $i > $o).
% 0.24/0.55  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.24/0.55  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.24/0.55  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.24/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.24/0.55  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.24/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.24/0.55  thf(t6_tex_2, conjecture,
% 0.24/0.55    (![A:$i]:
% 0.24/0.55     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.24/0.55       ( ![B:$i]:
% 0.24/0.55         ( ( m1_subset_1 @ B @ A ) =>
% 0.24/0.55           ( ~( ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A ) & 
% 0.24/0.55                ( v1_zfmisc_1 @ A ) ) ) ) ) ))).
% 0.24/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.24/0.55    (~( ![A:$i]:
% 0.24/0.55        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.24/0.55          ( ![B:$i]:
% 0.24/0.55            ( ( m1_subset_1 @ B @ A ) =>
% 0.24/0.55              ( ~( ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A ) & 
% 0.24/0.55                   ( v1_zfmisc_1 @ A ) ) ) ) ) ) )),
% 0.24/0.55    inference('cnf.neg', [status(esa)], [t6_tex_2])).
% 0.24/0.55  thf('0', plain, ((v1_subset_1 @ (k6_domain_1 @ sk_A @ sk_B) @ sk_A)),
% 0.24/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.55  thf('1', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 0.24/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.55  thf(redefinition_k6_domain_1, axiom,
% 0.24/0.55    (![A:$i,B:$i]:
% 0.24/0.55     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.24/0.55       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.24/0.55  thf('2', plain,
% 0.24/0.55      (![X18 : $i, X19 : $i]:
% 0.24/0.55         ((v1_xboole_0 @ X18)
% 0.24/0.55          | ~ (m1_subset_1 @ X19 @ X18)
% 0.24/0.55          | ((k6_domain_1 @ X18 @ X19) = (k1_tarski @ X19)))),
% 0.24/0.55      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.24/0.55  thf('3', plain,
% 0.24/0.55      ((((k6_domain_1 @ sk_A @ sk_B) = (k1_tarski @ sk_B))
% 0.24/0.55        | (v1_xboole_0 @ sk_A))),
% 0.24/0.55      inference('sup-', [status(thm)], ['1', '2'])).
% 0.24/0.55  thf('4', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.24/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.55  thf('5', plain, (((k6_domain_1 @ sk_A @ sk_B) = (k1_tarski @ sk_B))),
% 0.24/0.55      inference('clc', [status(thm)], ['3', '4'])).
% 0.24/0.55  thf('6', plain, ((v1_subset_1 @ (k1_tarski @ sk_B) @ sk_A)),
% 0.24/0.55      inference('demod', [status(thm)], ['0', '5'])).
% 0.24/0.55  thf('7', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 0.24/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.55  thf(dt_k6_domain_1, axiom,
% 0.24/0.55    (![A:$i,B:$i]:
% 0.24/0.55     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.24/0.55       ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.24/0.55  thf('8', plain,
% 0.24/0.55      (![X15 : $i, X16 : $i]:
% 0.24/0.55         ((v1_xboole_0 @ X15)
% 0.24/0.55          | ~ (m1_subset_1 @ X16 @ X15)
% 0.24/0.55          | (m1_subset_1 @ (k6_domain_1 @ X15 @ X16) @ (k1_zfmisc_1 @ X15)))),
% 0.24/0.55      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.24/0.55  thf('9', plain,
% 0.24/0.55      (((m1_subset_1 @ (k6_domain_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))
% 0.24/0.55        | (v1_xboole_0 @ sk_A))),
% 0.24/0.55      inference('sup-', [status(thm)], ['7', '8'])).
% 0.24/0.55  thf('10', plain, (((k6_domain_1 @ sk_A @ sk_B) = (k1_tarski @ sk_B))),
% 0.24/0.55      inference('clc', [status(thm)], ['3', '4'])).
% 0.24/0.55  thf('11', plain,
% 0.24/0.55      (((m1_subset_1 @ (k1_tarski @ sk_B) @ (k1_zfmisc_1 @ sk_A))
% 0.24/0.55        | (v1_xboole_0 @ sk_A))),
% 0.24/0.55      inference('demod', [status(thm)], ['9', '10'])).
% 0.24/0.55  thf('12', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.24/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.55  thf('13', plain, ((m1_subset_1 @ (k1_tarski @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.24/0.55      inference('clc', [status(thm)], ['11', '12'])).
% 0.24/0.55  thf(t3_subset, axiom,
% 0.24/0.55    (![A:$i,B:$i]:
% 0.24/0.55     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.24/0.55  thf('14', plain,
% 0.24/0.55      (![X10 : $i, X11 : $i]:
% 0.24/0.55         ((r1_tarski @ X10 @ X11) | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 0.24/0.55      inference('cnf', [status(esa)], [t3_subset])).
% 0.24/0.55  thf('15', plain, ((r1_tarski @ (k1_tarski @ sk_B) @ sk_A)),
% 0.24/0.55      inference('sup-', [status(thm)], ['13', '14'])).
% 0.24/0.55  thf(t1_tex_2, axiom,
% 0.24/0.55    (![A:$i]:
% 0.24/0.55     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.24/0.55       ( ![B:$i]:
% 0.24/0.55         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v1_zfmisc_1 @ B ) ) =>
% 0.24/0.55           ( ( r1_tarski @ A @ B ) => ( ( A ) = ( B ) ) ) ) ) ))).
% 0.24/0.55  thf('16', plain,
% 0.24/0.55      (![X24 : $i, X25 : $i]:
% 0.24/0.55         ((v1_xboole_0 @ X24)
% 0.24/0.55          | ~ (v1_zfmisc_1 @ X24)
% 0.24/0.55          | ((X25) = (X24))
% 0.24/0.55          | ~ (r1_tarski @ X25 @ X24)
% 0.24/0.55          | (v1_xboole_0 @ X25))),
% 0.24/0.55      inference('cnf', [status(esa)], [t1_tex_2])).
% 0.24/0.55  thf('17', plain,
% 0.24/0.55      (((v1_xboole_0 @ (k1_tarski @ sk_B))
% 0.24/0.55        | ((k1_tarski @ sk_B) = (sk_A))
% 0.24/0.55        | ~ (v1_zfmisc_1 @ sk_A)
% 0.24/0.55        | (v1_xboole_0 @ sk_A))),
% 0.24/0.55      inference('sup-', [status(thm)], ['15', '16'])).
% 0.24/0.55  thf('18', plain, ((v1_zfmisc_1 @ sk_A)),
% 0.24/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.55  thf('19', plain,
% 0.24/0.55      (((v1_xboole_0 @ (k1_tarski @ sk_B))
% 0.24/0.55        | ((k1_tarski @ sk_B) = (sk_A))
% 0.24/0.55        | (v1_xboole_0 @ sk_A))),
% 0.24/0.55      inference('demod', [status(thm)], ['17', '18'])).
% 0.24/0.55  thf(t8_boole, axiom,
% 0.24/0.55    (![A:$i,B:$i]:
% 0.24/0.55     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 0.24/0.55  thf('20', plain,
% 0.24/0.55      (![X1 : $i, X2 : $i]:
% 0.24/0.55         (~ (v1_xboole_0 @ X1) | ~ (v1_xboole_0 @ X2) | ((X1) = (X2)))),
% 0.24/0.55      inference('cnf', [status(esa)], [t8_boole])).
% 0.24/0.55  thf(idempotence_k2_xboole_0, axiom,
% 0.24/0.55    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.24/0.55  thf('21', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.24/0.55      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.24/0.55  thf(t49_zfmisc_1, axiom,
% 0.24/0.55    (![A:$i,B:$i]:
% 0.24/0.55     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.24/0.55  thf('22', plain,
% 0.24/0.55      (![X8 : $i, X9 : $i]:
% 0.24/0.55         ((k2_xboole_0 @ (k1_tarski @ X8) @ X9) != (k1_xboole_0))),
% 0.24/0.55      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 0.24/0.55  thf('23', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 0.24/0.55      inference('sup-', [status(thm)], ['21', '22'])).
% 0.24/0.55  thf('24', plain,
% 0.24/0.55      (![X0 : $i, X1 : $i]:
% 0.24/0.55         (((X0) != (k1_xboole_0))
% 0.24/0.55          | ~ (v1_xboole_0 @ X0)
% 0.24/0.55          | ~ (v1_xboole_0 @ (k1_tarski @ X1)))),
% 0.24/0.55      inference('sup-', [status(thm)], ['20', '23'])).
% 0.24/0.55  thf('25', plain,
% 0.24/0.55      (![X1 : $i]:
% 0.24/0.55         (~ (v1_xboole_0 @ (k1_tarski @ X1)) | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.24/0.55      inference('simplify', [status(thm)], ['24'])).
% 0.24/0.55  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.24/0.55  thf('26', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.24/0.55      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.24/0.55  thf('27', plain, (![X1 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X1))),
% 0.24/0.55      inference('simplify_reflect+', [status(thm)], ['25', '26'])).
% 0.24/0.55  thf('28', plain, (((v1_xboole_0 @ sk_A) | ((k1_tarski @ sk_B) = (sk_A)))),
% 0.24/0.55      inference('clc', [status(thm)], ['19', '27'])).
% 0.24/0.55  thf('29', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.24/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.55  thf('30', plain, (((k1_tarski @ sk_B) = (sk_A))),
% 0.24/0.55      inference('clc', [status(thm)], ['28', '29'])).
% 0.24/0.55  thf('31', plain, ((v1_subset_1 @ sk_A @ sk_A)),
% 0.24/0.55      inference('demod', [status(thm)], ['6', '30'])).
% 0.24/0.55  thf(dt_l1_orders_2, axiom,
% 0.24/0.55    (![A:$i]: ( ( l1_orders_2 @ A ) => ( l1_struct_0 @ A ) ))).
% 0.24/0.55  thf('32', plain,
% 0.24/0.55      (![X17 : $i]: ((l1_struct_0 @ X17) | ~ (l1_orders_2 @ X17))),
% 0.24/0.55      inference('cnf', [status(esa)], [dt_l1_orders_2])).
% 0.24/0.55  thf(t1_yellow_1, axiom,
% 0.24/0.55    (![A:$i]:
% 0.24/0.55     ( ( ( u1_orders_2 @ ( k2_yellow_1 @ A ) ) = ( k1_yellow_1 @ A ) ) & 
% 0.24/0.55       ( ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) = ( A ) ) ))).
% 0.24/0.55  thf('33', plain,
% 0.24/0.55      (![X22 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X22)) = (X22))),
% 0.24/0.55      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.24/0.55  thf(fc12_struct_0, axiom,
% 0.24/0.55    (![A:$i]:
% 0.24/0.55     ( ( l1_struct_0 @ A ) =>
% 0.24/0.55       ( ~( v1_subset_1 @ ( k2_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) ))).
% 0.24/0.55  thf('34', plain,
% 0.24/0.55      (![X14 : $i]:
% 0.24/0.55         (~ (v1_subset_1 @ (k2_struct_0 @ X14) @ (u1_struct_0 @ X14))
% 0.24/0.55          | ~ (l1_struct_0 @ X14))),
% 0.24/0.55      inference('cnf', [status(esa)], [fc12_struct_0])).
% 0.24/0.55  thf('35', plain,
% 0.24/0.55      (![X0 : $i]:
% 0.24/0.55         (~ (v1_subset_1 @ (k2_struct_0 @ (k2_yellow_1 @ X0)) @ X0)
% 0.24/0.55          | ~ (l1_struct_0 @ (k2_yellow_1 @ X0)))),
% 0.24/0.55      inference('sup-', [status(thm)], ['33', '34'])).
% 0.24/0.55  thf('36', plain,
% 0.24/0.55      (![X17 : $i]: ((l1_struct_0 @ X17) | ~ (l1_orders_2 @ X17))),
% 0.24/0.55      inference('cnf', [status(esa)], [dt_l1_orders_2])).
% 0.24/0.55  thf(d3_struct_0, axiom,
% 0.24/0.55    (![A:$i]:
% 0.24/0.55     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.24/0.55  thf('37', plain,
% 0.24/0.55      (![X13 : $i]:
% 0.24/0.55         (((k2_struct_0 @ X13) = (u1_struct_0 @ X13)) | ~ (l1_struct_0 @ X13))),
% 0.24/0.55      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.24/0.55  thf('38', plain,
% 0.24/0.55      (![X22 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X22)) = (X22))),
% 0.24/0.55      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.24/0.55  thf('39', plain,
% 0.24/0.55      (![X0 : $i]:
% 0.24/0.55         (((k2_struct_0 @ (k2_yellow_1 @ X0)) = (X0))
% 0.24/0.55          | ~ (l1_struct_0 @ (k2_yellow_1 @ X0)))),
% 0.24/0.55      inference('sup+', [status(thm)], ['37', '38'])).
% 0.24/0.55  thf('40', plain,
% 0.24/0.55      (![X0 : $i]:
% 0.24/0.55         (~ (l1_orders_2 @ (k2_yellow_1 @ X0))
% 0.24/0.55          | ((k2_struct_0 @ (k2_yellow_1 @ X0)) = (X0)))),
% 0.24/0.55      inference('sup-', [status(thm)], ['36', '39'])).
% 0.24/0.55  thf(dt_k2_yellow_1, axiom,
% 0.24/0.55    (![A:$i]:
% 0.24/0.55     ( ( l1_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.24/0.55       ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ))).
% 0.24/0.55  thf('41', plain, (![X21 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X21))),
% 0.24/0.55      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.24/0.55  thf('42', plain, (![X0 : $i]: ((k2_struct_0 @ (k2_yellow_1 @ X0)) = (X0))),
% 0.24/0.55      inference('demod', [status(thm)], ['40', '41'])).
% 0.24/0.55  thf('43', plain,
% 0.24/0.55      (![X0 : $i]:
% 0.24/0.55         (~ (v1_subset_1 @ X0 @ X0) | ~ (l1_struct_0 @ (k2_yellow_1 @ X0)))),
% 0.24/0.55      inference('demod', [status(thm)], ['35', '42'])).
% 0.24/0.55  thf('44', plain,
% 0.24/0.55      (![X0 : $i]:
% 0.24/0.55         (~ (l1_orders_2 @ (k2_yellow_1 @ X0)) | ~ (v1_subset_1 @ X0 @ X0))),
% 0.24/0.55      inference('sup-', [status(thm)], ['32', '43'])).
% 0.24/0.55  thf('45', plain, (![X21 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X21))),
% 0.24/0.55      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.24/0.55  thf('46', plain, (![X0 : $i]: ~ (v1_subset_1 @ X0 @ X0)),
% 0.24/0.55      inference('demod', [status(thm)], ['44', '45'])).
% 0.24/0.55  thf('47', plain, ($false), inference('sup-', [status(thm)], ['31', '46'])).
% 0.24/0.55  
% 0.24/0.55  % SZS output end Refutation
% 0.24/0.55  
% 0.24/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
