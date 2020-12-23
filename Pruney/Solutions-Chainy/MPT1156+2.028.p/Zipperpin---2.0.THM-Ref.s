%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.I9CQg0VP0d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:01:56 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   66 (  92 expanded)
%              Number of leaves         :   26 (  39 expanded)
%              Depth                    :   15
%              Number of atoms          :  422 ( 994 expanded)
%              Number of equality atoms :   11 (  11 expanded)
%              Maximal formula depth    :   15 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v6_orders_2_type,type,(
    v6_orders_2: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(k2_orders_2_type,type,(
    k2_orders_2: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(t50_orders_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ~ ( r2_hidden @ B @ ( k2_orders_2 @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v3_orders_2 @ A )
          & ( v4_orders_2 @ A )
          & ( v5_orders_2 @ A )
          & ( l1_orders_2 @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ~ ( r2_hidden @ B @ ( k2_orders_2 @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t50_orders_2])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('2',plain,(
    ! [X8: $i,X9: $i] :
      ( ( v1_xboole_0 @ X8 )
      | ~ ( m1_subset_1 @ X9 @ X8 )
      | ( ( k6_domain_1 @ X8 @ X9 )
        = ( k1_tarski @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('3',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t35_orders_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( ( v6_orders_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A )
            & ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) )).

thf('6',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X11 ) )
      | ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ X11 ) @ X10 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( l1_orders_2 @ X11 )
      | ~ ( v3_orders_2 @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t35_orders_2])).

thf('7',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['7','8','9'])).

thf('11',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['10','11'])).

thf(t49_orders_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ~ ( ( r2_hidden @ B @ C )
                  & ( r2_hidden @ B @ ( k2_orders_2 @ A @ C ) ) ) ) ) ) )).

thf('13',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X13 ) )
      | ~ ( r2_hidden @ X12 @ ( k2_orders_2 @ X13 @ X14 ) )
      | ~ ( r2_hidden @ X12 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( l1_orders_2 @ X13 )
      | ~ ( v5_orders_2 @ X13 )
      | ~ ( v4_orders_2 @ X13 )
      | ~ ( v3_orders_2 @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t49_orders_2])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['14','15','16','17','18'])).

thf('20',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r2_hidden @ sk_B @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['4','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ~ ( r2_hidden @ sk_B @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('25',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k1_tarski @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','24'])).

thf(t67_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = ( k1_tarski @ A ) )
    <=> ~ ( r2_hidden @ A @ B ) ) )).

thf('26',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X3 ) @ X5 )
        = ( k1_tarski @ X3 ) )
      | ( r2_hidden @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t67_zfmisc_1])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 != X0 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
       != ( k1_tarski @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) )
     != ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
       != ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['26','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['25','30'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('32',plain,(
    ! [X6: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('33',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('35',plain,(
    ! [X7: $i] :
      ( ( l1_struct_0 @ X7 )
      | ~ ( l1_orders_2 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_orders_2])).

thf('36',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['33','36'])).

thf('38',plain,(
    $false ),
    inference(demod,[status(thm)],['0','37'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.I9CQg0VP0d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:20:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.47  % Solved by: fo/fo7.sh
% 0.20/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.47  % done 34 iterations in 0.018s
% 0.20/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.47  % SZS output start Refutation
% 0.20/0.47  thf(v6_orders_2_type, type, v6_orders_2: $i > $i > $o).
% 0.20/0.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.47  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.47  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.20/0.47  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.20/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.47  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.47  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.47  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.20/0.47  thf(k2_orders_2_type, type, k2_orders_2: $i > $i > $i).
% 0.20/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.47  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.47  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.20/0.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.47  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.47  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.20/0.47  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.20/0.47  thf(t50_orders_2, conjecture,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.20/0.47         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.20/0.47       ( ![B:$i]:
% 0.20/0.47         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.47           ( ~( r2_hidden @
% 0.20/0.47                B @ 
% 0.20/0.47                ( k2_orders_2 @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 0.20/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.47    (~( ![A:$i]:
% 0.20/0.47        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.20/0.47            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.20/0.47          ( ![B:$i]:
% 0.20/0.47            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.47              ( ~( r2_hidden @
% 0.20/0.47                   B @ 
% 0.20/0.47                   ( k2_orders_2 @
% 0.20/0.47                     A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ) )),
% 0.20/0.47    inference('cnf.neg', [status(esa)], [t50_orders_2])).
% 0.20/0.47  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('1', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(redefinition_k6_domain_1, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.20/0.47       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.20/0.47  thf('2', plain,
% 0.20/0.47      (![X8 : $i, X9 : $i]:
% 0.20/0.47         ((v1_xboole_0 @ X8)
% 0.20/0.47          | ~ (m1_subset_1 @ X9 @ X8)
% 0.20/0.47          | ((k6_domain_1 @ X8 @ X9) = (k1_tarski @ X9)))),
% 0.20/0.47      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.20/0.47  thf('3', plain,
% 0.20/0.47      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) = (k1_tarski @ sk_B))
% 0.20/0.47        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.47  thf('4', plain,
% 0.20/0.47      ((r2_hidden @ sk_B @ 
% 0.20/0.47        (k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('5', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(t35_orders_2, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.20/0.47       ( ![B:$i]:
% 0.20/0.47         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.47           ( ( v6_orders_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) & 
% 0.20/0.47             ( m1_subset_1 @
% 0.20/0.47               ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 0.20/0.47               ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 0.20/0.47  thf('6', plain,
% 0.20/0.47      (![X10 : $i, X11 : $i]:
% 0.20/0.47         (~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X11))
% 0.20/0.47          | (m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ X11) @ X10) @ 
% 0.20/0.47             (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.20/0.47          | ~ (l1_orders_2 @ X11)
% 0.20/0.47          | ~ (v3_orders_2 @ X11)
% 0.20/0.47          | (v2_struct_0 @ X11))),
% 0.20/0.47      inference('cnf', [status(esa)], [t35_orders_2])).
% 0.20/0.47  thf('7', plain,
% 0.20/0.47      (((v2_struct_0 @ sk_A)
% 0.20/0.47        | ~ (v3_orders_2 @ sk_A)
% 0.20/0.47        | ~ (l1_orders_2 @ sk_A)
% 0.20/0.47        | (m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.20/0.47           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.47      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.47  thf('8', plain, ((v3_orders_2 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('9', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('10', plain,
% 0.20/0.47      (((v2_struct_0 @ sk_A)
% 0.20/0.47        | (m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.20/0.47           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.47      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.20/0.47  thf('11', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('12', plain,
% 0.20/0.47      ((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.20/0.47        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.47      inference('clc', [status(thm)], ['10', '11'])).
% 0.20/0.47  thf(t49_orders_2, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.20/0.47         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.20/0.47       ( ![B:$i]:
% 0.20/0.47         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.47           ( ![C:$i]:
% 0.20/0.47             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.47               ( ~( ( r2_hidden @ B @ C ) & 
% 0.20/0.47                    ( r2_hidden @ B @ ( k2_orders_2 @ A @ C ) ) ) ) ) ) ) ) ))).
% 0.20/0.47  thf('13', plain,
% 0.20/0.47      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.20/0.47         (~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X13))
% 0.20/0.47          | ~ (r2_hidden @ X12 @ (k2_orders_2 @ X13 @ X14))
% 0.20/0.47          | ~ (r2_hidden @ X12 @ X14)
% 0.20/0.47          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.20/0.47          | ~ (l1_orders_2 @ X13)
% 0.20/0.47          | ~ (v5_orders_2 @ X13)
% 0.20/0.47          | ~ (v4_orders_2 @ X13)
% 0.20/0.47          | ~ (v3_orders_2 @ X13)
% 0.20/0.47          | (v2_struct_0 @ X13))),
% 0.20/0.47      inference('cnf', [status(esa)], [t49_orders_2])).
% 0.20/0.47  thf('14', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((v2_struct_0 @ sk_A)
% 0.20/0.47          | ~ (v3_orders_2 @ sk_A)
% 0.20/0.47          | ~ (v4_orders_2 @ sk_A)
% 0.20/0.47          | ~ (v5_orders_2 @ sk_A)
% 0.20/0.47          | ~ (l1_orders_2 @ sk_A)
% 0.20/0.47          | ~ (r2_hidden @ X0 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.20/0.47          | ~ (r2_hidden @ X0 @ 
% 0.20/0.47               (k2_orders_2 @ sk_A @ 
% 0.20/0.47                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 0.20/0.47          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.47  thf('15', plain, ((v3_orders_2 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('16', plain, ((v4_orders_2 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('17', plain, ((v5_orders_2 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('18', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('19', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((v2_struct_0 @ sk_A)
% 0.20/0.47          | ~ (r2_hidden @ X0 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.20/0.47          | ~ (r2_hidden @ X0 @ 
% 0.20/0.47               (k2_orders_2 @ sk_A @ 
% 0.20/0.47                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 0.20/0.47          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.47      inference('demod', [status(thm)], ['14', '15', '16', '17', '18'])).
% 0.20/0.47  thf('20', plain,
% 0.20/0.47      ((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.20/0.47        | ~ (r2_hidden @ sk_B @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.20/0.47        | (v2_struct_0 @ sk_A))),
% 0.20/0.47      inference('sup-', [status(thm)], ['4', '19'])).
% 0.20/0.47  thf('21', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('22', plain,
% 0.20/0.47      ((~ (r2_hidden @ sk_B @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.20/0.47        | (v2_struct_0 @ sk_A))),
% 0.20/0.47      inference('demod', [status(thm)], ['20', '21'])).
% 0.20/0.47  thf('23', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('24', plain,
% 0.20/0.47      (~ (r2_hidden @ sk_B @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.20/0.47      inference('clc', [status(thm)], ['22', '23'])).
% 0.20/0.47  thf('25', plain,
% 0.20/0.47      ((~ (r2_hidden @ sk_B @ (k1_tarski @ sk_B))
% 0.20/0.47        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['3', '24'])).
% 0.20/0.47  thf(t67_zfmisc_1, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) <=>
% 0.20/0.47       ( ~( r2_hidden @ A @ B ) ) ))).
% 0.20/0.47  thf('26', plain,
% 0.20/0.47      (![X3 : $i, X5 : $i]:
% 0.20/0.47         (((k4_xboole_0 @ (k1_tarski @ X3) @ X5) = (k1_tarski @ X3))
% 0.20/0.47          | (r2_hidden @ X3 @ X5))),
% 0.20/0.47      inference('cnf', [status(esa)], [t67_zfmisc_1])).
% 0.20/0.47  thf(t20_zfmisc_1, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.20/0.47         ( k1_tarski @ A ) ) <=>
% 0.20/0.47       ( ( A ) != ( B ) ) ))).
% 0.20/0.47  thf('27', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         (((X1) != (X0))
% 0.20/0.47          | ((k4_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 0.20/0.47              != (k1_tarski @ X1)))),
% 0.20/0.47      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.20/0.47  thf('28', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((k4_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0))
% 0.20/0.47           != (k1_tarski @ X0))),
% 0.20/0.47      inference('simplify', [status(thm)], ['27'])).
% 0.20/0.47  thf('29', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         (((k1_tarski @ X0) != (k1_tarski @ X0))
% 0.20/0.47          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['26', '28'])).
% 0.20/0.47  thf('30', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.20/0.47      inference('simplify', [status(thm)], ['29'])).
% 0.20/0.47  thf('31', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.20/0.47      inference('demod', [status(thm)], ['25', '30'])).
% 0.20/0.47  thf(fc2_struct_0, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.20/0.47       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.20/0.47  thf('32', plain,
% 0.20/0.47      (![X6 : $i]:
% 0.20/0.47         (~ (v1_xboole_0 @ (u1_struct_0 @ X6))
% 0.20/0.47          | ~ (l1_struct_0 @ X6)
% 0.20/0.47          | (v2_struct_0 @ X6))),
% 0.20/0.47      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.20/0.47  thf('33', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 0.20/0.47      inference('sup-', [status(thm)], ['31', '32'])).
% 0.20/0.47  thf('34', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(dt_l1_orders_2, axiom,
% 0.20/0.47    (![A:$i]: ( ( l1_orders_2 @ A ) => ( l1_struct_0 @ A ) ))).
% 0.20/0.47  thf('35', plain, (![X7 : $i]: ((l1_struct_0 @ X7) | ~ (l1_orders_2 @ X7))),
% 0.20/0.47      inference('cnf', [status(esa)], [dt_l1_orders_2])).
% 0.20/0.47  thf('36', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.47      inference('sup-', [status(thm)], ['34', '35'])).
% 0.20/0.47  thf('37', plain, ((v2_struct_0 @ sk_A)),
% 0.20/0.47      inference('demod', [status(thm)], ['33', '36'])).
% 0.20/0.47  thf('38', plain, ($false), inference('demod', [status(thm)], ['0', '37'])).
% 0.20/0.47  
% 0.20/0.47  % SZS output end Refutation
% 0.20/0.47  
% 0.20/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
