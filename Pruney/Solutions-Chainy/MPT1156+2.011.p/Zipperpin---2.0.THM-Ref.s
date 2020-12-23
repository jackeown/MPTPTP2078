%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.NUhnwsSwqW

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:01:54 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   61 (  87 expanded)
%              Number of leaves         :   24 (  37 expanded)
%              Depth                    :   15
%              Number of atoms          :  383 ( 955 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal formula depth    :   15 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_orders_2_type,type,(
    k2_orders_2: $i > $i > $i )).

thf(v6_orders_2_type,type,(
    v6_orders_2: $i > $i > $o )).

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
    ! [X7: $i,X8: $i] :
      ( ( v1_xboole_0 @ X7 )
      | ~ ( m1_subset_1 @ X8 @ X7 )
      | ( ( k6_domain_1 @ X7 @ X8 )
        = ( k1_tarski @ X8 ) ) ) ),
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
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X10 ) )
      | ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ X10 ) @ X9 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( l1_orders_2 @ X10 )
      | ~ ( v3_orders_2 @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
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
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X12 ) )
      | ~ ( r2_hidden @ X11 @ ( k2_orders_2 @ X12 @ X13 ) )
      | ~ ( r2_hidden @ X11 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( l1_orders_2 @ X12 )
      | ~ ( v5_orders_2 @ X12 )
      | ~ ( v4_orders_2 @ X12 )
      | ~ ( v3_orders_2 @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
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

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X1 != X0 )
      | ( r2_hidden @ X1 @ X2 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('27',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['25','27'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('29',plain,(
    ! [X5: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X5 ) )
      | ~ ( l1_struct_0 @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('30',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('32',plain,(
    ! [X6: $i] :
      ( ( l1_struct_0 @ X6 )
      | ~ ( l1_orders_2 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_orders_2])).

thf('33',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['30','33'])).

thf('35',plain,(
    $false ),
    inference(demod,[status(thm)],['0','34'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.NUhnwsSwqW
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:36:55 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.47  % Solved by: fo/fo7.sh
% 0.21/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.47  % done 35 iterations in 0.022s
% 0.21/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.47  % SZS output start Refutation
% 0.21/0.47  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.21/0.47  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.47  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.21/0.47  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.47  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.47  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.21/0.47  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.21/0.47  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.47  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.21/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.47  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.21/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.47  thf(k2_orders_2_type, type, k2_orders_2: $i > $i > $i).
% 0.21/0.47  thf(v6_orders_2_type, type, v6_orders_2: $i > $i > $o).
% 0.21/0.47  thf(t50_orders_2, conjecture,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.21/0.47         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.21/0.47       ( ![B:$i]:
% 0.21/0.47         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.47           ( ~( r2_hidden @
% 0.21/0.47                B @ 
% 0.21/0.47                ( k2_orders_2 @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 0.21/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.47    (~( ![A:$i]:
% 0.21/0.47        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.21/0.47            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.21/0.47          ( ![B:$i]:
% 0.21/0.47            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.47              ( ~( r2_hidden @
% 0.21/0.47                   B @ 
% 0.21/0.47                   ( k2_orders_2 @
% 0.21/0.47                     A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ) )),
% 0.21/0.47    inference('cnf.neg', [status(esa)], [t50_orders_2])).
% 0.21/0.47  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('1', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(redefinition_k6_domain_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.21/0.47       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.21/0.47  thf('2', plain,
% 0.21/0.47      (![X7 : $i, X8 : $i]:
% 0.21/0.47         ((v1_xboole_0 @ X7)
% 0.21/0.47          | ~ (m1_subset_1 @ X8 @ X7)
% 0.21/0.47          | ((k6_domain_1 @ X7 @ X8) = (k1_tarski @ X8)))),
% 0.21/0.47      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.21/0.47  thf('3', plain,
% 0.21/0.47      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) = (k1_tarski @ sk_B))
% 0.21/0.47        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.47  thf('4', plain,
% 0.21/0.47      ((r2_hidden @ sk_B @ 
% 0.21/0.47        (k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('5', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(t35_orders_2, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.21/0.47       ( ![B:$i]:
% 0.21/0.47         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.47           ( ( v6_orders_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) & 
% 0.21/0.47             ( m1_subset_1 @
% 0.21/0.47               ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 0.21/0.47               ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 0.21/0.47  thf('6', plain,
% 0.21/0.47      (![X9 : $i, X10 : $i]:
% 0.21/0.47         (~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X10))
% 0.21/0.47          | (m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ X10) @ X9) @ 
% 0.21/0.47             (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.21/0.47          | ~ (l1_orders_2 @ X10)
% 0.21/0.47          | ~ (v3_orders_2 @ X10)
% 0.21/0.47          | (v2_struct_0 @ X10))),
% 0.21/0.47      inference('cnf', [status(esa)], [t35_orders_2])).
% 0.21/0.47  thf('7', plain,
% 0.21/0.47      (((v2_struct_0 @ sk_A)
% 0.21/0.47        | ~ (v3_orders_2 @ sk_A)
% 0.21/0.47        | ~ (l1_orders_2 @ sk_A)
% 0.21/0.47        | (m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.21/0.47           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.47      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.47  thf('8', plain, ((v3_orders_2 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('9', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('10', plain,
% 0.21/0.47      (((v2_struct_0 @ sk_A)
% 0.21/0.47        | (m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.21/0.47           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.47      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.21/0.47  thf('11', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('12', plain,
% 0.21/0.47      ((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.21/0.47        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.47      inference('clc', [status(thm)], ['10', '11'])).
% 0.21/0.47  thf(t49_orders_2, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.21/0.47         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.21/0.47       ( ![B:$i]:
% 0.21/0.47         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.47           ( ![C:$i]:
% 0.21/0.47             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.47               ( ~( ( r2_hidden @ B @ C ) & 
% 0.21/0.47                    ( r2_hidden @ B @ ( k2_orders_2 @ A @ C ) ) ) ) ) ) ) ) ))).
% 0.21/0.47  thf('13', plain,
% 0.21/0.47      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.21/0.47         (~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X12))
% 0.21/0.47          | ~ (r2_hidden @ X11 @ (k2_orders_2 @ X12 @ X13))
% 0.21/0.47          | ~ (r2_hidden @ X11 @ X13)
% 0.21/0.47          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.21/0.47          | ~ (l1_orders_2 @ X12)
% 0.21/0.47          | ~ (v5_orders_2 @ X12)
% 0.21/0.47          | ~ (v4_orders_2 @ X12)
% 0.21/0.47          | ~ (v3_orders_2 @ X12)
% 0.21/0.47          | (v2_struct_0 @ X12))),
% 0.21/0.47      inference('cnf', [status(esa)], [t49_orders_2])).
% 0.21/0.47  thf('14', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         ((v2_struct_0 @ sk_A)
% 0.21/0.47          | ~ (v3_orders_2 @ sk_A)
% 0.21/0.47          | ~ (v4_orders_2 @ sk_A)
% 0.21/0.47          | ~ (v5_orders_2 @ sk_A)
% 0.21/0.47          | ~ (l1_orders_2 @ sk_A)
% 0.21/0.47          | ~ (r2_hidden @ X0 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.21/0.47          | ~ (r2_hidden @ X0 @ 
% 0.21/0.47               (k2_orders_2 @ sk_A @ 
% 0.21/0.47                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 0.21/0.47          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.47  thf('15', plain, ((v3_orders_2 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('16', plain, ((v4_orders_2 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('17', plain, ((v5_orders_2 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('18', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('19', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         ((v2_struct_0 @ sk_A)
% 0.21/0.47          | ~ (r2_hidden @ X0 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.21/0.47          | ~ (r2_hidden @ X0 @ 
% 0.21/0.47               (k2_orders_2 @ sk_A @ 
% 0.21/0.47                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 0.21/0.47          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.47      inference('demod', [status(thm)], ['14', '15', '16', '17', '18'])).
% 0.21/0.47  thf('20', plain,
% 0.21/0.47      ((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.21/0.47        | ~ (r2_hidden @ sk_B @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.21/0.47        | (v2_struct_0 @ sk_A))),
% 0.21/0.47      inference('sup-', [status(thm)], ['4', '19'])).
% 0.21/0.47  thf('21', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('22', plain,
% 0.21/0.47      ((~ (r2_hidden @ sk_B @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.21/0.47        | (v2_struct_0 @ sk_A))),
% 0.21/0.47      inference('demod', [status(thm)], ['20', '21'])).
% 0.21/0.47  thf('23', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('24', plain,
% 0.21/0.47      (~ (r2_hidden @ sk_B @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.21/0.47      inference('clc', [status(thm)], ['22', '23'])).
% 0.21/0.47  thf('25', plain,
% 0.21/0.47      ((~ (r2_hidden @ sk_B @ (k1_tarski @ sk_B))
% 0.21/0.47        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['3', '24'])).
% 0.21/0.47  thf(d1_tarski, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.21/0.47       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.21/0.47  thf('26', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.47         (((X1) != (X0)) | (r2_hidden @ X1 @ X2) | ((X2) != (k1_tarski @ X0)))),
% 0.21/0.47      inference('cnf', [status(esa)], [d1_tarski])).
% 0.21/0.47  thf('27', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.21/0.47      inference('simplify', [status(thm)], ['26'])).
% 0.21/0.47  thf('28', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.21/0.47      inference('demod', [status(thm)], ['25', '27'])).
% 0.21/0.47  thf(fc2_struct_0, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.47       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.21/0.47  thf('29', plain,
% 0.21/0.47      (![X5 : $i]:
% 0.21/0.47         (~ (v1_xboole_0 @ (u1_struct_0 @ X5))
% 0.21/0.47          | ~ (l1_struct_0 @ X5)
% 0.21/0.47          | (v2_struct_0 @ X5))),
% 0.21/0.47      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.21/0.47  thf('30', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 0.21/0.47      inference('sup-', [status(thm)], ['28', '29'])).
% 0.21/0.47  thf('31', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(dt_l1_orders_2, axiom,
% 0.21/0.47    (![A:$i]: ( ( l1_orders_2 @ A ) => ( l1_struct_0 @ A ) ))).
% 0.21/0.47  thf('32', plain, (![X6 : $i]: ((l1_struct_0 @ X6) | ~ (l1_orders_2 @ X6))),
% 0.21/0.47      inference('cnf', [status(esa)], [dt_l1_orders_2])).
% 0.21/0.47  thf('33', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.47      inference('sup-', [status(thm)], ['31', '32'])).
% 0.21/0.47  thf('34', plain, ((v2_struct_0 @ sk_A)),
% 0.21/0.47      inference('demod', [status(thm)], ['30', '33'])).
% 0.21/0.47  thf('35', plain, ($false), inference('demod', [status(thm)], ['0', '34'])).
% 0.21/0.47  
% 0.21/0.47  % SZS output end Refutation
% 0.21/0.47  
% 0.21/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
